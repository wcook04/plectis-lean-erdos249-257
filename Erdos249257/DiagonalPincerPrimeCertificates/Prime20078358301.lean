import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=27 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_20078358301 : Nat.Prime 20078358301 := by
  apply lucas_primality 20078358301 (18 : ZMod 20078358301)
  ·
      have fermat_0 : (18 : ZMod 20078358301) ^ 1 = 18 := by norm_num
      have fermat_1 : (18 : ZMod 20078358301) ^ 2 = 324 := by
        calc
          (18 : ZMod 20078358301) ^ 2 = (18 : ZMod 20078358301) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 1 * (18 : ZMod 20078358301) ^ 1 := by rw [pow_add]
          _ = 324 := by rw [fermat_0]; decide
      have fermat_2 : (18 : ZMod 20078358301) ^ 4 = 104976 := by
        calc
          (18 : ZMod 20078358301) ^ 4 = (18 : ZMod 20078358301) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 2 * (18 : ZMod 20078358301) ^ 2 := by rw [pow_add]
          _ = 104976 := by rw [fermat_1]; decide
      have fermat_3 : (18 : ZMod 20078358301) ^ 9 = 17654065659 := by
        calc
          (18 : ZMod 20078358301) ^ 9 = (18 : ZMod 20078358301) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 4 * (18 : ZMod 20078358301) ^ 4) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 17654065659 := by rw [fermat_2]; decide
      have fermat_4 : (18 : ZMod 20078358301) ^ 18 = 7276824448 := by
        calc
          (18 : ZMod 20078358301) ^ 18 = (18 : ZMod 20078358301) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 9 * (18 : ZMod 20078358301) ^ 9 := by rw [pow_add]
          _ = 7276824448 := by rw [fermat_3]; decide
      have fermat_5 : (18 : ZMod 20078358301) ^ 37 = 15928362456 := by
        calc
          (18 : ZMod 20078358301) ^ 37 = (18 : ZMod 20078358301) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 18 * (18 : ZMod 20078358301) ^ 18) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 15928362456 := by rw [fermat_4]; decide
      have fermat_6 : (18 : ZMod 20078358301) ^ 74 = 10855739191 := by
        calc
          (18 : ZMod 20078358301) ^ 74 = (18 : ZMod 20078358301) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 37 * (18 : ZMod 20078358301) ^ 37 := by rw [pow_add]
          _ = 10855739191 := by rw [fermat_5]; decide
      have fermat_7 : (18 : ZMod 20078358301) ^ 149 = 6666040044 := by
        calc
          (18 : ZMod 20078358301) ^ 149 = (18 : ZMod 20078358301) ^ (74 + 74 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 74 * (18 : ZMod 20078358301) ^ 74) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 6666040044 := by rw [fermat_6]; decide
      have fermat_8 : (18 : ZMod 20078358301) ^ 299 = 16115438919 := by
        calc
          (18 : ZMod 20078358301) ^ 299 = (18 : ZMod 20078358301) ^ (149 + 149 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 149 * (18 : ZMod 20078358301) ^ 149) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 16115438919 := by rw [fermat_7]; decide
      have fermat_9 : (18 : ZMod 20078358301) ^ 598 = 17889398807 := by
        calc
          (18 : ZMod 20078358301) ^ 598 = (18 : ZMod 20078358301) ^ (299 + 299) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 299 * (18 : ZMod 20078358301) ^ 299 := by rw [pow_add]
          _ = 17889398807 := by rw [fermat_8]; decide
      have fermat_10 : (18 : ZMod 20078358301) ^ 1196 = 8798758933 := by
        calc
          (18 : ZMod 20078358301) ^ 1196 = (18 : ZMod 20078358301) ^ (598 + 598) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 598 * (18 : ZMod 20078358301) ^ 598 := by rw [pow_add]
          _ = 8798758933 := by rw [fermat_9]; decide
      have fermat_11 : (18 : ZMod 20078358301) ^ 2393 = 9141342348 := by
        calc
          (18 : ZMod 20078358301) ^ 2393 = (18 : ZMod 20078358301) ^ (1196 + 1196 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 1196 * (18 : ZMod 20078358301) ^ 1196) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 9141342348 := by rw [fermat_10]; decide
      have fermat_12 : (18 : ZMod 20078358301) ^ 4787 = 6538475385 := by
        calc
          (18 : ZMod 20078358301) ^ 4787 = (18 : ZMod 20078358301) ^ (2393 + 2393 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 2393 * (18 : ZMod 20078358301) ^ 2393) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 6538475385 := by rw [fermat_11]; decide
      have fermat_13 : (18 : ZMod 20078358301) ^ 9574 = 6157193492 := by
        calc
          (18 : ZMod 20078358301) ^ 9574 = (18 : ZMod 20078358301) ^ (4787 + 4787) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 4787 * (18 : ZMod 20078358301) ^ 4787 := by rw [pow_add]
          _ = 6157193492 := by rw [fermat_12]; decide
      have fermat_14 : (18 : ZMod 20078358301) ^ 19148 = 1751848706 := by
        calc
          (18 : ZMod 20078358301) ^ 19148 = (18 : ZMod 20078358301) ^ (9574 + 9574) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 9574 * (18 : ZMod 20078358301) ^ 9574 := by rw [pow_add]
          _ = 1751848706 := by rw [fermat_13]; decide
      have fermat_15 : (18 : ZMod 20078358301) ^ 38296 = 14864994295 := by
        calc
          (18 : ZMod 20078358301) ^ 38296 = (18 : ZMod 20078358301) ^ (19148 + 19148) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 19148 * (18 : ZMod 20078358301) ^ 19148 := by rw [pow_add]
          _ = 14864994295 := by rw [fermat_14]; decide
      have fermat_16 : (18 : ZMod 20078358301) ^ 76592 = 15996836928 := by
        calc
          (18 : ZMod 20078358301) ^ 76592 = (18 : ZMod 20078358301) ^ (38296 + 38296) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 38296 * (18 : ZMod 20078358301) ^ 38296 := by rw [pow_add]
          _ = 15996836928 := by rw [fermat_15]; decide
      have fermat_17 : (18 : ZMod 20078358301) ^ 153185 = 16789743878 := by
        calc
          (18 : ZMod 20078358301) ^ 153185 = (18 : ZMod 20078358301) ^ (76592 + 76592 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 76592 * (18 : ZMod 20078358301) ^ 76592) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 16789743878 := by rw [fermat_16]; decide
      have fermat_18 : (18 : ZMod 20078358301) ^ 306371 = 14398202328 := by
        calc
          (18 : ZMod 20078358301) ^ 306371 = (18 : ZMod 20078358301) ^ (153185 + 153185 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 153185 * (18 : ZMod 20078358301) ^ 153185) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 14398202328 := by rw [fermat_17]; decide
      have fermat_19 : (18 : ZMod 20078358301) ^ 612742 = 17218300384 := by
        calc
          (18 : ZMod 20078358301) ^ 612742 = (18 : ZMod 20078358301) ^ (306371 + 306371) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 306371 * (18 : ZMod 20078358301) ^ 306371 := by rw [pow_add]
          _ = 17218300384 := by rw [fermat_18]; decide
      have fermat_20 : (18 : ZMod 20078358301) ^ 1225485 = 11670621926 := by
        calc
          (18 : ZMod 20078358301) ^ 1225485 = (18 : ZMod 20078358301) ^ (612742 + 612742 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 612742 * (18 : ZMod 20078358301) ^ 612742) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 11670621926 := by rw [fermat_19]; decide
      have fermat_21 : (18 : ZMod 20078358301) ^ 2450971 = 1042195701 := by
        calc
          (18 : ZMod 20078358301) ^ 2450971 = (18 : ZMod 20078358301) ^ (1225485 + 1225485 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 1225485 * (18 : ZMod 20078358301) ^ 1225485) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 1042195701 := by rw [fermat_20]; decide
      have fermat_22 : (18 : ZMod 20078358301) ^ 4901942 = 17834164654 := by
        calc
          (18 : ZMod 20078358301) ^ 4901942 = (18 : ZMod 20078358301) ^ (2450971 + 2450971) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 2450971 * (18 : ZMod 20078358301) ^ 2450971 := by rw [pow_add]
          _ = 17834164654 := by rw [fermat_21]; decide
      have fermat_23 : (18 : ZMod 20078358301) ^ 9803885 = 13673680430 := by
        calc
          (18 : ZMod 20078358301) ^ 9803885 = (18 : ZMod 20078358301) ^ (4901942 + 4901942 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 4901942 * (18 : ZMod 20078358301) ^ 4901942) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 13673680430 := by rw [fermat_22]; decide
      have fermat_24 : (18 : ZMod 20078358301) ^ 19607771 = 4797786120 := by
        calc
          (18 : ZMod 20078358301) ^ 19607771 = (18 : ZMod 20078358301) ^ (9803885 + 9803885 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 9803885 * (18 : ZMod 20078358301) ^ 9803885) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 4797786120 := by rw [fermat_23]; decide
      have fermat_25 : (18 : ZMod 20078358301) ^ 39215543 = 19366404211 := by
        calc
          (18 : ZMod 20078358301) ^ 39215543 = (18 : ZMod 20078358301) ^ (19607771 + 19607771 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 19607771 * (18 : ZMod 20078358301) ^ 19607771) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 19366404211 := by rw [fermat_24]; decide
      have fermat_26 : (18 : ZMod 20078358301) ^ 78431087 = 4194492778 := by
        calc
          (18 : ZMod 20078358301) ^ 78431087 = (18 : ZMod 20078358301) ^ (39215543 + 39215543 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 39215543 * (18 : ZMod 20078358301) ^ 39215543) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 4194492778 := by rw [fermat_25]; decide
      have fermat_27 : (18 : ZMod 20078358301) ^ 156862174 = 1170023195 := by
        calc
          (18 : ZMod 20078358301) ^ 156862174 = (18 : ZMod 20078358301) ^ (78431087 + 78431087) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 78431087 * (18 : ZMod 20078358301) ^ 78431087 := by rw [pow_add]
          _ = 1170023195 := by rw [fermat_26]; decide
      have fermat_28 : (18 : ZMod 20078358301) ^ 313724348 = 1801147037 := by
        calc
          (18 : ZMod 20078358301) ^ 313724348 = (18 : ZMod 20078358301) ^ (156862174 + 156862174) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 156862174 * (18 : ZMod 20078358301) ^ 156862174 := by rw [pow_add]
          _ = 1801147037 := by rw [fermat_27]; decide
      have fermat_29 : (18 : ZMod 20078358301) ^ 627448696 = 3868897568 := by
        calc
          (18 : ZMod 20078358301) ^ 627448696 = (18 : ZMod 20078358301) ^ (313724348 + 313724348) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 313724348 * (18 : ZMod 20078358301) ^ 313724348 := by rw [pow_add]
          _ = 3868897568 := by rw [fermat_28]; decide
      have fermat_30 : (18 : ZMod 20078358301) ^ 1254897393 = 1379496614 := by
        calc
          (18 : ZMod 20078358301) ^ 1254897393 = (18 : ZMod 20078358301) ^ (627448696 + 627448696 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 627448696 * (18 : ZMod 20078358301) ^ 627448696) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 1379496614 := by rw [fermat_29]; decide
      have fermat_31 : (18 : ZMod 20078358301) ^ 2509794787 = 5207044275 := by
        calc
          (18 : ZMod 20078358301) ^ 2509794787 = (18 : ZMod 20078358301) ^ (1254897393 + 1254897393 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 1254897393 * (18 : ZMod 20078358301) ^ 1254897393) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 5207044275 := by rw [fermat_30]; decide
      have fermat_32 : (18 : ZMod 20078358301) ^ 5019589575 = 11163907348 := by
        calc
          (18 : ZMod 20078358301) ^ 5019589575 = (18 : ZMod 20078358301) ^ (2509794787 + 2509794787 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 2509794787 * (18 : ZMod 20078358301) ^ 2509794787) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 11163907348 := by rw [fermat_31]; decide
      have fermat_33 : (18 : ZMod 20078358301) ^ 10039179150 = 20078358300 := by
        calc
          (18 : ZMod 20078358301) ^ 10039179150 = (18 : ZMod 20078358301) ^ (5019589575 + 5019589575) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 5019589575 * (18 : ZMod 20078358301) ^ 5019589575 := by rw [pow_add]
          _ = 20078358300 := by rw [fermat_32]; decide
      have fermat_34 : (18 : ZMod 20078358301) ^ 20078358300 = 1 := by
        calc
          (18 : ZMod 20078358301) ^ 20078358300 = (18 : ZMod 20078358301) ^ (10039179150 + 10039179150) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 10039179150 * (18 : ZMod 20078358301) ^ 10039179150 := by rw [pow_add]
          _ = 1 := by rw [fermat_33]; decide
      simpa using fermat_34
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod = 20078358301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (18 : ZMod 20078358301) ^ 1 = 18 := by norm_num
      have factor_0_1 : (18 : ZMod 20078358301) ^ 2 = 324 := by
        calc
          (18 : ZMod 20078358301) ^ 2 = (18 : ZMod 20078358301) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 1 * (18 : ZMod 20078358301) ^ 1 := by rw [pow_add]
          _ = 324 := by rw [factor_0_0]; decide
      have factor_0_2 : (18 : ZMod 20078358301) ^ 4 = 104976 := by
        calc
          (18 : ZMod 20078358301) ^ 4 = (18 : ZMod 20078358301) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 2 * (18 : ZMod 20078358301) ^ 2 := by rw [pow_add]
          _ = 104976 := by rw [factor_0_1]; decide
      have factor_0_3 : (18 : ZMod 20078358301) ^ 9 = 17654065659 := by
        calc
          (18 : ZMod 20078358301) ^ 9 = (18 : ZMod 20078358301) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 4 * (18 : ZMod 20078358301) ^ 4) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 17654065659 := by rw [factor_0_2]; decide
      have factor_0_4 : (18 : ZMod 20078358301) ^ 18 = 7276824448 := by
        calc
          (18 : ZMod 20078358301) ^ 18 = (18 : ZMod 20078358301) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 9 * (18 : ZMod 20078358301) ^ 9 := by rw [pow_add]
          _ = 7276824448 := by rw [factor_0_3]; decide
      have factor_0_5 : (18 : ZMod 20078358301) ^ 37 = 15928362456 := by
        calc
          (18 : ZMod 20078358301) ^ 37 = (18 : ZMod 20078358301) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 18 * (18 : ZMod 20078358301) ^ 18) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 15928362456 := by rw [factor_0_4]; decide
      have factor_0_6 : (18 : ZMod 20078358301) ^ 74 = 10855739191 := by
        calc
          (18 : ZMod 20078358301) ^ 74 = (18 : ZMod 20078358301) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 37 * (18 : ZMod 20078358301) ^ 37 := by rw [pow_add]
          _ = 10855739191 := by rw [factor_0_5]; decide
      have factor_0_7 : (18 : ZMod 20078358301) ^ 149 = 6666040044 := by
        calc
          (18 : ZMod 20078358301) ^ 149 = (18 : ZMod 20078358301) ^ (74 + 74 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 74 * (18 : ZMod 20078358301) ^ 74) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 6666040044 := by rw [factor_0_6]; decide
      have factor_0_8 : (18 : ZMod 20078358301) ^ 299 = 16115438919 := by
        calc
          (18 : ZMod 20078358301) ^ 299 = (18 : ZMod 20078358301) ^ (149 + 149 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 149 * (18 : ZMod 20078358301) ^ 149) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 16115438919 := by rw [factor_0_7]; decide
      have factor_0_9 : (18 : ZMod 20078358301) ^ 598 = 17889398807 := by
        calc
          (18 : ZMod 20078358301) ^ 598 = (18 : ZMod 20078358301) ^ (299 + 299) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 299 * (18 : ZMod 20078358301) ^ 299 := by rw [pow_add]
          _ = 17889398807 := by rw [factor_0_8]; decide
      have factor_0_10 : (18 : ZMod 20078358301) ^ 1196 = 8798758933 := by
        calc
          (18 : ZMod 20078358301) ^ 1196 = (18 : ZMod 20078358301) ^ (598 + 598) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 598 * (18 : ZMod 20078358301) ^ 598 := by rw [pow_add]
          _ = 8798758933 := by rw [factor_0_9]; decide
      have factor_0_11 : (18 : ZMod 20078358301) ^ 2393 = 9141342348 := by
        calc
          (18 : ZMod 20078358301) ^ 2393 = (18 : ZMod 20078358301) ^ (1196 + 1196 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 1196 * (18 : ZMod 20078358301) ^ 1196) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 9141342348 := by rw [factor_0_10]; decide
      have factor_0_12 : (18 : ZMod 20078358301) ^ 4787 = 6538475385 := by
        calc
          (18 : ZMod 20078358301) ^ 4787 = (18 : ZMod 20078358301) ^ (2393 + 2393 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 2393 * (18 : ZMod 20078358301) ^ 2393) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 6538475385 := by rw [factor_0_11]; decide
      have factor_0_13 : (18 : ZMod 20078358301) ^ 9574 = 6157193492 := by
        calc
          (18 : ZMod 20078358301) ^ 9574 = (18 : ZMod 20078358301) ^ (4787 + 4787) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 4787 * (18 : ZMod 20078358301) ^ 4787 := by rw [pow_add]
          _ = 6157193492 := by rw [factor_0_12]; decide
      have factor_0_14 : (18 : ZMod 20078358301) ^ 19148 = 1751848706 := by
        calc
          (18 : ZMod 20078358301) ^ 19148 = (18 : ZMod 20078358301) ^ (9574 + 9574) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 9574 * (18 : ZMod 20078358301) ^ 9574 := by rw [pow_add]
          _ = 1751848706 := by rw [factor_0_13]; decide
      have factor_0_15 : (18 : ZMod 20078358301) ^ 38296 = 14864994295 := by
        calc
          (18 : ZMod 20078358301) ^ 38296 = (18 : ZMod 20078358301) ^ (19148 + 19148) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 19148 * (18 : ZMod 20078358301) ^ 19148 := by rw [pow_add]
          _ = 14864994295 := by rw [factor_0_14]; decide
      have factor_0_16 : (18 : ZMod 20078358301) ^ 76592 = 15996836928 := by
        calc
          (18 : ZMod 20078358301) ^ 76592 = (18 : ZMod 20078358301) ^ (38296 + 38296) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 38296 * (18 : ZMod 20078358301) ^ 38296 := by rw [pow_add]
          _ = 15996836928 := by rw [factor_0_15]; decide
      have factor_0_17 : (18 : ZMod 20078358301) ^ 153185 = 16789743878 := by
        calc
          (18 : ZMod 20078358301) ^ 153185 = (18 : ZMod 20078358301) ^ (76592 + 76592 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 76592 * (18 : ZMod 20078358301) ^ 76592) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 16789743878 := by rw [factor_0_16]; decide
      have factor_0_18 : (18 : ZMod 20078358301) ^ 306371 = 14398202328 := by
        calc
          (18 : ZMod 20078358301) ^ 306371 = (18 : ZMod 20078358301) ^ (153185 + 153185 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 153185 * (18 : ZMod 20078358301) ^ 153185) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 14398202328 := by rw [factor_0_17]; decide
      have factor_0_19 : (18 : ZMod 20078358301) ^ 612742 = 17218300384 := by
        calc
          (18 : ZMod 20078358301) ^ 612742 = (18 : ZMod 20078358301) ^ (306371 + 306371) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 306371 * (18 : ZMod 20078358301) ^ 306371 := by rw [pow_add]
          _ = 17218300384 := by rw [factor_0_18]; decide
      have factor_0_20 : (18 : ZMod 20078358301) ^ 1225485 = 11670621926 := by
        calc
          (18 : ZMod 20078358301) ^ 1225485 = (18 : ZMod 20078358301) ^ (612742 + 612742 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 612742 * (18 : ZMod 20078358301) ^ 612742) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 11670621926 := by rw [factor_0_19]; decide
      have factor_0_21 : (18 : ZMod 20078358301) ^ 2450971 = 1042195701 := by
        calc
          (18 : ZMod 20078358301) ^ 2450971 = (18 : ZMod 20078358301) ^ (1225485 + 1225485 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 1225485 * (18 : ZMod 20078358301) ^ 1225485) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 1042195701 := by rw [factor_0_20]; decide
      have factor_0_22 : (18 : ZMod 20078358301) ^ 4901942 = 17834164654 := by
        calc
          (18 : ZMod 20078358301) ^ 4901942 = (18 : ZMod 20078358301) ^ (2450971 + 2450971) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 2450971 * (18 : ZMod 20078358301) ^ 2450971 := by rw [pow_add]
          _ = 17834164654 := by rw [factor_0_21]; decide
      have factor_0_23 : (18 : ZMod 20078358301) ^ 9803885 = 13673680430 := by
        calc
          (18 : ZMod 20078358301) ^ 9803885 = (18 : ZMod 20078358301) ^ (4901942 + 4901942 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 4901942 * (18 : ZMod 20078358301) ^ 4901942) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 13673680430 := by rw [factor_0_22]; decide
      have factor_0_24 : (18 : ZMod 20078358301) ^ 19607771 = 4797786120 := by
        calc
          (18 : ZMod 20078358301) ^ 19607771 = (18 : ZMod 20078358301) ^ (9803885 + 9803885 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 9803885 * (18 : ZMod 20078358301) ^ 9803885) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 4797786120 := by rw [factor_0_23]; decide
      have factor_0_25 : (18 : ZMod 20078358301) ^ 39215543 = 19366404211 := by
        calc
          (18 : ZMod 20078358301) ^ 39215543 = (18 : ZMod 20078358301) ^ (19607771 + 19607771 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 19607771 * (18 : ZMod 20078358301) ^ 19607771) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 19366404211 := by rw [factor_0_24]; decide
      have factor_0_26 : (18 : ZMod 20078358301) ^ 78431087 = 4194492778 := by
        calc
          (18 : ZMod 20078358301) ^ 78431087 = (18 : ZMod 20078358301) ^ (39215543 + 39215543 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 39215543 * (18 : ZMod 20078358301) ^ 39215543) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 4194492778 := by rw [factor_0_25]; decide
      have factor_0_27 : (18 : ZMod 20078358301) ^ 156862174 = 1170023195 := by
        calc
          (18 : ZMod 20078358301) ^ 156862174 = (18 : ZMod 20078358301) ^ (78431087 + 78431087) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 78431087 * (18 : ZMod 20078358301) ^ 78431087 := by rw [pow_add]
          _ = 1170023195 := by rw [factor_0_26]; decide
      have factor_0_28 : (18 : ZMod 20078358301) ^ 313724348 = 1801147037 := by
        calc
          (18 : ZMod 20078358301) ^ 313724348 = (18 : ZMod 20078358301) ^ (156862174 + 156862174) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 156862174 * (18 : ZMod 20078358301) ^ 156862174 := by rw [pow_add]
          _ = 1801147037 := by rw [factor_0_27]; decide
      have factor_0_29 : (18 : ZMod 20078358301) ^ 627448696 = 3868897568 := by
        calc
          (18 : ZMod 20078358301) ^ 627448696 = (18 : ZMod 20078358301) ^ (313724348 + 313724348) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 313724348 * (18 : ZMod 20078358301) ^ 313724348 := by rw [pow_add]
          _ = 3868897568 := by rw [factor_0_28]; decide
      have factor_0_30 : (18 : ZMod 20078358301) ^ 1254897393 = 1379496614 := by
        calc
          (18 : ZMod 20078358301) ^ 1254897393 = (18 : ZMod 20078358301) ^ (627448696 + 627448696 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 627448696 * (18 : ZMod 20078358301) ^ 627448696) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 1379496614 := by rw [factor_0_29]; decide
      have factor_0_31 : (18 : ZMod 20078358301) ^ 2509794787 = 5207044275 := by
        calc
          (18 : ZMod 20078358301) ^ 2509794787 = (18 : ZMod 20078358301) ^ (1254897393 + 1254897393 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 1254897393 * (18 : ZMod 20078358301) ^ 1254897393) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 5207044275 := by rw [factor_0_30]; decide
      have factor_0_32 : (18 : ZMod 20078358301) ^ 5019589575 = 11163907348 := by
        calc
          (18 : ZMod 20078358301) ^ 5019589575 = (18 : ZMod 20078358301) ^ (2509794787 + 2509794787 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 2509794787 * (18 : ZMod 20078358301) ^ 2509794787) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 11163907348 := by rw [factor_0_31]; decide
      have factor_0_33 : (18 : ZMod 20078358301) ^ 10039179150 = 20078358300 := by
        calc
          (18 : ZMod 20078358301) ^ 10039179150 = (18 : ZMod 20078358301) ^ (5019589575 + 5019589575) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 5019589575 * (18 : ZMod 20078358301) ^ 5019589575 := by rw [pow_add]
          _ = 20078358300 := by rw [factor_0_32]; decide
      change (18 : ZMod 20078358301) ^ 10039179150 ≠ 1
      rw [factor_0_33]
      decide
    ·
      have factor_1_0 : (18 : ZMod 20078358301) ^ 1 = 18 := by norm_num
      have factor_1_1 : (18 : ZMod 20078358301) ^ 3 = 5832 := by
        calc
          (18 : ZMod 20078358301) ^ 3 = (18 : ZMod 20078358301) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 1 * (18 : ZMod 20078358301) ^ 1) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 5832 := by rw [factor_1_0]; decide
      have factor_1_2 : (18 : ZMod 20078358301) ^ 6 = 34012224 := by
        calc
          (18 : ZMod 20078358301) ^ 6 = (18 : ZMod 20078358301) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 3 * (18 : ZMod 20078358301) ^ 3 := by rw [pow_add]
          _ = 34012224 := by rw [factor_1_1]; decide
      have factor_1_3 : (18 : ZMod 20078358301) ^ 12 = 16767914061 := by
        calc
          (18 : ZMod 20078358301) ^ 12 = (18 : ZMod 20078358301) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 6 * (18 : ZMod 20078358301) ^ 6 := by rw [pow_add]
          _ = 16767914061 := by rw [factor_1_2]; decide
      have factor_1_4 : (18 : ZMod 20078358301) ^ 24 = 19712125699 := by
        calc
          (18 : ZMod 20078358301) ^ 24 = (18 : ZMod 20078358301) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 12 * (18 : ZMod 20078358301) ^ 12 := by rw [pow_add]
          _ = 19712125699 := by rw [factor_1_3]; decide
      have factor_1_5 : (18 : ZMod 20078358301) ^ 49 = 13071620886 := by
        calc
          (18 : ZMod 20078358301) ^ 49 = (18 : ZMod 20078358301) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 24 * (18 : ZMod 20078358301) ^ 24) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 13071620886 := by rw [factor_1_4]; decide
      have factor_1_6 : (18 : ZMod 20078358301) ^ 99 = 13631595485 := by
        calc
          (18 : ZMod 20078358301) ^ 99 = (18 : ZMod 20078358301) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 49 * (18 : ZMod 20078358301) ^ 49) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 13631595485 := by rw [factor_1_5]; decide
      have factor_1_7 : (18 : ZMod 20078358301) ^ 199 = 8596458302 := by
        calc
          (18 : ZMod 20078358301) ^ 199 = (18 : ZMod 20078358301) ^ (99 + 99 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 99 * (18 : ZMod 20078358301) ^ 99) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 8596458302 := by rw [factor_1_6]; decide
      have factor_1_8 : (18 : ZMod 20078358301) ^ 398 = 8713413260 := by
        calc
          (18 : ZMod 20078358301) ^ 398 = (18 : ZMod 20078358301) ^ (199 + 199) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 199 * (18 : ZMod 20078358301) ^ 199 := by rw [pow_add]
          _ = 8713413260 := by rw [factor_1_7]; decide
      have factor_1_9 : (18 : ZMod 20078358301) ^ 797 = 4713770320 := by
        calc
          (18 : ZMod 20078358301) ^ 797 = (18 : ZMod 20078358301) ^ (398 + 398 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 398 * (18 : ZMod 20078358301) ^ 398) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 4713770320 := by rw [factor_1_8]; decide
      have factor_1_10 : (18 : ZMod 20078358301) ^ 1595 = 8234149729 := by
        calc
          (18 : ZMod 20078358301) ^ 1595 = (18 : ZMod 20078358301) ^ (797 + 797 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 797 * (18 : ZMod 20078358301) ^ 797) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 8234149729 := by rw [factor_1_9]; decide
      have factor_1_11 : (18 : ZMod 20078358301) ^ 3191 = 2876510517 := by
        calc
          (18 : ZMod 20078358301) ^ 3191 = (18 : ZMod 20078358301) ^ (1595 + 1595 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 1595 * (18 : ZMod 20078358301) ^ 1595) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 2876510517 := by rw [factor_1_10]; decide
      have factor_1_12 : (18 : ZMod 20078358301) ^ 6382 = 15509708229 := by
        calc
          (18 : ZMod 20078358301) ^ 6382 = (18 : ZMod 20078358301) ^ (3191 + 3191) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 3191 * (18 : ZMod 20078358301) ^ 3191 := by rw [pow_add]
          _ = 15509708229 := by rw [factor_1_11]; decide
      have factor_1_13 : (18 : ZMod 20078358301) ^ 12765 = 625610687 := by
        calc
          (18 : ZMod 20078358301) ^ 12765 = (18 : ZMod 20078358301) ^ (6382 + 6382 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 6382 * (18 : ZMod 20078358301) ^ 6382) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 625610687 := by rw [factor_1_12]; decide
      have factor_1_14 : (18 : ZMod 20078358301) ^ 25530 = 8312287705 := by
        calc
          (18 : ZMod 20078358301) ^ 25530 = (18 : ZMod 20078358301) ^ (12765 + 12765) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 12765 * (18 : ZMod 20078358301) ^ 12765 := by rw [pow_add]
          _ = 8312287705 := by rw [factor_1_13]; decide
      have factor_1_15 : (18 : ZMod 20078358301) ^ 51061 = 15207653763 := by
        calc
          (18 : ZMod 20078358301) ^ 51061 = (18 : ZMod 20078358301) ^ (25530 + 25530 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 25530 * (18 : ZMod 20078358301) ^ 25530) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 15207653763 := by rw [factor_1_14]; decide
      have factor_1_16 : (18 : ZMod 20078358301) ^ 102123 = 11759537818 := by
        calc
          (18 : ZMod 20078358301) ^ 102123 = (18 : ZMod 20078358301) ^ (51061 + 51061 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 51061 * (18 : ZMod 20078358301) ^ 51061) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 11759537818 := by rw [factor_1_15]; decide
      have factor_1_17 : (18 : ZMod 20078358301) ^ 204247 = 17075097020 := by
        calc
          (18 : ZMod 20078358301) ^ 204247 = (18 : ZMod 20078358301) ^ (102123 + 102123 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 102123 * (18 : ZMod 20078358301) ^ 102123) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 17075097020 := by rw [factor_1_16]; decide
      have factor_1_18 : (18 : ZMod 20078358301) ^ 408495 = 18656580537 := by
        calc
          (18 : ZMod 20078358301) ^ 408495 = (18 : ZMod 20078358301) ^ (204247 + 204247 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 204247 * (18 : ZMod 20078358301) ^ 204247) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 18656580537 := by rw [factor_1_17]; decide
      have factor_1_19 : (18 : ZMod 20078358301) ^ 816990 = 1266299944 := by
        calc
          (18 : ZMod 20078358301) ^ 816990 = (18 : ZMod 20078358301) ^ (408495 + 408495) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 408495 * (18 : ZMod 20078358301) ^ 408495 := by rw [pow_add]
          _ = 1266299944 := by rw [factor_1_18]; decide
      have factor_1_20 : (18 : ZMod 20078358301) ^ 1633980 = 8506277955 := by
        calc
          (18 : ZMod 20078358301) ^ 1633980 = (18 : ZMod 20078358301) ^ (816990 + 816990) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 816990 * (18 : ZMod 20078358301) ^ 816990 := by rw [pow_add]
          _ = 8506277955 := by rw [factor_1_19]; decide
      have factor_1_21 : (18 : ZMod 20078358301) ^ 3267961 = 17524514848 := by
        calc
          (18 : ZMod 20078358301) ^ 3267961 = (18 : ZMod 20078358301) ^ (1633980 + 1633980 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 1633980 * (18 : ZMod 20078358301) ^ 1633980) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 17524514848 := by rw [factor_1_20]; decide
      have factor_1_22 : (18 : ZMod 20078358301) ^ 6535923 = 15844222955 := by
        calc
          (18 : ZMod 20078358301) ^ 6535923 = (18 : ZMod 20078358301) ^ (3267961 + 3267961 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 3267961 * (18 : ZMod 20078358301) ^ 3267961) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 15844222955 := by rw [factor_1_21]; decide
      have factor_1_23 : (18 : ZMod 20078358301) ^ 13071847 = 18913034763 := by
        calc
          (18 : ZMod 20078358301) ^ 13071847 = (18 : ZMod 20078358301) ^ (6535923 + 6535923 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 6535923 * (18 : ZMod 20078358301) ^ 6535923) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 18913034763 := by rw [factor_1_22]; decide
      have factor_1_24 : (18 : ZMod 20078358301) ^ 26143695 = 3760898953 := by
        calc
          (18 : ZMod 20078358301) ^ 26143695 = (18 : ZMod 20078358301) ^ (13071847 + 13071847 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 13071847 * (18 : ZMod 20078358301) ^ 13071847) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 3760898953 := by rw [factor_1_23]; decide
      have factor_1_25 : (18 : ZMod 20078358301) ^ 52287391 = 11731869343 := by
        calc
          (18 : ZMod 20078358301) ^ 52287391 = (18 : ZMod 20078358301) ^ (26143695 + 26143695 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 26143695 * (18 : ZMod 20078358301) ^ 26143695) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 11731869343 := by rw [factor_1_24]; decide
      have factor_1_26 : (18 : ZMod 20078358301) ^ 104574782 = 1593910367 := by
        calc
          (18 : ZMod 20078358301) ^ 104574782 = (18 : ZMod 20078358301) ^ (52287391 + 52287391) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 52287391 * (18 : ZMod 20078358301) ^ 52287391 := by rw [pow_add]
          _ = 1593910367 := by rw [factor_1_25]; decide
      have factor_1_27 : (18 : ZMod 20078358301) ^ 209149565 = 130360803 := by
        calc
          (18 : ZMod 20078358301) ^ 209149565 = (18 : ZMod 20078358301) ^ (104574782 + 104574782 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 104574782 * (18 : ZMod 20078358301) ^ 104574782) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 130360803 := by rw [factor_1_26]; decide
      have factor_1_28 : (18 : ZMod 20078358301) ^ 418299131 = 3826346906 := by
        calc
          (18 : ZMod 20078358301) ^ 418299131 = (18 : ZMod 20078358301) ^ (209149565 + 209149565 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 209149565 * (18 : ZMod 20078358301) ^ 209149565) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 3826346906 := by rw [factor_1_27]; decide
      have factor_1_29 : (18 : ZMod 20078358301) ^ 836598262 = 4620512507 := by
        calc
          (18 : ZMod 20078358301) ^ 836598262 = (18 : ZMod 20078358301) ^ (418299131 + 418299131) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 418299131 * (18 : ZMod 20078358301) ^ 418299131 := by rw [pow_add]
          _ = 4620512507 := by rw [factor_1_28]; decide
      have factor_1_30 : (18 : ZMod 20078358301) ^ 1673196525 = 9985075940 := by
        calc
          (18 : ZMod 20078358301) ^ 1673196525 = (18 : ZMod 20078358301) ^ (836598262 + 836598262 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 836598262 * (18 : ZMod 20078358301) ^ 836598262) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 9985075940 := by rw [factor_1_29]; decide
      have factor_1_31 : (18 : ZMod 20078358301) ^ 3346393050 = 8823548149 := by
        calc
          (18 : ZMod 20078358301) ^ 3346393050 = (18 : ZMod 20078358301) ^ (1673196525 + 1673196525) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 1673196525 * (18 : ZMod 20078358301) ^ 1673196525 := by rw [pow_add]
          _ = 8823548149 := by rw [factor_1_30]; decide
      have factor_1_32 : (18 : ZMod 20078358301) ^ 6692786100 = 8823548148 := by
        calc
          (18 : ZMod 20078358301) ^ 6692786100 = (18 : ZMod 20078358301) ^ (3346393050 + 3346393050) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 3346393050 * (18 : ZMod 20078358301) ^ 3346393050 := by rw [pow_add]
          _ = 8823548148 := by rw [factor_1_31]; decide
      change (18 : ZMod 20078358301) ^ 6692786100 ≠ 1
      rw [factor_1_32]
      decide
    ·
      have factor_2_0 : (18 : ZMod 20078358301) ^ 1 = 18 := by norm_num
      have factor_2_1 : (18 : ZMod 20078358301) ^ 3 = 5832 := by
        calc
          (18 : ZMod 20078358301) ^ 3 = (18 : ZMod 20078358301) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 1 * (18 : ZMod 20078358301) ^ 1) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 5832 := by rw [factor_2_0]; decide
      have factor_2_2 : (18 : ZMod 20078358301) ^ 7 = 612220032 := by
        calc
          (18 : ZMod 20078358301) ^ 7 = (18 : ZMod 20078358301) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 3 * (18 : ZMod 20078358301) ^ 3) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 612220032 := by rw [factor_2_1]; decide
      have factor_2_3 : (18 : ZMod 20078358301) ^ 14 = 11647414494 := by
        calc
          (18 : ZMod 20078358301) ^ 14 = (18 : ZMod 20078358301) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 7 * (18 : ZMod 20078358301) ^ 7 := by rw [pow_add]
          _ = 11647414494 := by rw [factor_2_2]; decide
      have factor_2_4 : (18 : ZMod 20078358301) ^ 29 = 19370264631 := by
        calc
          (18 : ZMod 20078358301) ^ 29 = (18 : ZMod 20078358301) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 14 * (18 : ZMod 20078358301) ^ 14) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 19370264631 := by rw [factor_2_3]; decide
      have factor_2_5 : (18 : ZMod 20078358301) ^ 59 = 4332924106 := by
        calc
          (18 : ZMod 20078358301) ^ 59 = (18 : ZMod 20078358301) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 29 * (18 : ZMod 20078358301) ^ 29) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 4332924106 := by rw [factor_2_4]; decide
      have factor_2_6 : (18 : ZMod 20078358301) ^ 119 = 4895704075 := by
        calc
          (18 : ZMod 20078358301) ^ 119 = (18 : ZMod 20078358301) ^ (59 + 59 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 59 * (18 : ZMod 20078358301) ^ 59) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 4895704075 := by rw [factor_2_5]; decide
      have factor_2_7 : (18 : ZMod 20078358301) ^ 239 = 8761668215 := by
        calc
          (18 : ZMod 20078358301) ^ 239 = (18 : ZMod 20078358301) ^ (119 + 119 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 119 * (18 : ZMod 20078358301) ^ 119) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 8761668215 := by rw [factor_2_6]; decide
      have factor_2_8 : (18 : ZMod 20078358301) ^ 478 = 8089453937 := by
        calc
          (18 : ZMod 20078358301) ^ 478 = (18 : ZMod 20078358301) ^ (239 + 239) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 239 * (18 : ZMod 20078358301) ^ 239 := by rw [pow_add]
          _ = 8089453937 := by rw [factor_2_7]; decide
      have factor_2_9 : (18 : ZMod 20078358301) ^ 957 = 12175210158 := by
        calc
          (18 : ZMod 20078358301) ^ 957 = (18 : ZMod 20078358301) ^ (478 + 478 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 478 * (18 : ZMod 20078358301) ^ 478) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 12175210158 := by rw [factor_2_8]; decide
      have factor_2_10 : (18 : ZMod 20078358301) ^ 1914 = 12606563070 := by
        calc
          (18 : ZMod 20078358301) ^ 1914 = (18 : ZMod 20078358301) ^ (957 + 957) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 957 * (18 : ZMod 20078358301) ^ 957 := by rw [pow_add]
          _ = 12606563070 := by rw [factor_2_9]; decide
      have factor_2_11 : (18 : ZMod 20078358301) ^ 3829 = 12337037021 := by
        calc
          (18 : ZMod 20078358301) ^ 3829 = (18 : ZMod 20078358301) ^ (1914 + 1914 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 1914 * (18 : ZMod 20078358301) ^ 1914) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 12337037021 := by rw [factor_2_10]; decide
      have factor_2_12 : (18 : ZMod 20078358301) ^ 7659 = 1320783804 := by
        calc
          (18 : ZMod 20078358301) ^ 7659 = (18 : ZMod 20078358301) ^ (3829 + 3829 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 3829 * (18 : ZMod 20078358301) ^ 3829) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 1320783804 := by rw [factor_2_11]; decide
      have factor_2_13 : (18 : ZMod 20078358301) ^ 15318 = 5433963724 := by
        calc
          (18 : ZMod 20078358301) ^ 15318 = (18 : ZMod 20078358301) ^ (7659 + 7659) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 7659 * (18 : ZMod 20078358301) ^ 7659 := by rw [pow_add]
          _ = 5433963724 := by rw [factor_2_12]; decide
      have factor_2_14 : (18 : ZMod 20078358301) ^ 30637 = 10848161993 := by
        calc
          (18 : ZMod 20078358301) ^ 30637 = (18 : ZMod 20078358301) ^ (15318 + 15318 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 15318 * (18 : ZMod 20078358301) ^ 15318) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 10848161993 := by rw [factor_2_13]; decide
      have factor_2_15 : (18 : ZMod 20078358301) ^ 61274 = 8988102174 := by
        calc
          (18 : ZMod 20078358301) ^ 61274 = (18 : ZMod 20078358301) ^ (30637 + 30637) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 30637 * (18 : ZMod 20078358301) ^ 30637 := by rw [pow_add]
          _ = 8988102174 := by rw [factor_2_14]; decide
      have factor_2_16 : (18 : ZMod 20078358301) ^ 122548 = 10720371611 := by
        calc
          (18 : ZMod 20078358301) ^ 122548 = (18 : ZMod 20078358301) ^ (61274 + 61274) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 61274 * (18 : ZMod 20078358301) ^ 61274 := by rw [pow_add]
          _ = 10720371611 := by rw [factor_2_15]; decide
      have factor_2_17 : (18 : ZMod 20078358301) ^ 245097 = 7740499001 := by
        calc
          (18 : ZMod 20078358301) ^ 245097 = (18 : ZMod 20078358301) ^ (122548 + 122548 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 122548 * (18 : ZMod 20078358301) ^ 122548) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 7740499001 := by rw [factor_2_16]; decide
      have factor_2_18 : (18 : ZMod 20078358301) ^ 490194 = 6279911014 := by
        calc
          (18 : ZMod 20078358301) ^ 490194 = (18 : ZMod 20078358301) ^ (245097 + 245097) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 245097 * (18 : ZMod 20078358301) ^ 245097 := by rw [pow_add]
          _ = 6279911014 := by rw [factor_2_17]; decide
      have factor_2_19 : (18 : ZMod 20078358301) ^ 980388 = 3821520225 := by
        calc
          (18 : ZMod 20078358301) ^ 980388 = (18 : ZMod 20078358301) ^ (490194 + 490194) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 490194 * (18 : ZMod 20078358301) ^ 490194 := by rw [pow_add]
          _ = 3821520225 := by rw [factor_2_18]; decide
      have factor_2_20 : (18 : ZMod 20078358301) ^ 1960777 = 7302600603 := by
        calc
          (18 : ZMod 20078358301) ^ 1960777 = (18 : ZMod 20078358301) ^ (980388 + 980388 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 980388 * (18 : ZMod 20078358301) ^ 980388) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 7302600603 := by rw [factor_2_19]; decide
      have factor_2_21 : (18 : ZMod 20078358301) ^ 3921554 = 1779131585 := by
        calc
          (18 : ZMod 20078358301) ^ 3921554 = (18 : ZMod 20078358301) ^ (1960777 + 1960777) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 1960777 * (18 : ZMod 20078358301) ^ 1960777 := by rw [pow_add]
          _ = 1779131585 := by rw [factor_2_20]; decide
      have factor_2_22 : (18 : ZMod 20078358301) ^ 7843108 = 2274999716 := by
        calc
          (18 : ZMod 20078358301) ^ 7843108 = (18 : ZMod 20078358301) ^ (3921554 + 3921554) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 3921554 * (18 : ZMod 20078358301) ^ 3921554 := by rw [pow_add]
          _ = 2274999716 := by rw [factor_2_21]; decide
      have factor_2_23 : (18 : ZMod 20078358301) ^ 15686217 = 17540908138 := by
        calc
          (18 : ZMod 20078358301) ^ 15686217 = (18 : ZMod 20078358301) ^ (7843108 + 7843108 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 7843108 * (18 : ZMod 20078358301) ^ 7843108) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 17540908138 := by rw [factor_2_22]; decide
      have factor_2_24 : (18 : ZMod 20078358301) ^ 31372434 = 923493085 := by
        calc
          (18 : ZMod 20078358301) ^ 31372434 = (18 : ZMod 20078358301) ^ (15686217 + 15686217) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 15686217 * (18 : ZMod 20078358301) ^ 15686217 := by rw [pow_add]
          _ = 923493085 := by rw [factor_2_23]; decide
      have factor_2_25 : (18 : ZMod 20078358301) ^ 62744869 = 18396951602 := by
        calc
          (18 : ZMod 20078358301) ^ 62744869 = (18 : ZMod 20078358301) ^ (31372434 + 31372434 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 31372434 * (18 : ZMod 20078358301) ^ 31372434) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 18396951602 := by rw [factor_2_24]; decide
      have factor_2_26 : (18 : ZMod 20078358301) ^ 125489739 = 17618967680 := by
        calc
          (18 : ZMod 20078358301) ^ 125489739 = (18 : ZMod 20078358301) ^ (62744869 + 62744869 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 62744869 * (18 : ZMod 20078358301) ^ 62744869) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 17618967680 := by rw [factor_2_25]; decide
      have factor_2_27 : (18 : ZMod 20078358301) ^ 250979478 = 1023843801 := by
        calc
          (18 : ZMod 20078358301) ^ 250979478 = (18 : ZMod 20078358301) ^ (125489739 + 125489739) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 125489739 * (18 : ZMod 20078358301) ^ 125489739 := by rw [pow_add]
          _ = 1023843801 := by rw [factor_2_26]; decide
      have factor_2_28 : (18 : ZMod 20078358301) ^ 501958957 = 10865670158 := by
        calc
          (18 : ZMod 20078358301) ^ 501958957 = (18 : ZMod 20078358301) ^ (250979478 + 250979478 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 250979478 * (18 : ZMod 20078358301) ^ 250979478) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 10865670158 := by rw [factor_2_27]; decide
      have factor_2_29 : (18 : ZMod 20078358301) ^ 1003917915 = 19611783967 := by
        calc
          (18 : ZMod 20078358301) ^ 1003917915 = (18 : ZMod 20078358301) ^ (501958957 + 501958957 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 501958957 * (18 : ZMod 20078358301) ^ 501958957) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 19611783967 := by rw [factor_2_28]; decide
      have factor_2_30 : (18 : ZMod 20078358301) ^ 2007835830 = 455554854 := by
        calc
          (18 : ZMod 20078358301) ^ 2007835830 = (18 : ZMod 20078358301) ^ (1003917915 + 1003917915) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 1003917915 * (18 : ZMod 20078358301) ^ 1003917915 := by rw [pow_add]
          _ = 455554854 := by rw [factor_2_29]; decide
      have factor_2_31 : (18 : ZMod 20078358301) ^ 4015671660 = 12428450801 := by
        calc
          (18 : ZMod 20078358301) ^ 4015671660 = (18 : ZMod 20078358301) ^ (2007835830 + 2007835830) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 2007835830 * (18 : ZMod 20078358301) ^ 2007835830 := by rw [pow_add]
          _ = 12428450801 := by rw [factor_2_30]; decide
      change (18 : ZMod 20078358301) ^ 4015671660 ≠ 1
      rw [factor_2_31]
      decide
    ·
      have factor_3_0 : (18 : ZMod 20078358301) ^ 1 = 18 := by norm_num
      have factor_3_1 : (18 : ZMod 20078358301) ^ 2 = 324 := by
        calc
          (18 : ZMod 20078358301) ^ 2 = (18 : ZMod 20078358301) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 1 * (18 : ZMod 20078358301) ^ 1 := by rw [pow_add]
          _ = 324 := by rw [factor_3_0]; decide
      have factor_3_2 : (18 : ZMod 20078358301) ^ 5 = 1889568 := by
        calc
          (18 : ZMod 20078358301) ^ 5 = (18 : ZMod 20078358301) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 2 * (18 : ZMod 20078358301) ^ 2) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 1889568 := by rw [factor_3_1]; decide
      have factor_3_3 : (18 : ZMod 20078358301) ^ 10 = 16597807347 := by
        calc
          (18 : ZMod 20078358301) ^ 10 = (18 : ZMod 20078358301) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 5 * (18 : ZMod 20078358301) ^ 5 := by rw [pow_add]
          _ = 16597807347 := by rw [factor_3_2]; decide
      have factor_3_4 : (18 : ZMod 20078358301) ^ 21 = 12869090723 := by
        calc
          (18 : ZMod 20078358301) ^ 21 = (18 : ZMod 20078358301) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 10 * (18 : ZMod 20078358301) ^ 10) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 12869090723 := by rw [factor_3_3]; decide
      have factor_3_5 : (18 : ZMod 20078358301) ^ 42 = 3877402095 := by
        calc
          (18 : ZMod 20078358301) ^ 42 = (18 : ZMod 20078358301) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 21 * (18 : ZMod 20078358301) ^ 21 := by rw [pow_add]
          _ = 3877402095 := by rw [factor_3_4]; decide
      have factor_3_6 : (18 : ZMod 20078358301) ^ 85 = 13450013569 := by
        calc
          (18 : ZMod 20078358301) ^ 85 = (18 : ZMod 20078358301) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 42 * (18 : ZMod 20078358301) ^ 42) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 13450013569 := by rw [factor_3_5]; decide
      have factor_3_7 : (18 : ZMod 20078358301) ^ 170 = 1344497612 := by
        calc
          (18 : ZMod 20078358301) ^ 170 = (18 : ZMod 20078358301) ^ (85 + 85) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 85 * (18 : ZMod 20078358301) ^ 85 := by rw [pow_add]
          _ = 1344497612 := by rw [factor_3_6]; decide
      have factor_3_8 : (18 : ZMod 20078358301) ^ 341 = 4126996552 := by
        calc
          (18 : ZMod 20078358301) ^ 341 = (18 : ZMod 20078358301) ^ (170 + 170 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 170 * (18 : ZMod 20078358301) ^ 170) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 4126996552 := by rw [factor_3_7]; decide
      have factor_3_9 : (18 : ZMod 20078358301) ^ 683 = 10848448296 := by
        calc
          (18 : ZMod 20078358301) ^ 683 = (18 : ZMod 20078358301) ^ (341 + 341 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 341 * (18 : ZMod 20078358301) ^ 341) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 10848448296 := by rw [factor_3_8]; decide
      have factor_3_10 : (18 : ZMod 20078358301) ^ 1367 = 2062502324 := by
        calc
          (18 : ZMod 20078358301) ^ 1367 = (18 : ZMod 20078358301) ^ (683 + 683 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 683 * (18 : ZMod 20078358301) ^ 683) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 2062502324 := by rw [factor_3_9]; decide
      have factor_3_11 : (18 : ZMod 20078358301) ^ 2735 = 15785783210 := by
        calc
          (18 : ZMod 20078358301) ^ 2735 = (18 : ZMod 20078358301) ^ (1367 + 1367 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 1367 * (18 : ZMod 20078358301) ^ 1367) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 15785783210 := by rw [factor_3_10]; decide
      have factor_3_12 : (18 : ZMod 20078358301) ^ 5470 = 1440144363 := by
        calc
          (18 : ZMod 20078358301) ^ 5470 = (18 : ZMod 20078358301) ^ (2735 + 2735) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 2735 * (18 : ZMod 20078358301) ^ 2735 := by rw [pow_add]
          _ = 1440144363 := by rw [factor_3_11]; decide
      have factor_3_13 : (18 : ZMod 20078358301) ^ 10941 = 11492684730 := by
        calc
          (18 : ZMod 20078358301) ^ 10941 = (18 : ZMod 20078358301) ^ (5470 + 5470 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 5470 * (18 : ZMod 20078358301) ^ 5470) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 11492684730 := by rw [factor_3_12]; decide
      have factor_3_14 : (18 : ZMod 20078358301) ^ 21883 = 14818964785 := by
        calc
          (18 : ZMod 20078358301) ^ 21883 = (18 : ZMod 20078358301) ^ (10941 + 10941 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 10941 * (18 : ZMod 20078358301) ^ 10941) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 14818964785 := by rw [factor_3_13]; decide
      have factor_3_15 : (18 : ZMod 20078358301) ^ 43767 = 14206865698 := by
        calc
          (18 : ZMod 20078358301) ^ 43767 = (18 : ZMod 20078358301) ^ (21883 + 21883 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 21883 * (18 : ZMod 20078358301) ^ 21883) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 14206865698 := by rw [factor_3_14]; decide
      have factor_3_16 : (18 : ZMod 20078358301) ^ 87534 = 16315754078 := by
        calc
          (18 : ZMod 20078358301) ^ 87534 = (18 : ZMod 20078358301) ^ (43767 + 43767) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 43767 * (18 : ZMod 20078358301) ^ 43767 := by rw [pow_add]
          _ = 16315754078 := by rw [factor_3_15]; decide
      have factor_3_17 : (18 : ZMod 20078358301) ^ 175069 = 4004412521 := by
        calc
          (18 : ZMod 20078358301) ^ 175069 = (18 : ZMod 20078358301) ^ (87534 + 87534 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 87534 * (18 : ZMod 20078358301) ^ 87534) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 4004412521 := by rw [factor_3_16]; decide
      have factor_3_18 : (18 : ZMod 20078358301) ^ 350138 = 689421451 := by
        calc
          (18 : ZMod 20078358301) ^ 350138 = (18 : ZMod 20078358301) ^ (175069 + 175069) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 175069 * (18 : ZMod 20078358301) ^ 175069 := by rw [pow_add]
          _ = 689421451 := by rw [factor_3_17]; decide
      have factor_3_19 : (18 : ZMod 20078358301) ^ 700277 = 14717241908 := by
        calc
          (18 : ZMod 20078358301) ^ 700277 = (18 : ZMod 20078358301) ^ (350138 + 350138 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 350138 * (18 : ZMod 20078358301) ^ 350138) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 14717241908 := by rw [factor_3_18]; decide
      have factor_3_20 : (18 : ZMod 20078358301) ^ 1400555 = 19067012608 := by
        calc
          (18 : ZMod 20078358301) ^ 1400555 = (18 : ZMod 20078358301) ^ (700277 + 700277 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 700277 * (18 : ZMod 20078358301) ^ 700277) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 19067012608 := by rw [factor_3_19]; decide
      have factor_3_21 : (18 : ZMod 20078358301) ^ 2801110 = 7549564528 := by
        calc
          (18 : ZMod 20078358301) ^ 2801110 = (18 : ZMod 20078358301) ^ (1400555 + 1400555) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 1400555 * (18 : ZMod 20078358301) ^ 1400555 := by rw [pow_add]
          _ = 7549564528 := by rw [factor_3_20]; decide
      have factor_3_22 : (18 : ZMod 20078358301) ^ 5602220 = 8232789642 := by
        calc
          (18 : ZMod 20078358301) ^ 5602220 = (18 : ZMod 20078358301) ^ (2801110 + 2801110) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 2801110 * (18 : ZMod 20078358301) ^ 2801110 := by rw [pow_add]
          _ = 8232789642 := by rw [factor_3_21]; decide
      have factor_3_23 : (18 : ZMod 20078358301) ^ 11204441 = 10273823390 := by
        calc
          (18 : ZMod 20078358301) ^ 11204441 = (18 : ZMod 20078358301) ^ (5602220 + 5602220 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 5602220 * (18 : ZMod 20078358301) ^ 5602220) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 10273823390 := by rw [factor_3_22]; decide
      have factor_3_24 : (18 : ZMod 20078358301) ^ 22408882 = 3739140033 := by
        calc
          (18 : ZMod 20078358301) ^ 22408882 = (18 : ZMod 20078358301) ^ (11204441 + 11204441) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 11204441 * (18 : ZMod 20078358301) ^ 11204441 := by rw [pow_add]
          _ = 3739140033 := by rw [factor_3_23]; decide
      have factor_3_25 : (18 : ZMod 20078358301) ^ 44817764 = 11371769043 := by
        calc
          (18 : ZMod 20078358301) ^ 44817764 = (18 : ZMod 20078358301) ^ (22408882 + 22408882) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 22408882 * (18 : ZMod 20078358301) ^ 22408882 := by rw [pow_add]
          _ = 11371769043 := by rw [factor_3_24]; decide
      have factor_3_26 : (18 : ZMod 20078358301) ^ 89635528 = 11652979604 := by
        calc
          (18 : ZMod 20078358301) ^ 89635528 = (18 : ZMod 20078358301) ^ (44817764 + 44817764) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 44817764 * (18 : ZMod 20078358301) ^ 44817764 := by rw [pow_add]
          _ = 11652979604 := by rw [factor_3_25]; decide
      have factor_3_27 : (18 : ZMod 20078358301) ^ 179271056 = 10176053483 := by
        calc
          (18 : ZMod 20078358301) ^ 179271056 = (18 : ZMod 20078358301) ^ (89635528 + 89635528) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 89635528 * (18 : ZMod 20078358301) ^ 89635528 := by rw [pow_add]
          _ = 10176053483 := by rw [factor_3_26]; decide
      have factor_3_28 : (18 : ZMod 20078358301) ^ 358542112 = 3862742008 := by
        calc
          (18 : ZMod 20078358301) ^ 358542112 = (18 : ZMod 20078358301) ^ (179271056 + 179271056) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 179271056 * (18 : ZMod 20078358301) ^ 179271056 := by rw [pow_add]
          _ = 3862742008 := by rw [factor_3_27]; decide
      have factor_3_29 : (18 : ZMod 20078358301) ^ 717084225 = 5008458286 := by
        calc
          (18 : ZMod 20078358301) ^ 717084225 = (18 : ZMod 20078358301) ^ (358542112 + 358542112 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 358542112 * (18 : ZMod 20078358301) ^ 358542112) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 5008458286 := by rw [factor_3_28]; decide
      have factor_3_30 : (18 : ZMod 20078358301) ^ 1434168450 = 5815983876 := by
        calc
          (18 : ZMod 20078358301) ^ 1434168450 = (18 : ZMod 20078358301) ^ (717084225 + 717084225) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 717084225 * (18 : ZMod 20078358301) ^ 717084225 := by rw [pow_add]
          _ = 5815983876 := by rw [factor_3_29]; decide
      have factor_3_31 : (18 : ZMod 20078358301) ^ 2868336900 = 10090641299 := by
        calc
          (18 : ZMod 20078358301) ^ 2868336900 = (18 : ZMod 20078358301) ^ (1434168450 + 1434168450) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 1434168450 * (18 : ZMod 20078358301) ^ 1434168450 := by rw [pow_add]
          _ = 10090641299 := by rw [factor_3_30]; decide
      change (18 : ZMod 20078358301) ^ 2868336900 ≠ 1
      rw [factor_3_31]
      decide
    ·
      have factor_4_0 : (18 : ZMod 20078358301) ^ 1 = 18 := by norm_num
      have factor_4_1 : (18 : ZMod 20078358301) ^ 3 = 5832 := by
        calc
          (18 : ZMod 20078358301) ^ 3 = (18 : ZMod 20078358301) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 1 * (18 : ZMod 20078358301) ^ 1) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 5832 := by rw [factor_4_0]; decide
      have factor_4_2 : (18 : ZMod 20078358301) ^ 6 = 34012224 := by
        calc
          (18 : ZMod 20078358301) ^ 6 = (18 : ZMod 20078358301) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 3 * (18 : ZMod 20078358301) ^ 3 := by rw [pow_add]
          _ = 34012224 := by rw [factor_4_1]; decide
      have factor_4_3 : (18 : ZMod 20078358301) ^ 13 = 647078583 := by
        calc
          (18 : ZMod 20078358301) ^ 13 = (18 : ZMod 20078358301) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 6 * (18 : ZMod 20078358301) ^ 6) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 647078583 := by rw [factor_4_2]; decide
      have factor_4_4 : (18 : ZMod 20078358301) ^ 27 = 12515803343 := by
        calc
          (18 : ZMod 20078358301) ^ 27 = (18 : ZMod 20078358301) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 13 * (18 : ZMod 20078358301) ^ 13) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 12515803343 := by rw [factor_4_3]; decide
      have factor_4_5 : (18 : ZMod 20078358301) ^ 54 = 2816609282 := by
        calc
          (18 : ZMod 20078358301) ^ 54 = (18 : ZMod 20078358301) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 27 * (18 : ZMod 20078358301) ^ 27 := by rw [pow_add]
          _ = 2816609282 := by rw [factor_4_4]; decide
      have factor_4_6 : (18 : ZMod 20078358301) ^ 108 = 781651164 := by
        calc
          (18 : ZMod 20078358301) ^ 108 = (18 : ZMod 20078358301) ^ (54 + 54) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 54 * (18 : ZMod 20078358301) ^ 54 := by rw [pow_add]
          _ = 781651164 := by rw [factor_4_5]; decide
      have factor_4_7 : (18 : ZMod 20078358301) ^ 217 = 18090018719 := by
        calc
          (18 : ZMod 20078358301) ^ 217 = (18 : ZMod 20078358301) ^ (108 + 108 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 108 * (18 : ZMod 20078358301) ^ 108) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 18090018719 := by rw [factor_4_6]; decide
      have factor_4_8 : (18 : ZMod 20078358301) ^ 435 = 5603216573 := by
        calc
          (18 : ZMod 20078358301) ^ 435 = (18 : ZMod 20078358301) ^ (217 + 217 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 217 * (18 : ZMod 20078358301) ^ 217) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 5603216573 := by rw [factor_4_7]; decide
      have factor_4_9 : (18 : ZMod 20078358301) ^ 870 = 12364453879 := by
        calc
          (18 : ZMod 20078358301) ^ 870 = (18 : ZMod 20078358301) ^ (435 + 435) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 435 * (18 : ZMod 20078358301) ^ 435 := by rw [pow_add]
          _ = 12364453879 := by rw [factor_4_8]; decide
      have factor_4_10 : (18 : ZMod 20078358301) ^ 1740 = 5463071465 := by
        calc
          (18 : ZMod 20078358301) ^ 1740 = (18 : ZMod 20078358301) ^ (870 + 870) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 870 * (18 : ZMod 20078358301) ^ 870 := by rw [pow_add]
          _ = 5463071465 := by rw [factor_4_9]; decide
      have factor_4_11 : (18 : ZMod 20078358301) ^ 3481 = 4288236384 := by
        calc
          (18 : ZMod 20078358301) ^ 3481 = (18 : ZMod 20078358301) ^ (1740 + 1740 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 1740 * (18 : ZMod 20078358301) ^ 1740) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 4288236384 := by rw [factor_4_10]; decide
      have factor_4_12 : (18 : ZMod 20078358301) ^ 6962 = 7921686855 := by
        calc
          (18 : ZMod 20078358301) ^ 6962 = (18 : ZMod 20078358301) ^ (3481 + 3481) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 3481 * (18 : ZMod 20078358301) ^ 3481 := by rw [pow_add]
          _ = 7921686855 := by rw [factor_4_11]; decide
      have factor_4_13 : (18 : ZMod 20078358301) ^ 13925 = 18872394994 := by
        calc
          (18 : ZMod 20078358301) ^ 13925 = (18 : ZMod 20078358301) ^ (6962 + 6962 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 6962 * (18 : ZMod 20078358301) ^ 6962) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 18872394994 := by rw [factor_4_12]; decide
      have factor_4_14 : (18 : ZMod 20078358301) ^ 27851 = 11415986330 := by
        calc
          (18 : ZMod 20078358301) ^ 27851 = (18 : ZMod 20078358301) ^ (13925 + 13925 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 13925 * (18 : ZMod 20078358301) ^ 13925) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 11415986330 := by rw [factor_4_13]; decide
      have factor_4_15 : (18 : ZMod 20078358301) ^ 55703 = 17712360634 := by
        calc
          (18 : ZMod 20078358301) ^ 55703 = (18 : ZMod 20078358301) ^ (27851 + 27851 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 27851 * (18 : ZMod 20078358301) ^ 27851) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 17712360634 := by rw [factor_4_14]; decide
      have factor_4_16 : (18 : ZMod 20078358301) ^ 111407 = 15803131950 := by
        calc
          (18 : ZMod 20078358301) ^ 111407 = (18 : ZMod 20078358301) ^ (55703 + 55703 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 55703 * (18 : ZMod 20078358301) ^ 55703) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 15803131950 := by rw [factor_4_15]; decide
      have factor_4_17 : (18 : ZMod 20078358301) ^ 222815 = 3509718417 := by
        calc
          (18 : ZMod 20078358301) ^ 222815 = (18 : ZMod 20078358301) ^ (111407 + 111407 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 111407 * (18 : ZMod 20078358301) ^ 111407) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 3509718417 := by rw [factor_4_16]; decide
      have factor_4_18 : (18 : ZMod 20078358301) ^ 445631 = 10493977886 := by
        calc
          (18 : ZMod 20078358301) ^ 445631 = (18 : ZMod 20078358301) ^ (222815 + 222815 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 222815 * (18 : ZMod 20078358301) ^ 222815) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 10493977886 := by rw [factor_4_17]; decide
      have factor_4_19 : (18 : ZMod 20078358301) ^ 891262 = 18575932053 := by
        calc
          (18 : ZMod 20078358301) ^ 891262 = (18 : ZMod 20078358301) ^ (445631 + 445631) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 445631 * (18 : ZMod 20078358301) ^ 445631 := by rw [pow_add]
          _ = 18575932053 := by rw [factor_4_18]; decide
      have factor_4_20 : (18 : ZMod 20078358301) ^ 1782524 = 15540292540 := by
        calc
          (18 : ZMod 20078358301) ^ 1782524 = (18 : ZMod 20078358301) ^ (891262 + 891262) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 891262 * (18 : ZMod 20078358301) ^ 891262 := by rw [pow_add]
          _ = 15540292540 := by rw [factor_4_19]; decide
      have factor_4_21 : (18 : ZMod 20078358301) ^ 3565049 = 2832853847 := by
        calc
          (18 : ZMod 20078358301) ^ 3565049 = (18 : ZMod 20078358301) ^ (1782524 + 1782524 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 1782524 * (18 : ZMod 20078358301) ^ 1782524) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 2832853847 := by rw [factor_4_20]; decide
      have factor_4_22 : (18 : ZMod 20078358301) ^ 7130098 = 15983290804 := by
        calc
          (18 : ZMod 20078358301) ^ 7130098 = (18 : ZMod 20078358301) ^ (3565049 + 3565049) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 3565049 * (18 : ZMod 20078358301) ^ 3565049 := by rw [pow_add]
          _ = 15983290804 := by rw [factor_4_21]; decide
      have factor_4_23 : (18 : ZMod 20078358301) ^ 14260197 = 16384072273 := by
        calc
          (18 : ZMod 20078358301) ^ 14260197 = (18 : ZMod 20078358301) ^ (7130098 + 7130098 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 7130098 * (18 : ZMod 20078358301) ^ 7130098) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 16384072273 := by rw [factor_4_22]; decide
      have factor_4_24 : (18 : ZMod 20078358301) ^ 28520395 = 11500654923 := by
        calc
          (18 : ZMod 20078358301) ^ 28520395 = (18 : ZMod 20078358301) ^ (14260197 + 14260197 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 14260197 * (18 : ZMod 20078358301) ^ 14260197) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 11500654923 := by rw [factor_4_23]; decide
      have factor_4_25 : (18 : ZMod 20078358301) ^ 57040790 = 7494762993 := by
        calc
          (18 : ZMod 20078358301) ^ 57040790 = (18 : ZMod 20078358301) ^ (28520395 + 28520395) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 28520395 * (18 : ZMod 20078358301) ^ 28520395 := by rw [pow_add]
          _ = 7494762993 := by rw [factor_4_24]; decide
      have factor_4_26 : (18 : ZMod 20078358301) ^ 114081581 = 7331020061 := by
        calc
          (18 : ZMod 20078358301) ^ 114081581 = (18 : ZMod 20078358301) ^ (57040790 + 57040790 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 57040790 * (18 : ZMod 20078358301) ^ 57040790) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 7331020061 := by rw [factor_4_25]; decide
      have factor_4_27 : (18 : ZMod 20078358301) ^ 228163162 = 7694984770 := by
        calc
          (18 : ZMod 20078358301) ^ 228163162 = (18 : ZMod 20078358301) ^ (114081581 + 114081581) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 114081581 * (18 : ZMod 20078358301) ^ 114081581 := by rw [pow_add]
          _ = 7694984770 := by rw [factor_4_26]; decide
      have factor_4_28 : (18 : ZMod 20078358301) ^ 456326325 = 14001884731 := by
        calc
          (18 : ZMod 20078358301) ^ 456326325 = (18 : ZMod 20078358301) ^ (228163162 + 228163162 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 228163162 * (18 : ZMod 20078358301) ^ 228163162) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 14001884731 := by rw [factor_4_27]; decide
      have factor_4_29 : (18 : ZMod 20078358301) ^ 912652650 = 15413202183 := by
        calc
          (18 : ZMod 20078358301) ^ 912652650 = (18 : ZMod 20078358301) ^ (456326325 + 456326325) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 456326325 * (18 : ZMod 20078358301) ^ 456326325 := by rw [pow_add]
          _ = 15413202183 := by rw [factor_4_28]; decide
      have factor_4_30 : (18 : ZMod 20078358301) ^ 1825305300 = 19702511119 := by
        calc
          (18 : ZMod 20078358301) ^ 1825305300 = (18 : ZMod 20078358301) ^ (912652650 + 912652650) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 912652650 * (18 : ZMod 20078358301) ^ 912652650 := by rw [pow_add]
          _ = 19702511119 := by rw [factor_4_29]; decide
      change (18 : ZMod 20078358301) ^ 1825305300 ≠ 1
      rw [factor_4_30]
      decide
    ·
      have factor_5_0 : (18 : ZMod 20078358301) ^ 1 = 18 := by norm_num
      have factor_5_1 : (18 : ZMod 20078358301) ^ 2 = 324 := by
        calc
          (18 : ZMod 20078358301) ^ 2 = (18 : ZMod 20078358301) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 1 * (18 : ZMod 20078358301) ^ 1 := by rw [pow_add]
          _ = 324 := by rw [factor_5_0]; decide
      have factor_5_2 : (18 : ZMod 20078358301) ^ 5 = 1889568 := by
        calc
          (18 : ZMod 20078358301) ^ 5 = (18 : ZMod 20078358301) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 2 * (18 : ZMod 20078358301) ^ 2) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 1889568 := by rw [factor_5_1]; decide
      have factor_5_3 : (18 : ZMod 20078358301) ^ 11 = 17663516032 := by
        calc
          (18 : ZMod 20078358301) ^ 11 = (18 : ZMod 20078358301) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 5 * (18 : ZMod 20078358301) ^ 5) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 17663516032 := by rw [factor_5_2]; decide
      have factor_5_4 : (18 : ZMod 20078358301) ^ 23 = 13365225945 := by
        calc
          (18 : ZMod 20078358301) ^ 23 = (18 : ZMod 20078358301) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 11 * (18 : ZMod 20078358301) ^ 11) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 13365225945 := by rw [factor_5_3]; decide
      have factor_5_5 : (18 : ZMod 20078358301) ^ 46 = 5682846848 := by
        calc
          (18 : ZMod 20078358301) ^ 46 = (18 : ZMod 20078358301) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 23 * (18 : ZMod 20078358301) ^ 23 := by rw [pow_add]
          _ = 5682846848 := by rw [factor_5_4]; decide
      have factor_5_6 : (18 : ZMod 20078358301) ^ 92 = 9103789404 := by
        calc
          (18 : ZMod 20078358301) ^ 92 = (18 : ZMod 20078358301) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 46 * (18 : ZMod 20078358301) ^ 46 := by rw [pow_add]
          _ = 9103789404 := by rw [factor_5_5]; decide
      have factor_5_7 : (18 : ZMod 20078358301) ^ 184 = 15740891620 := by
        calc
          (18 : ZMod 20078358301) ^ 184 = (18 : ZMod 20078358301) ^ (92 + 92) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 92 * (18 : ZMod 20078358301) ^ 92 := by rw [pow_add]
          _ = 15740891620 := by rw [factor_5_6]; decide
      have factor_5_8 : (18 : ZMod 20078358301) ^ 368 = 17930095526 := by
        calc
          (18 : ZMod 20078358301) ^ 368 = (18 : ZMod 20078358301) ^ (184 + 184) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 184 * (18 : ZMod 20078358301) ^ 184 := by rw [pow_add]
          _ = 17930095526 := by rw [factor_5_7]; decide
      have factor_5_9 : (18 : ZMod 20078358301) ^ 736 = 7988136515 := by
        calc
          (18 : ZMod 20078358301) ^ 736 = (18 : ZMod 20078358301) ^ (368 + 368) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 368 * (18 : ZMod 20078358301) ^ 368 := by rw [pow_add]
          _ = 7988136515 := by rw [factor_5_8]; decide
      have factor_5_10 : (18 : ZMod 20078358301) ^ 1472 = 19378942365 := by
        calc
          (18 : ZMod 20078358301) ^ 1472 = (18 : ZMod 20078358301) ^ (736 + 736) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 736 * (18 : ZMod 20078358301) ^ 736 := by rw [pow_add]
          _ = 19378942365 := by rw [factor_5_9]; decide
      have factor_5_11 : (18 : ZMod 20078358301) ^ 2945 = 12489961829 := by
        calc
          (18 : ZMod 20078358301) ^ 2945 = (18 : ZMod 20078358301) ^ (1472 + 1472 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 1472 * (18 : ZMod 20078358301) ^ 1472) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 12489961829 := by rw [factor_5_10]; decide
      have factor_5_12 : (18 : ZMod 20078358301) ^ 5891 = 3252783135 := by
        calc
          (18 : ZMod 20078358301) ^ 5891 = (18 : ZMod 20078358301) ^ (2945 + 2945 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 2945 * (18 : ZMod 20078358301) ^ 2945) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 3252783135 := by rw [factor_5_11]; decide
      have factor_5_13 : (18 : ZMod 20078358301) ^ 11783 = 18261138135 := by
        calc
          (18 : ZMod 20078358301) ^ 11783 = (18 : ZMod 20078358301) ^ (5891 + 5891 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 5891 * (18 : ZMod 20078358301) ^ 5891) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 18261138135 := by rw [factor_5_12]; decide
      have factor_5_14 : (18 : ZMod 20078358301) ^ 23567 = 6837584026 := by
        calc
          (18 : ZMod 20078358301) ^ 23567 = (18 : ZMod 20078358301) ^ (11783 + 11783 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 11783 * (18 : ZMod 20078358301) ^ 11783) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 6837584026 := by rw [factor_5_13]; decide
      have factor_5_15 : (18 : ZMod 20078358301) ^ 47134 = 6265001495 := by
        calc
          (18 : ZMod 20078358301) ^ 47134 = (18 : ZMod 20078358301) ^ (23567 + 23567) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 23567 * (18 : ZMod 20078358301) ^ 23567 := by rw [pow_add]
          _ = 6265001495 := by rw [factor_5_14]; decide
      have factor_5_16 : (18 : ZMod 20078358301) ^ 94268 = 13996564688 := by
        calc
          (18 : ZMod 20078358301) ^ 94268 = (18 : ZMod 20078358301) ^ (47134 + 47134) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 47134 * (18 : ZMod 20078358301) ^ 47134 := by rw [pow_add]
          _ = 13996564688 := by rw [factor_5_15]; decide
      have factor_5_17 : (18 : ZMod 20078358301) ^ 188536 = 8052146348 := by
        calc
          (18 : ZMod 20078358301) ^ 188536 = (18 : ZMod 20078358301) ^ (94268 + 94268) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 94268 * (18 : ZMod 20078358301) ^ 94268 := by rw [pow_add]
          _ = 8052146348 := by rw [factor_5_16]; decide
      have factor_5_18 : (18 : ZMod 20078358301) ^ 377072 = 1841312600 := by
        calc
          (18 : ZMod 20078358301) ^ 377072 = (18 : ZMod 20078358301) ^ (188536 + 188536) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 188536 * (18 : ZMod 20078358301) ^ 188536 := by rw [pow_add]
          _ = 1841312600 := by rw [factor_5_17]; decide
      have factor_5_19 : (18 : ZMod 20078358301) ^ 754145 = 12161173045 := by
        calc
          (18 : ZMod 20078358301) ^ 754145 = (18 : ZMod 20078358301) ^ (377072 + 377072 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 377072 * (18 : ZMod 20078358301) ^ 377072) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 12161173045 := by rw [factor_5_18]; decide
      have factor_5_20 : (18 : ZMod 20078358301) ^ 1508290 = 17278856800 := by
        calc
          (18 : ZMod 20078358301) ^ 1508290 = (18 : ZMod 20078358301) ^ (754145 + 754145) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 754145 * (18 : ZMod 20078358301) ^ 754145 := by rw [pow_add]
          _ = 17278856800 := by rw [factor_5_19]; decide
      have factor_5_21 : (18 : ZMod 20078358301) ^ 3016580 = 8516593453 := by
        calc
          (18 : ZMod 20078358301) ^ 3016580 = (18 : ZMod 20078358301) ^ (1508290 + 1508290) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 1508290 * (18 : ZMod 20078358301) ^ 1508290 := by rw [pow_add]
          _ = 8516593453 := by rw [factor_5_20]; decide
      have factor_5_22 : (18 : ZMod 20078358301) ^ 6033160 = 13968719038 := by
        calc
          (18 : ZMod 20078358301) ^ 6033160 = (18 : ZMod 20078358301) ^ (3016580 + 3016580) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 3016580 * (18 : ZMod 20078358301) ^ 3016580 := by rw [pow_add]
          _ = 13968719038 := by rw [factor_5_21]; decide
      have factor_5_23 : (18 : ZMod 20078358301) ^ 12066321 = 14474235993 := by
        calc
          (18 : ZMod 20078358301) ^ 12066321 = (18 : ZMod 20078358301) ^ (6033160 + 6033160 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 6033160 * (18 : ZMod 20078358301) ^ 6033160) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 14474235993 := by rw [factor_5_22]; decide
      have factor_5_24 : (18 : ZMod 20078358301) ^ 24132642 = 16388107951 := by
        calc
          (18 : ZMod 20078358301) ^ 24132642 = (18 : ZMod 20078358301) ^ (12066321 + 12066321) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 12066321 * (18 : ZMod 20078358301) ^ 12066321 := by rw [pow_add]
          _ = 16388107951 := by rw [factor_5_23]; decide
      have factor_5_25 : (18 : ZMod 20078358301) ^ 48265284 = 4160843905 := by
        calc
          (18 : ZMod 20078358301) ^ 48265284 = (18 : ZMod 20078358301) ^ (24132642 + 24132642) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 24132642 * (18 : ZMod 20078358301) ^ 24132642 := by rw [pow_add]
          _ = 4160843905 := by rw [factor_5_24]; decide
      have factor_5_26 : (18 : ZMod 20078358301) ^ 96530568 = 12163508359 := by
        calc
          (18 : ZMod 20078358301) ^ 96530568 = (18 : ZMod 20078358301) ^ (48265284 + 48265284) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 48265284 * (18 : ZMod 20078358301) ^ 48265284 := by rw [pow_add]
          _ = 12163508359 := by rw [factor_5_25]; decide
      have factor_5_27 : (18 : ZMod 20078358301) ^ 193061137 = 3374976623 := by
        calc
          (18 : ZMod 20078358301) ^ 193061137 = (18 : ZMod 20078358301) ^ (96530568 + 96530568 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 96530568 * (18 : ZMod 20078358301) ^ 96530568) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 3374976623 := by rw [factor_5_26]; decide
      have factor_5_28 : (18 : ZMod 20078358301) ^ 386122275 = 8026502486 := by
        calc
          (18 : ZMod 20078358301) ^ 386122275 = (18 : ZMod 20078358301) ^ (193061137 + 193061137 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 193061137 * (18 : ZMod 20078358301) ^ 193061137) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 8026502486 := by rw [factor_5_27]; decide
      have factor_5_29 : (18 : ZMod 20078358301) ^ 772244550 = 15083700269 := by
        calc
          (18 : ZMod 20078358301) ^ 772244550 = (18 : ZMod 20078358301) ^ (386122275 + 386122275) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 386122275 * (18 : ZMod 20078358301) ^ 386122275 := by rw [pow_add]
          _ = 15083700269 := by rw [factor_5_28]; decide
      have factor_5_30 : (18 : ZMod 20078358301) ^ 1544489100 = 19875594745 := by
        calc
          (18 : ZMod 20078358301) ^ 1544489100 = (18 : ZMod 20078358301) ^ (772244550 + 772244550) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 772244550 * (18 : ZMod 20078358301) ^ 772244550 := by rw [pow_add]
          _ = 19875594745 := by rw [factor_5_29]; decide
      change (18 : ZMod 20078358301) ^ 1544489100 ≠ 1
      rw [factor_5_30]
      decide
    ·
      have factor_6_0 : (18 : ZMod 20078358301) ^ 1 = 18 := by norm_num
      have factor_6_1 : (18 : ZMod 20078358301) ^ 2 = 324 := by
        calc
          (18 : ZMod 20078358301) ^ 2 = (18 : ZMod 20078358301) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 1 * (18 : ZMod 20078358301) ^ 1 := by rw [pow_add]
          _ = 324 := by rw [factor_6_0]; decide
      have factor_6_2 : (18 : ZMod 20078358301) ^ 4 = 104976 := by
        calc
          (18 : ZMod 20078358301) ^ 4 = (18 : ZMod 20078358301) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 2 * (18 : ZMod 20078358301) ^ 2 := by rw [pow_add]
          _ = 104976 := by rw [factor_6_1]; decide
      have factor_6_3 : (18 : ZMod 20078358301) ^ 8 = 11019960576 := by
        calc
          (18 : ZMod 20078358301) ^ 8 = (18 : ZMod 20078358301) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 4 * (18 : ZMod 20078358301) ^ 4 := by rw [pow_add]
          _ = 11019960576 := by rw [factor_6_2]; decide
      have factor_6_4 : (18 : ZMod 20078358301) ^ 17 = 2635196725 := by
        calc
          (18 : ZMod 20078358301) ^ 17 = (18 : ZMod 20078358301) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 8 * (18 : ZMod 20078358301) ^ 8) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 2635196725 := by rw [factor_6_3]; decide
      have factor_6_5 : (18 : ZMod 20078358301) ^ 35 = 9716519313 := by
        calc
          (18 : ZMod 20078358301) ^ 35 = (18 : ZMod 20078358301) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 17 * (18 : ZMod 20078358301) ^ 17) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 9716519313 := by rw [factor_6_4]; decide
      have factor_6_6 : (18 : ZMod 20078358301) ^ 70 = 5936431778 := by
        calc
          (18 : ZMod 20078358301) ^ 70 = (18 : ZMod 20078358301) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 35 * (18 : ZMod 20078358301) ^ 35 := by rw [pow_add]
          _ = 5936431778 := by rw [factor_6_5]; decide
      have factor_6_7 : (18 : ZMod 20078358301) ^ 140 = 3482980135 := by
        calc
          (18 : ZMod 20078358301) ^ 140 = (18 : ZMod 20078358301) ^ (70 + 70) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 70 * (18 : ZMod 20078358301) ^ 70 := by rw [pow_add]
          _ = 3482980135 := by rw [factor_6_6]; decide
      have factor_6_8 : (18 : ZMod 20078358301) ^ 281 = 6512895189 := by
        calc
          (18 : ZMod 20078358301) ^ 281 = (18 : ZMod 20078358301) ^ (140 + 140 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 140 * (18 : ZMod 20078358301) ^ 140) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 6512895189 := by rw [factor_6_7]; decide
      have factor_6_9 : (18 : ZMod 20078358301) ^ 563 = 6740683609 := by
        calc
          (18 : ZMod 20078358301) ^ 563 = (18 : ZMod 20078358301) ^ (281 + 281 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 281 * (18 : ZMod 20078358301) ^ 281) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 6740683609 := by rw [factor_6_8]; decide
      have factor_6_10 : (18 : ZMod 20078358301) ^ 1126 = 9193286348 := by
        calc
          (18 : ZMod 20078358301) ^ 1126 = (18 : ZMod 20078358301) ^ (563 + 563) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 563 * (18 : ZMod 20078358301) ^ 563 := by rw [pow_add]
          _ = 9193286348 := by rw [factor_6_9]; decide
      have factor_6_11 : (18 : ZMod 20078358301) ^ 2252 = 5066280923 := by
        calc
          (18 : ZMod 20078358301) ^ 2252 = (18 : ZMod 20078358301) ^ (1126 + 1126) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 1126 * (18 : ZMod 20078358301) ^ 1126 := by rw [pow_add]
          _ = 5066280923 := by rw [factor_6_10]; decide
      have factor_6_12 : (18 : ZMod 20078358301) ^ 4505 = 17996982888 := by
        calc
          (18 : ZMod 20078358301) ^ 4505 = (18 : ZMod 20078358301) ^ (2252 + 2252 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 2252 * (18 : ZMod 20078358301) ^ 2252) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 17996982888 := by rw [factor_6_11]; decide
      have factor_6_13 : (18 : ZMod 20078358301) ^ 9010 = 16447679622 := by
        calc
          (18 : ZMod 20078358301) ^ 9010 = (18 : ZMod 20078358301) ^ (4505 + 4505) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 4505 * (18 : ZMod 20078358301) ^ 4505 := by rw [pow_add]
          _ = 16447679622 := by rw [factor_6_12]; decide
      have factor_6_14 : (18 : ZMod 20078358301) ^ 18021 = 3220495091 := by
        calc
          (18 : ZMod 20078358301) ^ 18021 = (18 : ZMod 20078358301) ^ (9010 + 9010 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 9010 * (18 : ZMod 20078358301) ^ 9010) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 3220495091 := by rw [factor_6_13]; decide
      have factor_6_15 : (18 : ZMod 20078358301) ^ 36043 = 519051068 := by
        calc
          (18 : ZMod 20078358301) ^ 36043 = (18 : ZMod 20078358301) ^ (18021 + 18021 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 18021 * (18 : ZMod 20078358301) ^ 18021) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 519051068 := by rw [factor_6_14]; decide
      have factor_6_16 : (18 : ZMod 20078358301) ^ 72087 = 8589365902 := by
        calc
          (18 : ZMod 20078358301) ^ 72087 = (18 : ZMod 20078358301) ^ (36043 + 36043 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 36043 * (18 : ZMod 20078358301) ^ 36043) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 8589365902 := by rw [factor_6_15]; decide
      have factor_6_17 : (18 : ZMod 20078358301) ^ 144174 = 15184004213 := by
        calc
          (18 : ZMod 20078358301) ^ 144174 = (18 : ZMod 20078358301) ^ (72087 + 72087) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 72087 * (18 : ZMod 20078358301) ^ 72087 := by rw [pow_add]
          _ = 15184004213 := by rw [factor_6_16]; decide
      have factor_6_18 : (18 : ZMod 20078358301) ^ 288349 = 5592572242 := by
        calc
          (18 : ZMod 20078358301) ^ 288349 = (18 : ZMod 20078358301) ^ (144174 + 144174 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 144174 * (18 : ZMod 20078358301) ^ 144174) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 5592572242 := by rw [factor_6_17]; decide
      have factor_6_19 : (18 : ZMod 20078358301) ^ 576699 = 9289126681 := by
        calc
          (18 : ZMod 20078358301) ^ 576699 = (18 : ZMod 20078358301) ^ (288349 + 288349 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 288349 * (18 : ZMod 20078358301) ^ 288349) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 9289126681 := by rw [factor_6_18]; decide
      have factor_6_20 : (18 : ZMod 20078358301) ^ 1153398 = 8367128297 := by
        calc
          (18 : ZMod 20078358301) ^ 1153398 = (18 : ZMod 20078358301) ^ (576699 + 576699) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 576699 * (18 : ZMod 20078358301) ^ 576699 := by rw [pow_add]
          _ = 8367128297 := by rw [factor_6_19]; decide
      have factor_6_21 : (18 : ZMod 20078358301) ^ 2306796 = 12350243824 := by
        calc
          (18 : ZMod 20078358301) ^ 2306796 = (18 : ZMod 20078358301) ^ (1153398 + 1153398) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 1153398 * (18 : ZMod 20078358301) ^ 1153398 := by rw [pow_add]
          _ = 12350243824 := by rw [factor_6_20]; decide
      have factor_6_22 : (18 : ZMod 20078358301) ^ 4613593 = 9783499156 := by
        calc
          (18 : ZMod 20078358301) ^ 4613593 = (18 : ZMod 20078358301) ^ (2306796 + 2306796 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 2306796 * (18 : ZMod 20078358301) ^ 2306796) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 9783499156 := by rw [factor_6_21]; decide
      have factor_6_23 : (18 : ZMod 20078358301) ^ 9227186 = 11223469799 := by
        calc
          (18 : ZMod 20078358301) ^ 9227186 = (18 : ZMod 20078358301) ^ (4613593 + 4613593) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 4613593 * (18 : ZMod 20078358301) ^ 4613593 := by rw [pow_add]
          _ = 11223469799 := by rw [factor_6_22]; decide
      have factor_6_24 : (18 : ZMod 20078358301) ^ 18454373 = 11987630829 := by
        calc
          (18 : ZMod 20078358301) ^ 18454373 = (18 : ZMod 20078358301) ^ (9227186 + 9227186 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 9227186 * (18 : ZMod 20078358301) ^ 9227186) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 11987630829 := by rw [factor_6_23]; decide
      have factor_6_25 : (18 : ZMod 20078358301) ^ 36908746 = 3757174999 := by
        calc
          (18 : ZMod 20078358301) ^ 36908746 = (18 : ZMod 20078358301) ^ (18454373 + 18454373) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 18454373 * (18 : ZMod 20078358301) ^ 18454373 := by rw [pow_add]
          _ = 3757174999 := by rw [factor_6_24]; decide
      have factor_6_26 : (18 : ZMod 20078358301) ^ 73817493 = 13058355529 := by
        calc
          (18 : ZMod 20078358301) ^ 73817493 = (18 : ZMod 20078358301) ^ (36908746 + 36908746 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 36908746 * (18 : ZMod 20078358301) ^ 36908746) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 13058355529 := by rw [factor_6_25]; decide
      have factor_6_27 : (18 : ZMod 20078358301) ^ 147634987 = 18410857947 := by
        calc
          (18 : ZMod 20078358301) ^ 147634987 = (18 : ZMod 20078358301) ^ (73817493 + 73817493 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 73817493 * (18 : ZMod 20078358301) ^ 73817493) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 18410857947 := by rw [factor_6_26]; decide
      have factor_6_28 : (18 : ZMod 20078358301) ^ 295269975 = 2813315726 := by
        calc
          (18 : ZMod 20078358301) ^ 295269975 = (18 : ZMod 20078358301) ^ (147634987 + 147634987 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 147634987 * (18 : ZMod 20078358301) ^ 147634987) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 2813315726 := by rw [factor_6_27]; decide
      have factor_6_29 : (18 : ZMod 20078358301) ^ 590539950 = 11853126022 := by
        calc
          (18 : ZMod 20078358301) ^ 590539950 = (18 : ZMod 20078358301) ^ (295269975 + 295269975) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 295269975 * (18 : ZMod 20078358301) ^ 295269975 := by rw [pow_add]
          _ = 11853126022 := by rw [factor_6_28]; decide
      have factor_6_30 : (18 : ZMod 20078358301) ^ 1181079900 = 18039581536 := by
        calc
          (18 : ZMod 20078358301) ^ 1181079900 = (18 : ZMod 20078358301) ^ (590539950 + 590539950) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 590539950 * (18 : ZMod 20078358301) ^ 590539950 := by rw [pow_add]
          _ = 18039581536 := by rw [factor_6_29]; decide
      change (18 : ZMod 20078358301) ^ 1181079900 ≠ 1
      rw [factor_6_30]
      decide
    ·
      have factor_7_0 : (18 : ZMod 20078358301) ^ 1 = 18 := by norm_num
      have factor_7_1 : (18 : ZMod 20078358301) ^ 3 = 5832 := by
        calc
          (18 : ZMod 20078358301) ^ 3 = (18 : ZMod 20078358301) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 1 * (18 : ZMod 20078358301) ^ 1) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 5832 := by rw [factor_7_0]; decide
      have factor_7_2 : (18 : ZMod 20078358301) ^ 7 = 612220032 := by
        calc
          (18 : ZMod 20078358301) ^ 7 = (18 : ZMod 20078358301) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 3 * (18 : ZMod 20078358301) ^ 3) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 612220032 := by rw [factor_7_1]; decide
      have factor_7_3 : (18 : ZMod 20078358301) ^ 15 = 8869877882 := by
        calc
          (18 : ZMod 20078358301) ^ 15 = (18 : ZMod 20078358301) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 7 * (18 : ZMod 20078358301) ^ 7) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 8869877882 := by rw [factor_7_2]; decide
      have factor_7_4 : (18 : ZMod 20078358301) ^ 31 = 11517950532 := by
        calc
          (18 : ZMod 20078358301) ^ 31 = (18 : ZMod 20078358301) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 15 * (18 : ZMod 20078358301) ^ 15) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 11517950532 := by rw [factor_7_3]; decide
      have factor_7_5 : (18 : ZMod 20078358301) ^ 62 = 11038643534 := by
        calc
          (18 : ZMod 20078358301) ^ 62 = (18 : ZMod 20078358301) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 31 * (18 : ZMod 20078358301) ^ 31 := by rw [pow_add]
          _ = 11038643534 := by rw [factor_7_4]; decide
      have factor_7_6 : (18 : ZMod 20078358301) ^ 125 = 2809834503 := by
        calc
          (18 : ZMod 20078358301) ^ 125 = (18 : ZMod 20078358301) ^ (62 + 62 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 62 * (18 : ZMod 20078358301) ^ 62) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 2809834503 := by rw [factor_7_5]; decide
      have factor_7_7 : (18 : ZMod 20078358301) ^ 251 = 14993395320 := by
        calc
          (18 : ZMod 20078358301) ^ 251 = (18 : ZMod 20078358301) ^ (125 + 125 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 125 * (18 : ZMod 20078358301) ^ 125) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 14993395320 := by rw [factor_7_6]; decide
      have factor_7_8 : (18 : ZMod 20078358301) ^ 503 = 12364062555 := by
        calc
          (18 : ZMod 20078358301) ^ 503 = (18 : ZMod 20078358301) ^ (251 + 251 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 251 * (18 : ZMod 20078358301) ^ 251) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 12364062555 := by rw [factor_7_7]; decide
      have factor_7_9 : (18 : ZMod 20078358301) ^ 1007 = 15565695365 := by
        calc
          (18 : ZMod 20078358301) ^ 1007 = (18 : ZMod 20078358301) ^ (503 + 503 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 503 * (18 : ZMod 20078358301) ^ 503) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 15565695365 := by rw [factor_7_8]; decide
      have factor_7_10 : (18 : ZMod 20078358301) ^ 2015 = 4250688925 := by
        calc
          (18 : ZMod 20078358301) ^ 2015 = (18 : ZMod 20078358301) ^ (1007 + 1007 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 1007 * (18 : ZMod 20078358301) ^ 1007) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 4250688925 := by rw [factor_7_9]; decide
      have factor_7_11 : (18 : ZMod 20078358301) ^ 4031 = 16921171063 := by
        calc
          (18 : ZMod 20078358301) ^ 4031 = (18 : ZMod 20078358301) ^ (2015 + 2015 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 2015 * (18 : ZMod 20078358301) ^ 2015) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 16921171063 := by rw [factor_7_10]; decide
      have factor_7_12 : (18 : ZMod 20078358301) ^ 8062 = 9396998017 := by
        calc
          (18 : ZMod 20078358301) ^ 8062 = (18 : ZMod 20078358301) ^ (4031 + 4031) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 4031 * (18 : ZMod 20078358301) ^ 4031 := by rw [pow_add]
          _ = 9396998017 := by rw [factor_7_11]; decide
      have factor_7_13 : (18 : ZMod 20078358301) ^ 16124 = 14007244489 := by
        calc
          (18 : ZMod 20078358301) ^ 16124 = (18 : ZMod 20078358301) ^ (8062 + 8062) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 8062 * (18 : ZMod 20078358301) ^ 8062 := by rw [pow_add]
          _ = 14007244489 := by rw [factor_7_12]; decide
      have factor_7_14 : (18 : ZMod 20078358301) ^ 32249 = 7529471605 := by
        calc
          (18 : ZMod 20078358301) ^ 32249 = (18 : ZMod 20078358301) ^ (16124 + 16124 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 16124 * (18 : ZMod 20078358301) ^ 16124) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 7529471605 := by rw [factor_7_13]; decide
      have factor_7_15 : (18 : ZMod 20078358301) ^ 64499 = 18413587026 := by
        calc
          (18 : ZMod 20078358301) ^ 64499 = (18 : ZMod 20078358301) ^ (32249 + 32249 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 32249 * (18 : ZMod 20078358301) ^ 32249) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 18413587026 := by rw [factor_7_14]; decide
      have factor_7_16 : (18 : ZMod 20078358301) ^ 128998 = 16068922255 := by
        calc
          (18 : ZMod 20078358301) ^ 128998 = (18 : ZMod 20078358301) ^ (64499 + 64499) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 64499 * (18 : ZMod 20078358301) ^ 64499 := by rw [pow_add]
          _ = 16068922255 := by rw [factor_7_15]; decide
      have factor_7_17 : (18 : ZMod 20078358301) ^ 257996 = 18410989494 := by
        calc
          (18 : ZMod 20078358301) ^ 257996 = (18 : ZMod 20078358301) ^ (128998 + 128998) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 128998 * (18 : ZMod 20078358301) ^ 128998 := by rw [pow_add]
          _ = 18410989494 := by rw [factor_7_16]; decide
      have factor_7_18 : (18 : ZMod 20078358301) ^ 515993 = 3119252402 := by
        calc
          (18 : ZMod 20078358301) ^ 515993 = (18 : ZMod 20078358301) ^ (257996 + 257996 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 257996 * (18 : ZMod 20078358301) ^ 257996) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 3119252402 := by rw [factor_7_17]; decide
      have factor_7_19 : (18 : ZMod 20078358301) ^ 1031987 = 5487644737 := by
        calc
          (18 : ZMod 20078358301) ^ 1031987 = (18 : ZMod 20078358301) ^ (515993 + 515993 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 515993 * (18 : ZMod 20078358301) ^ 515993) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 5487644737 := by rw [factor_7_18]; decide
      have factor_7_20 : (18 : ZMod 20078358301) ^ 2063975 = 7006058300 := by
        calc
          (18 : ZMod 20078358301) ^ 2063975 = (18 : ZMod 20078358301) ^ (1031987 + 1031987 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 1031987 * (18 : ZMod 20078358301) ^ 1031987) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 7006058300 := by rw [factor_7_19]; decide
      have factor_7_21 : (18 : ZMod 20078358301) ^ 4127951 = 11779350180 := by
        calc
          (18 : ZMod 20078358301) ^ 4127951 = (18 : ZMod 20078358301) ^ (2063975 + 2063975 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 2063975 * (18 : ZMod 20078358301) ^ 2063975) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 11779350180 := by rw [factor_7_20]; decide
      have factor_7_22 : (18 : ZMod 20078358301) ^ 8255903 = 3919409643 := by
        calc
          (18 : ZMod 20078358301) ^ 8255903 = (18 : ZMod 20078358301) ^ (4127951 + 4127951 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 4127951 * (18 : ZMod 20078358301) ^ 4127951) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 3919409643 := by rw [factor_7_21]; decide
      have factor_7_23 : (18 : ZMod 20078358301) ^ 16511807 = 7415190238 := by
        calc
          (18 : ZMod 20078358301) ^ 16511807 = (18 : ZMod 20078358301) ^ (8255903 + 8255903 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 8255903 * (18 : ZMod 20078358301) ^ 8255903) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 7415190238 := by rw [factor_7_22]; decide
      have factor_7_24 : (18 : ZMod 20078358301) ^ 33023615 = 13675274663 := by
        calc
          (18 : ZMod 20078358301) ^ 33023615 = (18 : ZMod 20078358301) ^ (16511807 + 16511807 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 16511807 * (18 : ZMod 20078358301) ^ 16511807) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 13675274663 := by rw [factor_7_23]; decide
      have factor_7_25 : (18 : ZMod 20078358301) ^ 66047231 = 3197503257 := by
        calc
          (18 : ZMod 20078358301) ^ 66047231 = (18 : ZMod 20078358301) ^ (33023615 + 33023615 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 33023615 * (18 : ZMod 20078358301) ^ 33023615) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 3197503257 := by rw [factor_7_24]; decide
      have factor_7_26 : (18 : ZMod 20078358301) ^ 132094462 = 15961795923 := by
        calc
          (18 : ZMod 20078358301) ^ 132094462 = (18 : ZMod 20078358301) ^ (66047231 + 66047231) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 66047231 * (18 : ZMod 20078358301) ^ 66047231 := by rw [pow_add]
          _ = 15961795923 := by rw [factor_7_25]; decide
      have factor_7_27 : (18 : ZMod 20078358301) ^ 264188925 = 179292676 := by
        calc
          (18 : ZMod 20078358301) ^ 264188925 = (18 : ZMod 20078358301) ^ (132094462 + 132094462 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 132094462 * (18 : ZMod 20078358301) ^ 132094462) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 179292676 := by rw [factor_7_26]; decide
      have factor_7_28 : (18 : ZMod 20078358301) ^ 528377850 = 10460173956 := by
        calc
          (18 : ZMod 20078358301) ^ 528377850 = (18 : ZMod 20078358301) ^ (264188925 + 264188925) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 264188925 * (18 : ZMod 20078358301) ^ 264188925 := by rw [pow_add]
          _ = 10460173956 := by rw [factor_7_27]; decide
      have factor_7_29 : (18 : ZMod 20078358301) ^ 1056755700 = 13239324209 := by
        calc
          (18 : ZMod 20078358301) ^ 1056755700 = (18 : ZMod 20078358301) ^ (528377850 + 528377850) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 528377850 * (18 : ZMod 20078358301) ^ 528377850 := by rw [pow_add]
          _ = 13239324209 := by rw [factor_7_28]; decide
      change (18 : ZMod 20078358301) ^ 1056755700 ≠ 1
      rw [factor_7_29]
      decide
    ·
      have factor_8_0 : (18 : ZMod 20078358301) ^ 1 = 18 := by norm_num
      have factor_8_1 : (18 : ZMod 20078358301) ^ 3 = 5832 := by
        calc
          (18 : ZMod 20078358301) ^ 3 = (18 : ZMod 20078358301) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 1 * (18 : ZMod 20078358301) ^ 1) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 5832 := by rw [factor_8_0]; decide
      have factor_8_2 : (18 : ZMod 20078358301) ^ 6 = 34012224 := by
        calc
          (18 : ZMod 20078358301) ^ 6 = (18 : ZMod 20078358301) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 3 * (18 : ZMod 20078358301) ^ 3 := by rw [pow_add]
          _ = 34012224 := by rw [factor_8_1]; decide
      have factor_8_3 : (18 : ZMod 20078358301) ^ 13 = 647078583 := by
        calc
          (18 : ZMod 20078358301) ^ 13 = (18 : ZMod 20078358301) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 6 * (18 : ZMod 20078358301) ^ 6) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 647078583 := by rw [factor_8_2]; decide
      have factor_8_4 : (18 : ZMod 20078358301) ^ 26 = 1810786758 := by
        calc
          (18 : ZMod 20078358301) ^ 26 = (18 : ZMod 20078358301) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 13 * (18 : ZMod 20078358301) ^ 13 := by rw [pow_add]
          _ = 1810786758 := by rw [factor_8_3]; decide
      have factor_8_5 : (18 : ZMod 20078358301) ^ 52 = 16244896556 := by
        calc
          (18 : ZMod 20078358301) ^ 52 = (18 : ZMod 20078358301) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 26 * (18 : ZMod 20078358301) ^ 26 := by rw [pow_add]
          _ = 16244896556 := by rw [factor_8_4]; decide
      have factor_8_6 : (18 : ZMod 20078358301) ^ 104 = 3495588115 := by
        calc
          (18 : ZMod 20078358301) ^ 104 = (18 : ZMod 20078358301) ^ (52 + 52) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 52 * (18 : ZMod 20078358301) ^ 52 := by rw [pow_add]
          _ = 3495588115 := by rw [factor_8_5]; decide
      have factor_8_7 : (18 : ZMod 20078358301) ^ 208 = 4317813347 := by
        calc
          (18 : ZMod 20078358301) ^ 208 = (18 : ZMod 20078358301) ^ (104 + 104) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 104 * (18 : ZMod 20078358301) ^ 104 := by rw [pow_add]
          _ = 4317813347 := by rw [factor_8_6]; decide
      have factor_8_8 : (18 : ZMod 20078358301) ^ 416 = 5060568836 := by
        calc
          (18 : ZMod 20078358301) ^ 416 = (18 : ZMod 20078358301) ^ (208 + 208) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 208 * (18 : ZMod 20078358301) ^ 208 := by rw [pow_add]
          _ = 5060568836 := by rw [factor_8_7]; decide
      have factor_8_9 : (18 : ZMod 20078358301) ^ 832 = 9923087935 := by
        calc
          (18 : ZMod 20078358301) ^ 832 = (18 : ZMod 20078358301) ^ (416 + 416) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 416 * (18 : ZMod 20078358301) ^ 416 := by rw [pow_add]
          _ = 9923087935 := by rw [factor_8_8]; decide
      have factor_8_10 : (18 : ZMod 20078358301) ^ 1665 = 1571389858 := by
        calc
          (18 : ZMod 20078358301) ^ 1665 = (18 : ZMod 20078358301) ^ (832 + 832 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 832 * (18 : ZMod 20078358301) ^ 832) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 1571389858 := by rw [factor_8_9]; decide
      have factor_8_11 : (18 : ZMod 20078358301) ^ 3330 = 6546502791 := by
        calc
          (18 : ZMod 20078358301) ^ 3330 = (18 : ZMod 20078358301) ^ (1665 + 1665) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 1665 * (18 : ZMod 20078358301) ^ 1665 := by rw [pow_add]
          _ = 6546502791 := by rw [factor_8_10]; decide
      have factor_8_12 : (18 : ZMod 20078358301) ^ 6660 = 12902276023 := by
        calc
          (18 : ZMod 20078358301) ^ 6660 = (18 : ZMod 20078358301) ^ (3330 + 3330) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 3330 * (18 : ZMod 20078358301) ^ 3330 := by rw [pow_add]
          _ = 12902276023 := by rw [factor_8_11]; decide
      have factor_8_13 : (18 : ZMod 20078358301) ^ 13320 = 16817896051 := by
        calc
          (18 : ZMod 20078358301) ^ 13320 = (18 : ZMod 20078358301) ^ (6660 + 6660) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 6660 * (18 : ZMod 20078358301) ^ 6660 := by rw [pow_add]
          _ = 16817896051 := by rw [factor_8_12]; decide
      have factor_8_14 : (18 : ZMod 20078358301) ^ 26640 = 4497342461 := by
        calc
          (18 : ZMod 20078358301) ^ 26640 = (18 : ZMod 20078358301) ^ (13320 + 13320) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 13320 * (18 : ZMod 20078358301) ^ 13320 := by rw [pow_add]
          _ = 4497342461 := by rw [factor_8_13]; decide
      have factor_8_15 : (18 : ZMod 20078358301) ^ 53281 = 19389166244 := by
        calc
          (18 : ZMod 20078358301) ^ 53281 = (18 : ZMod 20078358301) ^ (26640 + 26640 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 26640 * (18 : ZMod 20078358301) ^ 26640) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 19389166244 := by rw [factor_8_14]; decide
      have factor_8_16 : (18 : ZMod 20078358301) ^ 106563 = 8072183682 := by
        calc
          (18 : ZMod 20078358301) ^ 106563 = (18 : ZMod 20078358301) ^ (53281 + 53281 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 53281 * (18 : ZMod 20078358301) ^ 53281) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 8072183682 := by rw [factor_8_15]; decide
      have factor_8_17 : (18 : ZMod 20078358301) ^ 213127 = 2999474735 := by
        calc
          (18 : ZMod 20078358301) ^ 213127 = (18 : ZMod 20078358301) ^ (106563 + 106563 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 106563 * (18 : ZMod 20078358301) ^ 106563) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 2999474735 := by rw [factor_8_16]; decide
      have factor_8_18 : (18 : ZMod 20078358301) ^ 426255 = 4075721226 := by
        calc
          (18 : ZMod 20078358301) ^ 426255 = (18 : ZMod 20078358301) ^ (213127 + 213127 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 213127 * (18 : ZMod 20078358301) ^ 213127) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 4075721226 := by rw [factor_8_17]; decide
      have factor_8_19 : (18 : ZMod 20078358301) ^ 852511 = 7891385828 := by
        calc
          (18 : ZMod 20078358301) ^ 852511 = (18 : ZMod 20078358301) ^ (426255 + 426255 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 426255 * (18 : ZMod 20078358301) ^ 426255) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 7891385828 := by rw [factor_8_18]; decide
      have factor_8_20 : (18 : ZMod 20078358301) ^ 1705023 = 10562434507 := by
        calc
          (18 : ZMod 20078358301) ^ 1705023 = (18 : ZMod 20078358301) ^ (852511 + 852511 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 852511 * (18 : ZMod 20078358301) ^ 852511) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 10562434507 := by rw [factor_8_19]; decide
      have factor_8_21 : (18 : ZMod 20078358301) ^ 3410047 = 8577177931 := by
        calc
          (18 : ZMod 20078358301) ^ 3410047 = (18 : ZMod 20078358301) ^ (1705023 + 1705023 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 1705023 * (18 : ZMod 20078358301) ^ 1705023) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 8577177931 := by rw [factor_8_20]; decide
      have factor_8_22 : (18 : ZMod 20078358301) ^ 6820094 = 4751243810 := by
        calc
          (18 : ZMod 20078358301) ^ 6820094 = (18 : ZMod 20078358301) ^ (3410047 + 3410047) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 3410047 * (18 : ZMod 20078358301) ^ 3410047 := by rw [pow_add]
          _ = 4751243810 := by rw [factor_8_21]; decide
      have factor_8_23 : (18 : ZMod 20078358301) ^ 13640189 = 16979102418 := by
        calc
          (18 : ZMod 20078358301) ^ 13640189 = (18 : ZMod 20078358301) ^ (6820094 + 6820094 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 6820094 * (18 : ZMod 20078358301) ^ 6820094) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 16979102418 := by rw [factor_8_22]; decide
      have factor_8_24 : (18 : ZMod 20078358301) ^ 27280378 = 5768882649 := by
        calc
          (18 : ZMod 20078358301) ^ 27280378 = (18 : ZMod 20078358301) ^ (13640189 + 13640189) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 13640189 * (18 : ZMod 20078358301) ^ 13640189 := by rw [pow_add]
          _ = 5768882649 := by rw [factor_8_23]; decide
      have factor_8_25 : (18 : ZMod 20078358301) ^ 54560756 = 14021438520 := by
        calc
          (18 : ZMod 20078358301) ^ 54560756 = (18 : ZMod 20078358301) ^ (27280378 + 27280378) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 27280378 * (18 : ZMod 20078358301) ^ 27280378 := by rw [pow_add]
          _ = 14021438520 := by rw [factor_8_24]; decide
      have factor_8_26 : (18 : ZMod 20078358301) ^ 109121512 = 14609890139 := by
        calc
          (18 : ZMod 20078358301) ^ 109121512 = (18 : ZMod 20078358301) ^ (54560756 + 54560756) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 54560756 * (18 : ZMod 20078358301) ^ 54560756 := by rw [pow_add]
          _ = 14609890139 := by rw [factor_8_25]; decide
      have factor_8_27 : (18 : ZMod 20078358301) ^ 218243025 = 11597926049 := by
        calc
          (18 : ZMod 20078358301) ^ 218243025 = (18 : ZMod 20078358301) ^ (109121512 + 109121512 + 1) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = ((18 : ZMod 20078358301) ^ 109121512 * (18 : ZMod 20078358301) ^ 109121512) * (18 : ZMod 20078358301) := by rw [pow_succ, pow_add]
          _ = 11597926049 := by rw [factor_8_26]; decide
      have factor_8_28 : (18 : ZMod 20078358301) ^ 436486050 = 12555993742 := by
        calc
          (18 : ZMod 20078358301) ^ 436486050 = (18 : ZMod 20078358301) ^ (218243025 + 218243025) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 218243025 * (18 : ZMod 20078358301) ^ 218243025 := by rw [pow_add]
          _ = 12555993742 := by rw [factor_8_27]; decide
      have factor_8_29 : (18 : ZMod 20078358301) ^ 872972100 = 8806140644 := by
        calc
          (18 : ZMod 20078358301) ^ 872972100 = (18 : ZMod 20078358301) ^ (436486050 + 436486050) :=
            congrArg (fun n : ℕ => (18 : ZMod 20078358301) ^ n) (by norm_num)
          _ = (18 : ZMod 20078358301) ^ 436486050 * (18 : ZMod 20078358301) ^ 436486050 := by rw [pow_add]
          _ = 8806140644 := by rw [factor_8_28]; decide
      change (18 : ZMod 20078358301) ^ 872972100 ≠ 1
      rw [factor_8_29]
      decide

#print axioms prime_lucas_20078358301

end TotientTailPeriodKiller
end Erdos249257
