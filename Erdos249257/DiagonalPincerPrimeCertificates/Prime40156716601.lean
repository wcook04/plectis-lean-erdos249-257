import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=27 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_40156716601 : Nat.Prime 40156716601 := by
  apply lucas_primality 40156716601 (47 : ZMod 40156716601)
  ·
      have fermat_0 : (47 : ZMod 40156716601) ^ 1 = 47 := by norm_num
      have fermat_1 : (47 : ZMod 40156716601) ^ 2 = 2209 := by
        calc
          (47 : ZMod 40156716601) ^ 2 = (47 : ZMod 40156716601) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 1 * (47 : ZMod 40156716601) ^ 1 := by rw [pow_add]
          _ = 2209 := by rw [fermat_0]; decide
      have fermat_2 : (47 : ZMod 40156716601) ^ 4 = 4879681 := by
        calc
          (47 : ZMod 40156716601) ^ 4 = (47 : ZMod 40156716601) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 2 * (47 : ZMod 40156716601) ^ 2 := by rw [pow_add]
          _ = 4879681 := by rw [fermat_1]; decide
      have fermat_3 : (47 : ZMod 40156716601) ^ 9 = 2938149498 := by
        calc
          (47 : ZMod 40156716601) ^ 9 = (47 : ZMod 40156716601) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 4 * (47 : ZMod 40156716601) ^ 4) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 2938149498 := by rw [fermat_2]; decide
      have fermat_4 : (47 : ZMod 40156716601) ^ 18 = 35297529800 := by
        calc
          (47 : ZMod 40156716601) ^ 18 = (47 : ZMod 40156716601) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 9 * (47 : ZMod 40156716601) ^ 9 := by rw [pow_add]
          _ = 35297529800 := by rw [fermat_3]; decide
      have fermat_5 : (47 : ZMod 40156716601) ^ 37 = 34244956639 := by
        calc
          (47 : ZMod 40156716601) ^ 37 = (47 : ZMod 40156716601) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 18 * (47 : ZMod 40156716601) ^ 18) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 34244956639 := by rw [fermat_4]; decide
      have fermat_6 : (47 : ZMod 40156716601) ^ 74 = 19155084210 := by
        calc
          (47 : ZMod 40156716601) ^ 74 = (47 : ZMod 40156716601) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 37 * (47 : ZMod 40156716601) ^ 37 := by rw [pow_add]
          _ = 19155084210 := by rw [fermat_5]; decide
      have fermat_7 : (47 : ZMod 40156716601) ^ 149 = 32965964226 := by
        calc
          (47 : ZMod 40156716601) ^ 149 = (47 : ZMod 40156716601) ^ (74 + 74 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 74 * (47 : ZMod 40156716601) ^ 74) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 32965964226 := by rw [fermat_6]; decide
      have fermat_8 : (47 : ZMod 40156716601) ^ 299 = 37370717342 := by
        calc
          (47 : ZMod 40156716601) ^ 299 = (47 : ZMod 40156716601) ^ (149 + 149 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 149 * (47 : ZMod 40156716601) ^ 149) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 37370717342 := by rw [fermat_7]; decide
      have fermat_9 : (47 : ZMod 40156716601) ^ 598 = 29252162369 := by
        calc
          (47 : ZMod 40156716601) ^ 598 = (47 : ZMod 40156716601) ^ (299 + 299) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 299 * (47 : ZMod 40156716601) ^ 299 := by rw [pow_add]
          _ = 29252162369 := by rw [fermat_8]; decide
      have fermat_10 : (47 : ZMod 40156716601) ^ 1196 = 35327686310 := by
        calc
          (47 : ZMod 40156716601) ^ 1196 = (47 : ZMod 40156716601) ^ (598 + 598) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 598 * (47 : ZMod 40156716601) ^ 598 := by rw [pow_add]
          _ = 35327686310 := by rw [fermat_9]; decide
      have fermat_11 : (47 : ZMod 40156716601) ^ 2393 = 28156447570 := by
        calc
          (47 : ZMod 40156716601) ^ 2393 = (47 : ZMod 40156716601) ^ (1196 + 1196 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 1196 * (47 : ZMod 40156716601) ^ 1196) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 28156447570 := by rw [fermat_10]; decide
      have fermat_12 : (47 : ZMod 40156716601) ^ 4787 = 22588112945 := by
        calc
          (47 : ZMod 40156716601) ^ 4787 = (47 : ZMod 40156716601) ^ (2393 + 2393 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 2393 * (47 : ZMod 40156716601) ^ 2393) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 22588112945 := by rw [fermat_11]; decide
      have fermat_13 : (47 : ZMod 40156716601) ^ 9574 = 5219295474 := by
        calc
          (47 : ZMod 40156716601) ^ 9574 = (47 : ZMod 40156716601) ^ (4787 + 4787) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 4787 * (47 : ZMod 40156716601) ^ 4787 := by rw [pow_add]
          _ = 5219295474 := by rw [fermat_12]; decide
      have fermat_14 : (47 : ZMod 40156716601) ^ 19148 = 24289355735 := by
        calc
          (47 : ZMod 40156716601) ^ 19148 = (47 : ZMod 40156716601) ^ (9574 + 9574) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 9574 * (47 : ZMod 40156716601) ^ 9574 := by rw [pow_add]
          _ = 24289355735 := by rw [fermat_13]; decide
      have fermat_15 : (47 : ZMod 40156716601) ^ 38296 = 10223547038 := by
        calc
          (47 : ZMod 40156716601) ^ 38296 = (47 : ZMod 40156716601) ^ (19148 + 19148) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 19148 * (47 : ZMod 40156716601) ^ 19148 := by rw [pow_add]
          _ = 10223547038 := by rw [fermat_14]; decide
      have fermat_16 : (47 : ZMod 40156716601) ^ 76592 = 39543995042 := by
        calc
          (47 : ZMod 40156716601) ^ 76592 = (47 : ZMod 40156716601) ^ (38296 + 38296) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 38296 * (47 : ZMod 40156716601) ^ 38296 := by rw [pow_add]
          _ = 39543995042 := by rw [fermat_15]; decide
      have fermat_17 : (47 : ZMod 40156716601) ^ 153185 = 21486913405 := by
        calc
          (47 : ZMod 40156716601) ^ 153185 = (47 : ZMod 40156716601) ^ (76592 + 76592 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 76592 * (47 : ZMod 40156716601) ^ 76592) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 21486913405 := by rw [fermat_16]; decide
      have fermat_18 : (47 : ZMod 40156716601) ^ 306371 = 38545647436 := by
        calc
          (47 : ZMod 40156716601) ^ 306371 = (47 : ZMod 40156716601) ^ (153185 + 153185 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 153185 * (47 : ZMod 40156716601) ^ 153185) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 38545647436 := by rw [fermat_17]; decide
      have fermat_19 : (47 : ZMod 40156716601) ^ 612742 = 20490185865 := by
        calc
          (47 : ZMod 40156716601) ^ 612742 = (47 : ZMod 40156716601) ^ (306371 + 306371) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 306371 * (47 : ZMod 40156716601) ^ 306371 := by rw [pow_add]
          _ = 20490185865 := by rw [fermat_18]; decide
      have fermat_20 : (47 : ZMod 40156716601) ^ 1225485 = 5723773223 := by
        calc
          (47 : ZMod 40156716601) ^ 1225485 = (47 : ZMod 40156716601) ^ (612742 + 612742 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 612742 * (47 : ZMod 40156716601) ^ 612742) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 5723773223 := by rw [fermat_19]; decide
      have fermat_21 : (47 : ZMod 40156716601) ^ 2450971 = 11034965055 := by
        calc
          (47 : ZMod 40156716601) ^ 2450971 = (47 : ZMod 40156716601) ^ (1225485 + 1225485 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 1225485 * (47 : ZMod 40156716601) ^ 1225485) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 11034965055 := by rw [fermat_20]; decide
      have fermat_22 : (47 : ZMod 40156716601) ^ 4901942 = 3500787891 := by
        calc
          (47 : ZMod 40156716601) ^ 4901942 = (47 : ZMod 40156716601) ^ (2450971 + 2450971) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 2450971 * (47 : ZMod 40156716601) ^ 2450971 := by rw [pow_add]
          _ = 3500787891 := by rw [fermat_21]; decide
      have fermat_23 : (47 : ZMod 40156716601) ^ 9803885 = 27917906775 := by
        calc
          (47 : ZMod 40156716601) ^ 9803885 = (47 : ZMod 40156716601) ^ (4901942 + 4901942 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 4901942 * (47 : ZMod 40156716601) ^ 4901942) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 27917906775 := by rw [fermat_22]; decide
      have fermat_24 : (47 : ZMod 40156716601) ^ 19607771 = 35442207900 := by
        calc
          (47 : ZMod 40156716601) ^ 19607771 = (47 : ZMod 40156716601) ^ (9803885 + 9803885 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 9803885 * (47 : ZMod 40156716601) ^ 9803885) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 35442207900 := by rw [fermat_23]; decide
      have fermat_25 : (47 : ZMod 40156716601) ^ 39215543 = 35370309216 := by
        calc
          (47 : ZMod 40156716601) ^ 39215543 = (47 : ZMod 40156716601) ^ (19607771 + 19607771 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 19607771 * (47 : ZMod 40156716601) ^ 19607771) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 35370309216 := by rw [fermat_24]; decide
      have fermat_26 : (47 : ZMod 40156716601) ^ 78431087 = 33835245520 := by
        calc
          (47 : ZMod 40156716601) ^ 78431087 = (47 : ZMod 40156716601) ^ (39215543 + 39215543 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 39215543 * (47 : ZMod 40156716601) ^ 39215543) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 33835245520 := by rw [fermat_25]; decide
      have fermat_27 : (47 : ZMod 40156716601) ^ 156862174 = 8587788865 := by
        calc
          (47 : ZMod 40156716601) ^ 156862174 = (47 : ZMod 40156716601) ^ (78431087 + 78431087) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 78431087 * (47 : ZMod 40156716601) ^ 78431087 := by rw [pow_add]
          _ = 8587788865 := by rw [fermat_26]; decide
      have fermat_28 : (47 : ZMod 40156716601) ^ 313724348 = 26675444962 := by
        calc
          (47 : ZMod 40156716601) ^ 313724348 = (47 : ZMod 40156716601) ^ (156862174 + 156862174) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 156862174 * (47 : ZMod 40156716601) ^ 156862174 := by rw [pow_add]
          _ = 26675444962 := by rw [fermat_27]; decide
      have fermat_29 : (47 : ZMod 40156716601) ^ 627448696 = 36527650630 := by
        calc
          (47 : ZMod 40156716601) ^ 627448696 = (47 : ZMod 40156716601) ^ (313724348 + 313724348) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 313724348 * (47 : ZMod 40156716601) ^ 313724348 := by rw [pow_add]
          _ = 36527650630 := by rw [fermat_28]; decide
      have fermat_30 : (47 : ZMod 40156716601) ^ 1254897393 = 15315230 := by
        calc
          (47 : ZMod 40156716601) ^ 1254897393 = (47 : ZMod 40156716601) ^ (627448696 + 627448696 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 627448696 * (47 : ZMod 40156716601) ^ 627448696) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 15315230 := by rw [fermat_29]; decide
      have fermat_31 : (47 : ZMod 40156716601) ^ 2509794787 = 1592746972 := by
        calc
          (47 : ZMod 40156716601) ^ 2509794787 = (47 : ZMod 40156716601) ^ (1254897393 + 1254897393 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 1254897393 * (47 : ZMod 40156716601) ^ 1254897393) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 1592746972 := by rw [fermat_30]; decide
      have fermat_32 : (47 : ZMod 40156716601) ^ 5019589575 = 15944943328 := by
        calc
          (47 : ZMod 40156716601) ^ 5019589575 = (47 : ZMod 40156716601) ^ (2509794787 + 2509794787 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 2509794787 * (47 : ZMod 40156716601) ^ 2509794787) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 15944943328 := by rw [fermat_31]; decide
      have fermat_33 : (47 : ZMod 40156716601) ^ 10039179150 = 33353506344 := by
        calc
          (47 : ZMod 40156716601) ^ 10039179150 = (47 : ZMod 40156716601) ^ (5019589575 + 5019589575) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 5019589575 * (47 : ZMod 40156716601) ^ 5019589575 := by rw [pow_add]
          _ = 33353506344 := by rw [fermat_32]; decide
      have fermat_34 : (47 : ZMod 40156716601) ^ 20078358300 = 40156716600 := by
        calc
          (47 : ZMod 40156716601) ^ 20078358300 = (47 : ZMod 40156716601) ^ (10039179150 + 10039179150) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 10039179150 * (47 : ZMod 40156716601) ^ 10039179150 := by rw [pow_add]
          _ = 40156716600 := by rw [fermat_33]; decide
      have fermat_35 : (47 : ZMod 40156716601) ^ 40156716600 = 1 := by
        calc
          (47 : ZMod 40156716601) ^ 40156716600 = (47 : ZMod 40156716601) ^ (20078358300 + 20078358300) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 20078358300 * (47 : ZMod 40156716601) ^ 20078358300 := by rw [pow_add]
          _ = 1 := by rw [fermat_34]; decide
      simpa using fermat_35
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 3), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 3), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod = 40156716601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (47 : ZMod 40156716601) ^ 1 = 47 := by norm_num
      have factor_0_1 : (47 : ZMod 40156716601) ^ 2 = 2209 := by
        calc
          (47 : ZMod 40156716601) ^ 2 = (47 : ZMod 40156716601) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 1 * (47 : ZMod 40156716601) ^ 1 := by rw [pow_add]
          _ = 2209 := by rw [factor_0_0]; decide
      have factor_0_2 : (47 : ZMod 40156716601) ^ 4 = 4879681 := by
        calc
          (47 : ZMod 40156716601) ^ 4 = (47 : ZMod 40156716601) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 2 * (47 : ZMod 40156716601) ^ 2 := by rw [pow_add]
          _ = 4879681 := by rw [factor_0_1]; decide
      have factor_0_3 : (47 : ZMod 40156716601) ^ 9 = 2938149498 := by
        calc
          (47 : ZMod 40156716601) ^ 9 = (47 : ZMod 40156716601) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 4 * (47 : ZMod 40156716601) ^ 4) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 2938149498 := by rw [factor_0_2]; decide
      have factor_0_4 : (47 : ZMod 40156716601) ^ 18 = 35297529800 := by
        calc
          (47 : ZMod 40156716601) ^ 18 = (47 : ZMod 40156716601) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 9 * (47 : ZMod 40156716601) ^ 9 := by rw [pow_add]
          _ = 35297529800 := by rw [factor_0_3]; decide
      have factor_0_5 : (47 : ZMod 40156716601) ^ 37 = 34244956639 := by
        calc
          (47 : ZMod 40156716601) ^ 37 = (47 : ZMod 40156716601) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 18 * (47 : ZMod 40156716601) ^ 18) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 34244956639 := by rw [factor_0_4]; decide
      have factor_0_6 : (47 : ZMod 40156716601) ^ 74 = 19155084210 := by
        calc
          (47 : ZMod 40156716601) ^ 74 = (47 : ZMod 40156716601) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 37 * (47 : ZMod 40156716601) ^ 37 := by rw [pow_add]
          _ = 19155084210 := by rw [factor_0_5]; decide
      have factor_0_7 : (47 : ZMod 40156716601) ^ 149 = 32965964226 := by
        calc
          (47 : ZMod 40156716601) ^ 149 = (47 : ZMod 40156716601) ^ (74 + 74 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 74 * (47 : ZMod 40156716601) ^ 74) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 32965964226 := by rw [factor_0_6]; decide
      have factor_0_8 : (47 : ZMod 40156716601) ^ 299 = 37370717342 := by
        calc
          (47 : ZMod 40156716601) ^ 299 = (47 : ZMod 40156716601) ^ (149 + 149 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 149 * (47 : ZMod 40156716601) ^ 149) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 37370717342 := by rw [factor_0_7]; decide
      have factor_0_9 : (47 : ZMod 40156716601) ^ 598 = 29252162369 := by
        calc
          (47 : ZMod 40156716601) ^ 598 = (47 : ZMod 40156716601) ^ (299 + 299) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 299 * (47 : ZMod 40156716601) ^ 299 := by rw [pow_add]
          _ = 29252162369 := by rw [factor_0_8]; decide
      have factor_0_10 : (47 : ZMod 40156716601) ^ 1196 = 35327686310 := by
        calc
          (47 : ZMod 40156716601) ^ 1196 = (47 : ZMod 40156716601) ^ (598 + 598) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 598 * (47 : ZMod 40156716601) ^ 598 := by rw [pow_add]
          _ = 35327686310 := by rw [factor_0_9]; decide
      have factor_0_11 : (47 : ZMod 40156716601) ^ 2393 = 28156447570 := by
        calc
          (47 : ZMod 40156716601) ^ 2393 = (47 : ZMod 40156716601) ^ (1196 + 1196 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 1196 * (47 : ZMod 40156716601) ^ 1196) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 28156447570 := by rw [factor_0_10]; decide
      have factor_0_12 : (47 : ZMod 40156716601) ^ 4787 = 22588112945 := by
        calc
          (47 : ZMod 40156716601) ^ 4787 = (47 : ZMod 40156716601) ^ (2393 + 2393 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 2393 * (47 : ZMod 40156716601) ^ 2393) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 22588112945 := by rw [factor_0_11]; decide
      have factor_0_13 : (47 : ZMod 40156716601) ^ 9574 = 5219295474 := by
        calc
          (47 : ZMod 40156716601) ^ 9574 = (47 : ZMod 40156716601) ^ (4787 + 4787) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 4787 * (47 : ZMod 40156716601) ^ 4787 := by rw [pow_add]
          _ = 5219295474 := by rw [factor_0_12]; decide
      have factor_0_14 : (47 : ZMod 40156716601) ^ 19148 = 24289355735 := by
        calc
          (47 : ZMod 40156716601) ^ 19148 = (47 : ZMod 40156716601) ^ (9574 + 9574) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 9574 * (47 : ZMod 40156716601) ^ 9574 := by rw [pow_add]
          _ = 24289355735 := by rw [factor_0_13]; decide
      have factor_0_15 : (47 : ZMod 40156716601) ^ 38296 = 10223547038 := by
        calc
          (47 : ZMod 40156716601) ^ 38296 = (47 : ZMod 40156716601) ^ (19148 + 19148) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 19148 * (47 : ZMod 40156716601) ^ 19148 := by rw [pow_add]
          _ = 10223547038 := by rw [factor_0_14]; decide
      have factor_0_16 : (47 : ZMod 40156716601) ^ 76592 = 39543995042 := by
        calc
          (47 : ZMod 40156716601) ^ 76592 = (47 : ZMod 40156716601) ^ (38296 + 38296) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 38296 * (47 : ZMod 40156716601) ^ 38296 := by rw [pow_add]
          _ = 39543995042 := by rw [factor_0_15]; decide
      have factor_0_17 : (47 : ZMod 40156716601) ^ 153185 = 21486913405 := by
        calc
          (47 : ZMod 40156716601) ^ 153185 = (47 : ZMod 40156716601) ^ (76592 + 76592 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 76592 * (47 : ZMod 40156716601) ^ 76592) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 21486913405 := by rw [factor_0_16]; decide
      have factor_0_18 : (47 : ZMod 40156716601) ^ 306371 = 38545647436 := by
        calc
          (47 : ZMod 40156716601) ^ 306371 = (47 : ZMod 40156716601) ^ (153185 + 153185 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 153185 * (47 : ZMod 40156716601) ^ 153185) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 38545647436 := by rw [factor_0_17]; decide
      have factor_0_19 : (47 : ZMod 40156716601) ^ 612742 = 20490185865 := by
        calc
          (47 : ZMod 40156716601) ^ 612742 = (47 : ZMod 40156716601) ^ (306371 + 306371) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 306371 * (47 : ZMod 40156716601) ^ 306371 := by rw [pow_add]
          _ = 20490185865 := by rw [factor_0_18]; decide
      have factor_0_20 : (47 : ZMod 40156716601) ^ 1225485 = 5723773223 := by
        calc
          (47 : ZMod 40156716601) ^ 1225485 = (47 : ZMod 40156716601) ^ (612742 + 612742 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 612742 * (47 : ZMod 40156716601) ^ 612742) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 5723773223 := by rw [factor_0_19]; decide
      have factor_0_21 : (47 : ZMod 40156716601) ^ 2450971 = 11034965055 := by
        calc
          (47 : ZMod 40156716601) ^ 2450971 = (47 : ZMod 40156716601) ^ (1225485 + 1225485 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 1225485 * (47 : ZMod 40156716601) ^ 1225485) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 11034965055 := by rw [factor_0_20]; decide
      have factor_0_22 : (47 : ZMod 40156716601) ^ 4901942 = 3500787891 := by
        calc
          (47 : ZMod 40156716601) ^ 4901942 = (47 : ZMod 40156716601) ^ (2450971 + 2450971) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 2450971 * (47 : ZMod 40156716601) ^ 2450971 := by rw [pow_add]
          _ = 3500787891 := by rw [factor_0_21]; decide
      have factor_0_23 : (47 : ZMod 40156716601) ^ 9803885 = 27917906775 := by
        calc
          (47 : ZMod 40156716601) ^ 9803885 = (47 : ZMod 40156716601) ^ (4901942 + 4901942 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 4901942 * (47 : ZMod 40156716601) ^ 4901942) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 27917906775 := by rw [factor_0_22]; decide
      have factor_0_24 : (47 : ZMod 40156716601) ^ 19607771 = 35442207900 := by
        calc
          (47 : ZMod 40156716601) ^ 19607771 = (47 : ZMod 40156716601) ^ (9803885 + 9803885 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 9803885 * (47 : ZMod 40156716601) ^ 9803885) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 35442207900 := by rw [factor_0_23]; decide
      have factor_0_25 : (47 : ZMod 40156716601) ^ 39215543 = 35370309216 := by
        calc
          (47 : ZMod 40156716601) ^ 39215543 = (47 : ZMod 40156716601) ^ (19607771 + 19607771 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 19607771 * (47 : ZMod 40156716601) ^ 19607771) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 35370309216 := by rw [factor_0_24]; decide
      have factor_0_26 : (47 : ZMod 40156716601) ^ 78431087 = 33835245520 := by
        calc
          (47 : ZMod 40156716601) ^ 78431087 = (47 : ZMod 40156716601) ^ (39215543 + 39215543 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 39215543 * (47 : ZMod 40156716601) ^ 39215543) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 33835245520 := by rw [factor_0_25]; decide
      have factor_0_27 : (47 : ZMod 40156716601) ^ 156862174 = 8587788865 := by
        calc
          (47 : ZMod 40156716601) ^ 156862174 = (47 : ZMod 40156716601) ^ (78431087 + 78431087) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 78431087 * (47 : ZMod 40156716601) ^ 78431087 := by rw [pow_add]
          _ = 8587788865 := by rw [factor_0_26]; decide
      have factor_0_28 : (47 : ZMod 40156716601) ^ 313724348 = 26675444962 := by
        calc
          (47 : ZMod 40156716601) ^ 313724348 = (47 : ZMod 40156716601) ^ (156862174 + 156862174) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 156862174 * (47 : ZMod 40156716601) ^ 156862174 := by rw [pow_add]
          _ = 26675444962 := by rw [factor_0_27]; decide
      have factor_0_29 : (47 : ZMod 40156716601) ^ 627448696 = 36527650630 := by
        calc
          (47 : ZMod 40156716601) ^ 627448696 = (47 : ZMod 40156716601) ^ (313724348 + 313724348) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 313724348 * (47 : ZMod 40156716601) ^ 313724348 := by rw [pow_add]
          _ = 36527650630 := by rw [factor_0_28]; decide
      have factor_0_30 : (47 : ZMod 40156716601) ^ 1254897393 = 15315230 := by
        calc
          (47 : ZMod 40156716601) ^ 1254897393 = (47 : ZMod 40156716601) ^ (627448696 + 627448696 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 627448696 * (47 : ZMod 40156716601) ^ 627448696) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 15315230 := by rw [factor_0_29]; decide
      have factor_0_31 : (47 : ZMod 40156716601) ^ 2509794787 = 1592746972 := by
        calc
          (47 : ZMod 40156716601) ^ 2509794787 = (47 : ZMod 40156716601) ^ (1254897393 + 1254897393 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 1254897393 * (47 : ZMod 40156716601) ^ 1254897393) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 1592746972 := by rw [factor_0_30]; decide
      have factor_0_32 : (47 : ZMod 40156716601) ^ 5019589575 = 15944943328 := by
        calc
          (47 : ZMod 40156716601) ^ 5019589575 = (47 : ZMod 40156716601) ^ (2509794787 + 2509794787 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 2509794787 * (47 : ZMod 40156716601) ^ 2509794787) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 15944943328 := by rw [factor_0_31]; decide
      have factor_0_33 : (47 : ZMod 40156716601) ^ 10039179150 = 33353506344 := by
        calc
          (47 : ZMod 40156716601) ^ 10039179150 = (47 : ZMod 40156716601) ^ (5019589575 + 5019589575) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 5019589575 * (47 : ZMod 40156716601) ^ 5019589575 := by rw [pow_add]
          _ = 33353506344 := by rw [factor_0_32]; decide
      have factor_0_34 : (47 : ZMod 40156716601) ^ 20078358300 = 40156716600 := by
        calc
          (47 : ZMod 40156716601) ^ 20078358300 = (47 : ZMod 40156716601) ^ (10039179150 + 10039179150) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 10039179150 * (47 : ZMod 40156716601) ^ 10039179150 := by rw [pow_add]
          _ = 40156716600 := by rw [factor_0_33]; decide
      change (47 : ZMod 40156716601) ^ 20078358300 ≠ 1
      rw [factor_0_34]
      decide
    ·
      have factor_1_0 : (47 : ZMod 40156716601) ^ 1 = 47 := by norm_num
      have factor_1_1 : (47 : ZMod 40156716601) ^ 3 = 103823 := by
        calc
          (47 : ZMod 40156716601) ^ 3 = (47 : ZMod 40156716601) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 1 * (47 : ZMod 40156716601) ^ 1) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 103823 := by rw [factor_1_0]; decide
      have factor_1_2 : (47 : ZMod 40156716601) ^ 6 = 10779215329 := by
        calc
          (47 : ZMod 40156716601) ^ 6 = (47 : ZMod 40156716601) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 3 * (47 : ZMod 40156716601) ^ 3 := by rw [pow_add]
          _ = 10779215329 := by rw [factor_1_1]; decide
      have factor_1_3 : (47 : ZMod 40156716601) ^ 12 = 17076029658 := by
        calc
          (47 : ZMod 40156716601) ^ 12 = (47 : ZMod 40156716601) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 6 * (47 : ZMod 40156716601) ^ 6 := by rw [pow_add]
          _ = 17076029658 := by rw [factor_1_2]; decide
      have factor_1_4 : (47 : ZMod 40156716601) ^ 24 = 15714725479 := by
        calc
          (47 : ZMod 40156716601) ^ 24 = (47 : ZMod 40156716601) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 12 * (47 : ZMod 40156716601) ^ 12 := by rw [pow_add]
          _ = 15714725479 := by rw [factor_1_3]; decide
      have factor_1_5 : (47 : ZMod 40156716601) ^ 49 = 32221997726 := by
        calc
          (47 : ZMod 40156716601) ^ 49 = (47 : ZMod 40156716601) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 24 * (47 : ZMod 40156716601) ^ 24) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 32221997726 := by rw [factor_1_4]; decide
      have factor_1_6 : (47 : ZMod 40156716601) ^ 99 = 32650133415 := by
        calc
          (47 : ZMod 40156716601) ^ 99 = (47 : ZMod 40156716601) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 49 * (47 : ZMod 40156716601) ^ 49) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 32650133415 := by rw [factor_1_5]; decide
      have factor_1_7 : (47 : ZMod 40156716601) ^ 199 = 3967123764 := by
        calc
          (47 : ZMod 40156716601) ^ 199 = (47 : ZMod 40156716601) ^ (99 + 99 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 99 * (47 : ZMod 40156716601) ^ 99) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 3967123764 := by rw [factor_1_6]; decide
      have factor_1_8 : (47 : ZMod 40156716601) ^ 398 = 11772080017 := by
        calc
          (47 : ZMod 40156716601) ^ 398 = (47 : ZMod 40156716601) ^ (199 + 199) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 199 * (47 : ZMod 40156716601) ^ 199 := by rw [pow_add]
          _ = 11772080017 := by rw [factor_1_7]; decide
      have factor_1_9 : (47 : ZMod 40156716601) ^ 797 = 14994069997 := by
        calc
          (47 : ZMod 40156716601) ^ 797 = (47 : ZMod 40156716601) ^ (398 + 398 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 398 * (47 : ZMod 40156716601) ^ 398) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 14994069997 := by rw [factor_1_8]; decide
      have factor_1_10 : (47 : ZMod 40156716601) ^ 1595 = 384534346 := by
        calc
          (47 : ZMod 40156716601) ^ 1595 = (47 : ZMod 40156716601) ^ (797 + 797 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 797 * (47 : ZMod 40156716601) ^ 797) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 384534346 := by rw [factor_1_9]; decide
      have factor_1_11 : (47 : ZMod 40156716601) ^ 3191 = 11429028978 := by
        calc
          (47 : ZMod 40156716601) ^ 3191 = (47 : ZMod 40156716601) ^ (1595 + 1595 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 1595 * (47 : ZMod 40156716601) ^ 1595) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 11429028978 := by rw [factor_1_10]; decide
      have factor_1_12 : (47 : ZMod 40156716601) ^ 6382 = 8890837785 := by
        calc
          (47 : ZMod 40156716601) ^ 6382 = (47 : ZMod 40156716601) ^ (3191 + 3191) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 3191 * (47 : ZMod 40156716601) ^ 3191 := by rw [pow_add]
          _ = 8890837785 := by rw [factor_1_11]; decide
      have factor_1_13 : (47 : ZMod 40156716601) ^ 12765 = 30743614926 := by
        calc
          (47 : ZMod 40156716601) ^ 12765 = (47 : ZMod 40156716601) ^ (6382 + 6382 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 6382 * (47 : ZMod 40156716601) ^ 6382) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 30743614926 := by rw [factor_1_12]; decide
      have factor_1_14 : (47 : ZMod 40156716601) ^ 25530 = 39069213894 := by
        calc
          (47 : ZMod 40156716601) ^ 25530 = (47 : ZMod 40156716601) ^ (12765 + 12765) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 12765 * (47 : ZMod 40156716601) ^ 12765 := by rw [pow_add]
          _ = 39069213894 := by rw [factor_1_13]; decide
      have factor_1_15 : (47 : ZMod 40156716601) ^ 51061 = 39881491689 := by
        calc
          (47 : ZMod 40156716601) ^ 51061 = (47 : ZMod 40156716601) ^ (25530 + 25530 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 25530 * (47 : ZMod 40156716601) ^ 25530) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 39881491689 := by rw [factor_1_14]; decide
      have factor_1_16 : (47 : ZMod 40156716601) ^ 102123 = 21474451937 := by
        calc
          (47 : ZMod 40156716601) ^ 102123 = (47 : ZMod 40156716601) ^ (51061 + 51061 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 51061 * (47 : ZMod 40156716601) ^ 51061) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 21474451937 := by rw [factor_1_15]; decide
      have factor_1_17 : (47 : ZMod 40156716601) ^ 204247 = 27435414031 := by
        calc
          (47 : ZMod 40156716601) ^ 204247 = (47 : ZMod 40156716601) ^ (102123 + 102123 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 102123 * (47 : ZMod 40156716601) ^ 102123) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 27435414031 := by rw [factor_1_16]; decide
      have factor_1_18 : (47 : ZMod 40156716601) ^ 408495 = 13702398237 := by
        calc
          (47 : ZMod 40156716601) ^ 408495 = (47 : ZMod 40156716601) ^ (204247 + 204247 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 204247 * (47 : ZMod 40156716601) ^ 204247) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 13702398237 := by rw [factor_1_17]; decide
      have factor_1_19 : (47 : ZMod 40156716601) ^ 816990 = 32635162537 := by
        calc
          (47 : ZMod 40156716601) ^ 816990 = (47 : ZMod 40156716601) ^ (408495 + 408495) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 408495 * (47 : ZMod 40156716601) ^ 408495 := by rw [pow_add]
          _ = 32635162537 := by rw [factor_1_18]; decide
      have factor_1_20 : (47 : ZMod 40156716601) ^ 1633980 = 34271140164 := by
        calc
          (47 : ZMod 40156716601) ^ 1633980 = (47 : ZMod 40156716601) ^ (816990 + 816990) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 816990 * (47 : ZMod 40156716601) ^ 816990 := by rw [pow_add]
          _ = 34271140164 := by rw [factor_1_19]; decide
      have factor_1_21 : (47 : ZMod 40156716601) ^ 3267961 = 25596823882 := by
        calc
          (47 : ZMod 40156716601) ^ 3267961 = (47 : ZMod 40156716601) ^ (1633980 + 1633980 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 1633980 * (47 : ZMod 40156716601) ^ 1633980) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 25596823882 := by rw [factor_1_20]; decide
      have factor_1_22 : (47 : ZMod 40156716601) ^ 6535923 = 11008373663 := by
        calc
          (47 : ZMod 40156716601) ^ 6535923 = (47 : ZMod 40156716601) ^ (3267961 + 3267961 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 3267961 * (47 : ZMod 40156716601) ^ 3267961) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 11008373663 := by rw [factor_1_21]; decide
      have factor_1_23 : (47 : ZMod 40156716601) ^ 13071847 = 27969061938 := by
        calc
          (47 : ZMod 40156716601) ^ 13071847 = (47 : ZMod 40156716601) ^ (6535923 + 6535923 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 6535923 * (47 : ZMod 40156716601) ^ 6535923) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 27969061938 := by rw [factor_1_22]; decide
      have factor_1_24 : (47 : ZMod 40156716601) ^ 26143695 = 5007681233 := by
        calc
          (47 : ZMod 40156716601) ^ 26143695 = (47 : ZMod 40156716601) ^ (13071847 + 13071847 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 13071847 * (47 : ZMod 40156716601) ^ 13071847) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 5007681233 := by rw [factor_1_23]; decide
      have factor_1_25 : (47 : ZMod 40156716601) ^ 52287391 = 29498529075 := by
        calc
          (47 : ZMod 40156716601) ^ 52287391 = (47 : ZMod 40156716601) ^ (26143695 + 26143695 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 26143695 * (47 : ZMod 40156716601) ^ 26143695) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 29498529075 := by rw [factor_1_24]; decide
      have factor_1_26 : (47 : ZMod 40156716601) ^ 104574782 = 12682134801 := by
        calc
          (47 : ZMod 40156716601) ^ 104574782 = (47 : ZMod 40156716601) ^ (52287391 + 52287391) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 52287391 * (47 : ZMod 40156716601) ^ 52287391 := by rw [pow_add]
          _ = 12682134801 := by rw [factor_1_25]; decide
      have factor_1_27 : (47 : ZMod 40156716601) ^ 209149565 = 8642718607 := by
        calc
          (47 : ZMod 40156716601) ^ 209149565 = (47 : ZMod 40156716601) ^ (104574782 + 104574782 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 104574782 * (47 : ZMod 40156716601) ^ 104574782) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 8642718607 := by rw [factor_1_26]; decide
      have factor_1_28 : (47 : ZMod 40156716601) ^ 418299131 = 10987037904 := by
        calc
          (47 : ZMod 40156716601) ^ 418299131 = (47 : ZMod 40156716601) ^ (209149565 + 209149565 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 209149565 * (47 : ZMod 40156716601) ^ 209149565) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 10987037904 := by rw [factor_1_27]; decide
      have factor_1_29 : (47 : ZMod 40156716601) ^ 836598262 = 15092460003 := by
        calc
          (47 : ZMod 40156716601) ^ 836598262 = (47 : ZMod 40156716601) ^ (418299131 + 418299131) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 418299131 * (47 : ZMod 40156716601) ^ 418299131 := by rw [pow_add]
          _ = 15092460003 := by rw [factor_1_28]; decide
      have factor_1_30 : (47 : ZMod 40156716601) ^ 1673196525 = 39347299563 := by
        calc
          (47 : ZMod 40156716601) ^ 1673196525 = (47 : ZMod 40156716601) ^ (836598262 + 836598262 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 836598262 * (47 : ZMod 40156716601) ^ 836598262) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 39347299563 := by rw [factor_1_29]; decide
      have factor_1_31 : (47 : ZMod 40156716601) ^ 3346393050 = 33663860267 := by
        calc
          (47 : ZMod 40156716601) ^ 3346393050 = (47 : ZMod 40156716601) ^ (1673196525 + 1673196525) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 1673196525 * (47 : ZMod 40156716601) ^ 1673196525 := by rw [pow_add]
          _ = 33663860267 := by rw [factor_1_30]; decide
      have factor_1_32 : (47 : ZMod 40156716601) ^ 6692786100 = 21663935864 := by
        calc
          (47 : ZMod 40156716601) ^ 6692786100 = (47 : ZMod 40156716601) ^ (3346393050 + 3346393050) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 3346393050 * (47 : ZMod 40156716601) ^ 3346393050 := by rw [pow_add]
          _ = 21663935864 := by rw [factor_1_31]; decide
      have factor_1_33 : (47 : ZMod 40156716601) ^ 13385572200 = 21663935863 := by
        calc
          (47 : ZMod 40156716601) ^ 13385572200 = (47 : ZMod 40156716601) ^ (6692786100 + 6692786100) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 6692786100 * (47 : ZMod 40156716601) ^ 6692786100 := by rw [pow_add]
          _ = 21663935863 := by rw [factor_1_32]; decide
      change (47 : ZMod 40156716601) ^ 13385572200 ≠ 1
      rw [factor_1_33]
      decide
    ·
      have factor_2_0 : (47 : ZMod 40156716601) ^ 1 = 47 := by norm_num
      have factor_2_1 : (47 : ZMod 40156716601) ^ 3 = 103823 := by
        calc
          (47 : ZMod 40156716601) ^ 3 = (47 : ZMod 40156716601) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 1 * (47 : ZMod 40156716601) ^ 1) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 103823 := by rw [factor_2_0]; decide
      have factor_2_2 : (47 : ZMod 40156716601) ^ 7 = 24742521251 := by
        calc
          (47 : ZMod 40156716601) ^ 7 = (47 : ZMod 40156716601) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 3 * (47 : ZMod 40156716601) ^ 3) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 24742521251 := by rw [factor_2_1]; decide
      have factor_2_3 : (47 : ZMod 40156716601) ^ 14 = 13792626183 := by
        calc
          (47 : ZMod 40156716601) ^ 14 = (47 : ZMod 40156716601) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 7 * (47 : ZMod 40156716601) ^ 7 := by rw [pow_add]
          _ = 13792626183 := by rw [factor_2_2]; decide
      have factor_2_4 : (47 : ZMod 40156716601) ^ 29 = 38932513244 := by
        calc
          (47 : ZMod 40156716601) ^ 29 = (47 : ZMod 40156716601) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 14 * (47 : ZMod 40156716601) ^ 14) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 38932513244 := by rw [factor_2_3]; decide
      have factor_2_5 : (47 : ZMod 40156716601) ^ 59 = 18399377214 := by
        calc
          (47 : ZMod 40156716601) ^ 59 = (47 : ZMod 40156716601) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 29 * (47 : ZMod 40156716601) ^ 29) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 18399377214 := by rw [factor_2_4]; decide
      have factor_2_6 : (47 : ZMod 40156716601) ^ 119 = 36765295926 := by
        calc
          (47 : ZMod 40156716601) ^ 119 = (47 : ZMod 40156716601) ^ (59 + 59 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 59 * (47 : ZMod 40156716601) ^ 59) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 36765295926 := by rw [factor_2_5]; decide
      have factor_2_7 : (47 : ZMod 40156716601) ^ 239 = 1049586067 := by
        calc
          (47 : ZMod 40156716601) ^ 239 = (47 : ZMod 40156716601) ^ (119 + 119 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 119 * (47 : ZMod 40156716601) ^ 119) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 1049586067 := by rw [factor_2_6]; decide
      have factor_2_8 : (47 : ZMod 40156716601) ^ 478 = 19920764598 := by
        calc
          (47 : ZMod 40156716601) ^ 478 = (47 : ZMod 40156716601) ^ (239 + 239) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 239 * (47 : ZMod 40156716601) ^ 239 := by rw [pow_add]
          _ = 19920764598 := by rw [factor_2_7]; decide
      have factor_2_9 : (47 : ZMod 40156716601) ^ 957 = 16710487395 := by
        calc
          (47 : ZMod 40156716601) ^ 957 = (47 : ZMod 40156716601) ^ (478 + 478 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 478 * (47 : ZMod 40156716601) ^ 478) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 16710487395 := by rw [factor_2_8]; decide
      have factor_2_10 : (47 : ZMod 40156716601) ^ 1914 = 11098051363 := by
        calc
          (47 : ZMod 40156716601) ^ 1914 = (47 : ZMod 40156716601) ^ (957 + 957) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 957 * (47 : ZMod 40156716601) ^ 957 := by rw [pow_add]
          _ = 11098051363 := by rw [factor_2_9]; decide
      have factor_2_11 : (47 : ZMod 40156716601) ^ 3829 = 38422834757 := by
        calc
          (47 : ZMod 40156716601) ^ 3829 = (47 : ZMod 40156716601) ^ (1914 + 1914 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 1914 * (47 : ZMod 40156716601) ^ 1914) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 38422834757 := by rw [factor_2_10]; decide
      have factor_2_12 : (47 : ZMod 40156716601) ^ 7659 = 23506824004 := by
        calc
          (47 : ZMod 40156716601) ^ 7659 = (47 : ZMod 40156716601) ^ (3829 + 3829 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 3829 * (47 : ZMod 40156716601) ^ 3829) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 23506824004 := by rw [factor_2_11]; decide
      have factor_2_13 : (47 : ZMod 40156716601) ^ 15318 = 25824548359 := by
        calc
          (47 : ZMod 40156716601) ^ 15318 = (47 : ZMod 40156716601) ^ (7659 + 7659) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 7659 * (47 : ZMod 40156716601) ^ 7659 := by rw [pow_add]
          _ = 25824548359 := by rw [factor_2_12]; decide
      have factor_2_14 : (47 : ZMod 40156716601) ^ 30637 = 36528933306 := by
        calc
          (47 : ZMod 40156716601) ^ 30637 = (47 : ZMod 40156716601) ^ (15318 + 15318 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 15318 * (47 : ZMod 40156716601) ^ 15318) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 36528933306 := by rw [factor_2_13]; decide
      have factor_2_15 : (47 : ZMod 40156716601) ^ 61274 = 4670003977 := by
        calc
          (47 : ZMod 40156716601) ^ 61274 = (47 : ZMod 40156716601) ^ (30637 + 30637) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 30637 * (47 : ZMod 40156716601) ^ 30637 := by rw [pow_add]
          _ = 4670003977 := by rw [factor_2_14]; decide
      have factor_2_16 : (47 : ZMod 40156716601) ^ 122548 = 4671129303 := by
        calc
          (47 : ZMod 40156716601) ^ 122548 = (47 : ZMod 40156716601) ^ (61274 + 61274) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 61274 * (47 : ZMod 40156716601) ^ 61274 := by rw [pow_add]
          _ = 4671129303 := by rw [factor_2_15]; decide
      have factor_2_17 : (47 : ZMod 40156716601) ^ 245097 = 12292219610 := by
        calc
          (47 : ZMod 40156716601) ^ 245097 = (47 : ZMod 40156716601) ^ (122548 + 122548 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 122548 * (47 : ZMod 40156716601) ^ 122548) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 12292219610 := by rw [factor_2_16]; decide
      have factor_2_18 : (47 : ZMod 40156716601) ^ 490194 = 20373896762 := by
        calc
          (47 : ZMod 40156716601) ^ 490194 = (47 : ZMod 40156716601) ^ (245097 + 245097) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 245097 * (47 : ZMod 40156716601) ^ 245097 := by rw [pow_add]
          _ = 20373896762 := by rw [factor_2_17]; decide
      have factor_2_19 : (47 : ZMod 40156716601) ^ 980388 = 25430169580 := by
        calc
          (47 : ZMod 40156716601) ^ 980388 = (47 : ZMod 40156716601) ^ (490194 + 490194) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 490194 * (47 : ZMod 40156716601) ^ 490194 := by rw [pow_add]
          _ = 25430169580 := by rw [factor_2_18]; decide
      have factor_2_20 : (47 : ZMod 40156716601) ^ 1960777 = 12484222907 := by
        calc
          (47 : ZMod 40156716601) ^ 1960777 = (47 : ZMod 40156716601) ^ (980388 + 980388 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 980388 * (47 : ZMod 40156716601) ^ 980388) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 12484222907 := by rw [factor_2_19]; decide
      have factor_2_21 : (47 : ZMod 40156716601) ^ 3921554 = 25916515880 := by
        calc
          (47 : ZMod 40156716601) ^ 3921554 = (47 : ZMod 40156716601) ^ (1960777 + 1960777) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 1960777 * (47 : ZMod 40156716601) ^ 1960777 := by rw [pow_add]
          _ = 25916515880 := by rw [factor_2_20]; decide
      have factor_2_22 : (47 : ZMod 40156716601) ^ 7843108 = 39557353808 := by
        calc
          (47 : ZMod 40156716601) ^ 7843108 = (47 : ZMod 40156716601) ^ (3921554 + 3921554) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 3921554 * (47 : ZMod 40156716601) ^ 3921554 := by rw [pow_add]
          _ = 39557353808 := by rw [factor_2_21]; decide
      have factor_2_23 : (47 : ZMod 40156716601) ^ 15686217 = 15870835794 := by
        calc
          (47 : ZMod 40156716601) ^ 15686217 = (47 : ZMod 40156716601) ^ (7843108 + 7843108 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 7843108 * (47 : ZMod 40156716601) ^ 7843108) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 15870835794 := by rw [factor_2_22]; decide
      have factor_2_24 : (47 : ZMod 40156716601) ^ 31372434 = 26038670280 := by
        calc
          (47 : ZMod 40156716601) ^ 31372434 = (47 : ZMod 40156716601) ^ (15686217 + 15686217) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 15686217 * (47 : ZMod 40156716601) ^ 15686217 := by rw [pow_add]
          _ = 26038670280 := by rw [factor_2_23]; decide
      have factor_2_25 : (47 : ZMod 40156716601) ^ 62744869 = 23531803345 := by
        calc
          (47 : ZMod 40156716601) ^ 62744869 = (47 : ZMod 40156716601) ^ (31372434 + 31372434 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 31372434 * (47 : ZMod 40156716601) ^ 31372434) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 23531803345 := by rw [factor_2_24]; decide
      have factor_2_26 : (47 : ZMod 40156716601) ^ 125489739 = 4970392052 := by
        calc
          (47 : ZMod 40156716601) ^ 125489739 = (47 : ZMod 40156716601) ^ (62744869 + 62744869 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 62744869 * (47 : ZMod 40156716601) ^ 62744869) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 4970392052 := by rw [factor_2_25]; decide
      have factor_2_27 : (47 : ZMod 40156716601) ^ 250979478 = 34894083715 := by
        calc
          (47 : ZMod 40156716601) ^ 250979478 = (47 : ZMod 40156716601) ^ (125489739 + 125489739) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 125489739 * (47 : ZMod 40156716601) ^ 125489739 := by rw [pow_add]
          _ = 34894083715 := by rw [factor_2_26]; decide
      have factor_2_28 : (47 : ZMod 40156716601) ^ 501958957 = 33170921717 := by
        calc
          (47 : ZMod 40156716601) ^ 501958957 = (47 : ZMod 40156716601) ^ (250979478 + 250979478 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 250979478 * (47 : ZMod 40156716601) ^ 250979478) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 33170921717 := by rw [factor_2_27]; decide
      have factor_2_29 : (47 : ZMod 40156716601) ^ 1003917915 = 32241410703 := by
        calc
          (47 : ZMod 40156716601) ^ 1003917915 = (47 : ZMod 40156716601) ^ (501958957 + 501958957 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 501958957 * (47 : ZMod 40156716601) ^ 501958957) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 32241410703 := by rw [factor_2_28]; decide
      have factor_2_30 : (47 : ZMod 40156716601) ^ 2007835830 = 22229430606 := by
        calc
          (47 : ZMod 40156716601) ^ 2007835830 = (47 : ZMod 40156716601) ^ (1003917915 + 1003917915) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 1003917915 * (47 : ZMod 40156716601) ^ 1003917915 := by rw [pow_add]
          _ = 22229430606 := by rw [factor_2_29]; decide
      have factor_2_31 : (47 : ZMod 40156716601) ^ 4015671660 = 10905403426 := by
        calc
          (47 : ZMod 40156716601) ^ 4015671660 = (47 : ZMod 40156716601) ^ (2007835830 + 2007835830) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 2007835830 * (47 : ZMod 40156716601) ^ 2007835830 := by rw [pow_add]
          _ = 10905403426 := by rw [factor_2_30]; decide
      have factor_2_32 : (47 : ZMod 40156716601) ^ 8031343320 = 307267146 := by
        calc
          (47 : ZMod 40156716601) ^ 8031343320 = (47 : ZMod 40156716601) ^ (4015671660 + 4015671660) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 4015671660 * (47 : ZMod 40156716601) ^ 4015671660 := by rw [pow_add]
          _ = 307267146 := by rw [factor_2_31]; decide
      change (47 : ZMod 40156716601) ^ 8031343320 ≠ 1
      rw [factor_2_32]
      decide
    ·
      have factor_3_0 : (47 : ZMod 40156716601) ^ 1 = 47 := by norm_num
      have factor_3_1 : (47 : ZMod 40156716601) ^ 2 = 2209 := by
        calc
          (47 : ZMod 40156716601) ^ 2 = (47 : ZMod 40156716601) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 1 * (47 : ZMod 40156716601) ^ 1 := by rw [pow_add]
          _ = 2209 := by rw [factor_3_0]; decide
      have factor_3_2 : (47 : ZMod 40156716601) ^ 5 = 229345007 := by
        calc
          (47 : ZMod 40156716601) ^ 5 = (47 : ZMod 40156716601) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 2 * (47 : ZMod 40156716601) ^ 2) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 229345007 := by rw [factor_3_1]; decide
      have factor_3_3 : (47 : ZMod 40156716601) ^ 10 = 17622876603 := by
        calc
          (47 : ZMod 40156716601) ^ 10 = (47 : ZMod 40156716601) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 5 * (47 : ZMod 40156716601) ^ 5 := by rw [pow_add]
          _ = 17622876603 := by rw [factor_3_2]; decide
      have factor_3_4 : (47 : ZMod 40156716601) ^ 21 = 33636134741 := by
        calc
          (47 : ZMod 40156716601) ^ 21 = (47 : ZMod 40156716601) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 10 * (47 : ZMod 40156716601) ^ 10) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 33636134741 := by rw [factor_3_3]; decide
      have factor_3_5 : (47 : ZMod 40156716601) ^ 42 = 36419018200 := by
        calc
          (47 : ZMod 40156716601) ^ 42 = (47 : ZMod 40156716601) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 21 * (47 : ZMod 40156716601) ^ 21 := by rw [pow_add]
          _ = 36419018200 := by rw [factor_3_4]; decide
      have factor_3_6 : (47 : ZMod 40156716601) ^ 85 = 33085512774 := by
        calc
          (47 : ZMod 40156716601) ^ 85 = (47 : ZMod 40156716601) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 42 * (47 : ZMod 40156716601) ^ 42) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 33085512774 := by rw [factor_3_5]; decide
      have factor_3_7 : (47 : ZMod 40156716601) ^ 170 = 12464584309 := by
        calc
          (47 : ZMod 40156716601) ^ 170 = (47 : ZMod 40156716601) ^ (85 + 85) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 85 * (47 : ZMod 40156716601) ^ 85 := by rw [pow_add]
          _ = 12464584309 := by rw [factor_3_6]; decide
      have factor_3_8 : (47 : ZMod 40156716601) ^ 341 = 24857263608 := by
        calc
          (47 : ZMod 40156716601) ^ 341 = (47 : ZMod 40156716601) ^ (170 + 170 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 170 * (47 : ZMod 40156716601) ^ 170) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 24857263608 := by rw [factor_3_7]; decide
      have factor_3_9 : (47 : ZMod 40156716601) ^ 683 = 27735362046 := by
        calc
          (47 : ZMod 40156716601) ^ 683 = (47 : ZMod 40156716601) ^ (341 + 341 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 341 * (47 : ZMod 40156716601) ^ 341) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 27735362046 := by rw [factor_3_8]; decide
      have factor_3_10 : (47 : ZMod 40156716601) ^ 1367 = 377628837 := by
        calc
          (47 : ZMod 40156716601) ^ 1367 = (47 : ZMod 40156716601) ^ (683 + 683 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 683 * (47 : ZMod 40156716601) ^ 683) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 377628837 := by rw [factor_3_9]; decide
      have factor_3_11 : (47 : ZMod 40156716601) ^ 2735 = 9664971306 := by
        calc
          (47 : ZMod 40156716601) ^ 2735 = (47 : ZMod 40156716601) ^ (1367 + 1367 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 1367 * (47 : ZMod 40156716601) ^ 1367) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 9664971306 := by rw [factor_3_10]; decide
      have factor_3_12 : (47 : ZMod 40156716601) ^ 5470 = 37889533646 := by
        calc
          (47 : ZMod 40156716601) ^ 5470 = (47 : ZMod 40156716601) ^ (2735 + 2735) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 2735 * (47 : ZMod 40156716601) ^ 2735 := by rw [pow_add]
          _ = 37889533646 := by rw [factor_3_11]; decide
      have factor_3_13 : (47 : ZMod 40156716601) ^ 10941 = 16088309724 := by
        calc
          (47 : ZMod 40156716601) ^ 10941 = (47 : ZMod 40156716601) ^ (5470 + 5470 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 5470 * (47 : ZMod 40156716601) ^ 5470) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 16088309724 := by rw [factor_3_12]; decide
      have factor_3_14 : (47 : ZMod 40156716601) ^ 21883 = 23489465663 := by
        calc
          (47 : ZMod 40156716601) ^ 21883 = (47 : ZMod 40156716601) ^ (10941 + 10941 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 10941 * (47 : ZMod 40156716601) ^ 10941) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 23489465663 := by rw [factor_3_13]; decide
      have factor_3_15 : (47 : ZMod 40156716601) ^ 43767 = 25453895123 := by
        calc
          (47 : ZMod 40156716601) ^ 43767 = (47 : ZMod 40156716601) ^ (21883 + 21883 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 21883 * (47 : ZMod 40156716601) ^ 21883) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 25453895123 := by rw [factor_3_14]; decide
      have factor_3_16 : (47 : ZMod 40156716601) ^ 87534 = 5816933948 := by
        calc
          (47 : ZMod 40156716601) ^ 87534 = (47 : ZMod 40156716601) ^ (43767 + 43767) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 43767 * (47 : ZMod 40156716601) ^ 43767 := by rw [pow_add]
          _ = 5816933948 := by rw [factor_3_15]; decide
      have factor_3_17 : (47 : ZMod 40156716601) ^ 175069 = 23412117568 := by
        calc
          (47 : ZMod 40156716601) ^ 175069 = (47 : ZMod 40156716601) ^ (87534 + 87534 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 87534 * (47 : ZMod 40156716601) ^ 87534) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 23412117568 := by rw [factor_3_16]; decide
      have factor_3_18 : (47 : ZMod 40156716601) ^ 350138 = 22698938375 := by
        calc
          (47 : ZMod 40156716601) ^ 350138 = (47 : ZMod 40156716601) ^ (175069 + 175069) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 175069 * (47 : ZMod 40156716601) ^ 175069 := by rw [pow_add]
          _ = 22698938375 := by rw [factor_3_17]; decide
      have factor_3_19 : (47 : ZMod 40156716601) ^ 700277 = 4938975322 := by
        calc
          (47 : ZMod 40156716601) ^ 700277 = (47 : ZMod 40156716601) ^ (350138 + 350138 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 350138 * (47 : ZMod 40156716601) ^ 350138) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 4938975322 := by rw [factor_3_18]; decide
      have factor_3_20 : (47 : ZMod 40156716601) ^ 1400555 = 16906422546 := by
        calc
          (47 : ZMod 40156716601) ^ 1400555 = (47 : ZMod 40156716601) ^ (700277 + 700277 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 700277 * (47 : ZMod 40156716601) ^ 700277) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 16906422546 := by rw [factor_3_19]; decide
      have factor_3_21 : (47 : ZMod 40156716601) ^ 2801110 = 23383026335 := by
        calc
          (47 : ZMod 40156716601) ^ 2801110 = (47 : ZMod 40156716601) ^ (1400555 + 1400555) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 1400555 * (47 : ZMod 40156716601) ^ 1400555 := by rw [pow_add]
          _ = 23383026335 := by rw [factor_3_20]; decide
      have factor_3_22 : (47 : ZMod 40156716601) ^ 5602220 = 22355043568 := by
        calc
          (47 : ZMod 40156716601) ^ 5602220 = (47 : ZMod 40156716601) ^ (2801110 + 2801110) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 2801110 * (47 : ZMod 40156716601) ^ 2801110 := by rw [pow_add]
          _ = 22355043568 := by rw [factor_3_21]; decide
      have factor_3_23 : (47 : ZMod 40156716601) ^ 11204441 = 11368838760 := by
        calc
          (47 : ZMod 40156716601) ^ 11204441 = (47 : ZMod 40156716601) ^ (5602220 + 5602220 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 5602220 * (47 : ZMod 40156716601) ^ 5602220) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 11368838760 := by rw [factor_3_22]; decide
      have factor_3_24 : (47 : ZMod 40156716601) ^ 22408882 = 35434999837 := by
        calc
          (47 : ZMod 40156716601) ^ 22408882 = (47 : ZMod 40156716601) ^ (11204441 + 11204441) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 11204441 * (47 : ZMod 40156716601) ^ 11204441 := by rw [pow_add]
          _ = 35434999837 := by rw [factor_3_23]; decide
      have factor_3_25 : (47 : ZMod 40156716601) ^ 44817764 = 23147344454 := by
        calc
          (47 : ZMod 40156716601) ^ 44817764 = (47 : ZMod 40156716601) ^ (22408882 + 22408882) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 22408882 * (47 : ZMod 40156716601) ^ 22408882 := by rw [pow_add]
          _ = 23147344454 := by rw [factor_3_24]; decide
      have factor_3_26 : (47 : ZMod 40156716601) ^ 89635528 = 1116145851 := by
        calc
          (47 : ZMod 40156716601) ^ 89635528 = (47 : ZMod 40156716601) ^ (44817764 + 44817764) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 44817764 * (47 : ZMod 40156716601) ^ 44817764 := by rw [pow_add]
          _ = 1116145851 := by rw [factor_3_25]; decide
      have factor_3_27 : (47 : ZMod 40156716601) ^ 179271056 = 22688707408 := by
        calc
          (47 : ZMod 40156716601) ^ 179271056 = (47 : ZMod 40156716601) ^ (89635528 + 89635528) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 89635528 * (47 : ZMod 40156716601) ^ 89635528 := by rw [pow_add]
          _ = 22688707408 := by rw [factor_3_26]; decide
      have factor_3_28 : (47 : ZMod 40156716601) ^ 358542112 = 29859934550 := by
        calc
          (47 : ZMod 40156716601) ^ 358542112 = (47 : ZMod 40156716601) ^ (179271056 + 179271056) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 179271056 * (47 : ZMod 40156716601) ^ 179271056 := by rw [pow_add]
          _ = 29859934550 := by rw [factor_3_27]; decide
      have factor_3_29 : (47 : ZMod 40156716601) ^ 717084225 = 4814856636 := by
        calc
          (47 : ZMod 40156716601) ^ 717084225 = (47 : ZMod 40156716601) ^ (358542112 + 358542112 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 358542112 * (47 : ZMod 40156716601) ^ 358542112) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 4814856636 := by rw [factor_3_28]; decide
      have factor_3_30 : (47 : ZMod 40156716601) ^ 1434168450 = 40123494635 := by
        calc
          (47 : ZMod 40156716601) ^ 1434168450 = (47 : ZMod 40156716601) ^ (717084225 + 717084225) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 717084225 * (47 : ZMod 40156716601) ^ 717084225 := by rw [pow_add]
          _ = 40123494635 := by rw [factor_3_29]; decide
      have factor_3_31 : (47 : ZMod 40156716601) ^ 2868336900 = 31825843272 := by
        calc
          (47 : ZMod 40156716601) ^ 2868336900 = (47 : ZMod 40156716601) ^ (1434168450 + 1434168450) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 1434168450 * (47 : ZMod 40156716601) ^ 1434168450 := by rw [pow_add]
          _ = 31825843272 := by rw [factor_3_30]; decide
      have factor_3_32 : (47 : ZMod 40156716601) ^ 5736673800 = 32116101972 := by
        calc
          (47 : ZMod 40156716601) ^ 5736673800 = (47 : ZMod 40156716601) ^ (2868336900 + 2868336900) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 2868336900 * (47 : ZMod 40156716601) ^ 2868336900 := by rw [pow_add]
          _ = 32116101972 := by rw [factor_3_31]; decide
      change (47 : ZMod 40156716601) ^ 5736673800 ≠ 1
      rw [factor_3_32]
      decide
    ·
      have factor_4_0 : (47 : ZMod 40156716601) ^ 1 = 47 := by norm_num
      have factor_4_1 : (47 : ZMod 40156716601) ^ 3 = 103823 := by
        calc
          (47 : ZMod 40156716601) ^ 3 = (47 : ZMod 40156716601) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 1 * (47 : ZMod 40156716601) ^ 1) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 103823 := by rw [factor_4_0]; decide
      have factor_4_2 : (47 : ZMod 40156716601) ^ 6 = 10779215329 := by
        calc
          (47 : ZMod 40156716601) ^ 6 = (47 : ZMod 40156716601) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 3 * (47 : ZMod 40156716601) ^ 3 := by rw [pow_add]
          _ = 10779215329 := by rw [factor_4_1]; decide
      have factor_4_3 : (47 : ZMod 40156716601) ^ 13 = 39595778507 := by
        calc
          (47 : ZMod 40156716601) ^ 13 = (47 : ZMod 40156716601) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 6 * (47 : ZMod 40156716601) ^ 6) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 39595778507 := by rw [factor_4_2]; decide
      have factor_4_4 : (47 : ZMod 40156716601) ^ 27 = 22704624188 := by
        calc
          (47 : ZMod 40156716601) ^ 27 = (47 : ZMod 40156716601) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 13 * (47 : ZMod 40156716601) ^ 13) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 22704624188 := by rw [factor_4_3]; decide
      have factor_4_5 : (47 : ZMod 40156716601) ^ 54 = 34725399631 := by
        calc
          (47 : ZMod 40156716601) ^ 54 = (47 : ZMod 40156716601) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 27 * (47 : ZMod 40156716601) ^ 27 := by rw [pow_add]
          _ = 34725399631 := by rw [factor_4_4]; decide
      have factor_4_6 : (47 : ZMod 40156716601) ^ 108 = 21335911708 := by
        calc
          (47 : ZMod 40156716601) ^ 108 = (47 : ZMod 40156716601) ^ (54 + 54) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 54 * (47 : ZMod 40156716601) ^ 54 := by rw [pow_add]
          _ = 21335911708 := by rw [factor_4_5]; decide
      have factor_4_7 : (47 : ZMod 40156716601) ^ 217 = 9913897550 := by
        calc
          (47 : ZMod 40156716601) ^ 217 = (47 : ZMod 40156716601) ^ (108 + 108 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 108 * (47 : ZMod 40156716601) ^ 108) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 9913897550 := by rw [factor_4_6]; decide
      have factor_4_8 : (47 : ZMod 40156716601) ^ 435 = 34910151476 := by
        calc
          (47 : ZMod 40156716601) ^ 435 = (47 : ZMod 40156716601) ^ (217 + 217 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 217 * (47 : ZMod 40156716601) ^ 217) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 34910151476 := by rw [factor_4_7]; decide
      have factor_4_9 : (47 : ZMod 40156716601) ^ 870 = 19653907120 := by
        calc
          (47 : ZMod 40156716601) ^ 870 = (47 : ZMod 40156716601) ^ (435 + 435) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 435 * (47 : ZMod 40156716601) ^ 435 := by rw [pow_add]
          _ = 19653907120 := by rw [factor_4_8]; decide
      have factor_4_10 : (47 : ZMod 40156716601) ^ 1740 = 22483670838 := by
        calc
          (47 : ZMod 40156716601) ^ 1740 = (47 : ZMod 40156716601) ^ (870 + 870) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 870 * (47 : ZMod 40156716601) ^ 870 := by rw [pow_add]
          _ = 22483670838 := by rw [factor_4_9]; decide
      have factor_4_11 : (47 : ZMod 40156716601) ^ 3481 = 2436848298 := by
        calc
          (47 : ZMod 40156716601) ^ 3481 = (47 : ZMod 40156716601) ^ (1740 + 1740 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 1740 * (47 : ZMod 40156716601) ^ 1740) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 2436848298 := by rw [factor_4_10]; decide
      have factor_4_12 : (47 : ZMod 40156716601) ^ 6962 = 24920728631 := by
        calc
          (47 : ZMod 40156716601) ^ 6962 = (47 : ZMod 40156716601) ^ (3481 + 3481) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 3481 * (47 : ZMod 40156716601) ^ 3481 := by rw [pow_add]
          _ = 24920728631 := by rw [factor_4_11]; decide
      have factor_4_13 : (47 : ZMod 40156716601) ^ 13925 = 6418110734 := by
        calc
          (47 : ZMod 40156716601) ^ 13925 = (47 : ZMod 40156716601) ^ (6962 + 6962 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 6962 * (47 : ZMod 40156716601) ^ 6962) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 6418110734 := by rw [factor_4_12]; decide
      have factor_4_14 : (47 : ZMod 40156716601) ^ 27851 = 28200469747 := by
        calc
          (47 : ZMod 40156716601) ^ 27851 = (47 : ZMod 40156716601) ^ (13925 + 13925 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 13925 * (47 : ZMod 40156716601) ^ 13925) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 28200469747 := by rw [factor_4_13]; decide
      have factor_4_15 : (47 : ZMod 40156716601) ^ 55703 = 24110209720 := by
        calc
          (47 : ZMod 40156716601) ^ 55703 = (47 : ZMod 40156716601) ^ (27851 + 27851 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 27851 * (47 : ZMod 40156716601) ^ 27851) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 24110209720 := by rw [factor_4_14]; decide
      have factor_4_16 : (47 : ZMod 40156716601) ^ 111407 = 22742226085 := by
        calc
          (47 : ZMod 40156716601) ^ 111407 = (47 : ZMod 40156716601) ^ (55703 + 55703 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 55703 * (47 : ZMod 40156716601) ^ 55703) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 22742226085 := by rw [factor_4_15]; decide
      have factor_4_17 : (47 : ZMod 40156716601) ^ 222815 = 29616428528 := by
        calc
          (47 : ZMod 40156716601) ^ 222815 = (47 : ZMod 40156716601) ^ (111407 + 111407 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 111407 * (47 : ZMod 40156716601) ^ 111407) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 29616428528 := by rw [factor_4_16]; decide
      have factor_4_18 : (47 : ZMod 40156716601) ^ 445631 = 18019931621 := by
        calc
          (47 : ZMod 40156716601) ^ 445631 = (47 : ZMod 40156716601) ^ (222815 + 222815 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 222815 * (47 : ZMod 40156716601) ^ 222815) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 18019931621 := by rw [factor_4_17]; decide
      have factor_4_19 : (47 : ZMod 40156716601) ^ 891262 = 13489742758 := by
        calc
          (47 : ZMod 40156716601) ^ 891262 = (47 : ZMod 40156716601) ^ (445631 + 445631) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 445631 * (47 : ZMod 40156716601) ^ 445631 := by rw [pow_add]
          _ = 13489742758 := by rw [factor_4_18]; decide
      have factor_4_20 : (47 : ZMod 40156716601) ^ 1782524 = 18023499697 := by
        calc
          (47 : ZMod 40156716601) ^ 1782524 = (47 : ZMod 40156716601) ^ (891262 + 891262) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 891262 * (47 : ZMod 40156716601) ^ 891262 := by rw [pow_add]
          _ = 18023499697 := by rw [factor_4_19]; decide
      have factor_4_21 : (47 : ZMod 40156716601) ^ 3565049 = 25906365739 := by
        calc
          (47 : ZMod 40156716601) ^ 3565049 = (47 : ZMod 40156716601) ^ (1782524 + 1782524 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 1782524 * (47 : ZMod 40156716601) ^ 1782524) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 25906365739 := by rw [factor_4_20]; decide
      have factor_4_22 : (47 : ZMod 40156716601) ^ 7130098 = 22003933247 := by
        calc
          (47 : ZMod 40156716601) ^ 7130098 = (47 : ZMod 40156716601) ^ (3565049 + 3565049) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 3565049 * (47 : ZMod 40156716601) ^ 3565049 := by rw [pow_add]
          _ = 22003933247 := by rw [factor_4_21]; decide
      have factor_4_23 : (47 : ZMod 40156716601) ^ 14260197 = 17634968606 := by
        calc
          (47 : ZMod 40156716601) ^ 14260197 = (47 : ZMod 40156716601) ^ (7130098 + 7130098 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 7130098 * (47 : ZMod 40156716601) ^ 7130098) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 17634968606 := by rw [factor_4_22]; decide
      have factor_4_24 : (47 : ZMod 40156716601) ^ 28520395 = 38773873504 := by
        calc
          (47 : ZMod 40156716601) ^ 28520395 = (47 : ZMod 40156716601) ^ (14260197 + 14260197 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 14260197 * (47 : ZMod 40156716601) ^ 14260197) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 38773873504 := by rw [factor_4_23]; decide
      have factor_4_25 : (47 : ZMod 40156716601) ^ 57040790 = 16940668604 := by
        calc
          (47 : ZMod 40156716601) ^ 57040790 = (47 : ZMod 40156716601) ^ (28520395 + 28520395) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 28520395 * (47 : ZMod 40156716601) ^ 28520395 := by rw [pow_add]
          _ = 16940668604 := by rw [factor_4_24]; decide
      have factor_4_26 : (47 : ZMod 40156716601) ^ 114081581 = 19321090204 := by
        calc
          (47 : ZMod 40156716601) ^ 114081581 = (47 : ZMod 40156716601) ^ (57040790 + 57040790 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 57040790 * (47 : ZMod 40156716601) ^ 57040790) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 19321090204 := by rw [factor_4_25]; decide
      have factor_4_27 : (47 : ZMod 40156716601) ^ 228163162 = 20427435338 := by
        calc
          (47 : ZMod 40156716601) ^ 228163162 = (47 : ZMod 40156716601) ^ (114081581 + 114081581) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 114081581 * (47 : ZMod 40156716601) ^ 114081581 := by rw [pow_add]
          _ = 20427435338 := by rw [factor_4_26]; decide
      have factor_4_28 : (47 : ZMod 40156716601) ^ 456326325 = 7257972255 := by
        calc
          (47 : ZMod 40156716601) ^ 456326325 = (47 : ZMod 40156716601) ^ (228163162 + 228163162 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 228163162 * (47 : ZMod 40156716601) ^ 228163162) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 7257972255 := by rw [factor_4_27]; decide
      have factor_4_29 : (47 : ZMod 40156716601) ^ 912652650 = 32132950772 := by
        calc
          (47 : ZMod 40156716601) ^ 912652650 = (47 : ZMod 40156716601) ^ (456326325 + 456326325) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 456326325 * (47 : ZMod 40156716601) ^ 456326325 := by rw [pow_add]
          _ = 32132950772 := by rw [factor_4_28]; decide
      have factor_4_30 : (47 : ZMod 40156716601) ^ 1825305300 = 16755907944 := by
        calc
          (47 : ZMod 40156716601) ^ 1825305300 = (47 : ZMod 40156716601) ^ (912652650 + 912652650) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 912652650 * (47 : ZMod 40156716601) ^ 912652650 := by rw [pow_add]
          _ = 16755907944 := by rw [factor_4_29]; decide
      have factor_4_31 : (47 : ZMod 40156716601) ^ 3650610600 = 28553252229 := by
        calc
          (47 : ZMod 40156716601) ^ 3650610600 = (47 : ZMod 40156716601) ^ (1825305300 + 1825305300) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 1825305300 * (47 : ZMod 40156716601) ^ 1825305300 := by rw [pow_add]
          _ = 28553252229 := by rw [factor_4_30]; decide
      change (47 : ZMod 40156716601) ^ 3650610600 ≠ 1
      rw [factor_4_31]
      decide
    ·
      have factor_5_0 : (47 : ZMod 40156716601) ^ 1 = 47 := by norm_num
      have factor_5_1 : (47 : ZMod 40156716601) ^ 2 = 2209 := by
        calc
          (47 : ZMod 40156716601) ^ 2 = (47 : ZMod 40156716601) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 1 * (47 : ZMod 40156716601) ^ 1 := by rw [pow_add]
          _ = 2209 := by rw [factor_5_0]; decide
      have factor_5_2 : (47 : ZMod 40156716601) ^ 5 = 229345007 := by
        calc
          (47 : ZMod 40156716601) ^ 5 = (47 : ZMod 40156716601) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 2 * (47 : ZMod 40156716601) ^ 2) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 229345007 := by rw [factor_5_1]; decide
      have factor_5_3 : (47 : ZMod 40156716601) ^ 11 = 25140868321 := by
        calc
          (47 : ZMod 40156716601) ^ 11 = (47 : ZMod 40156716601) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 5 * (47 : ZMod 40156716601) ^ 5) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 25140868321 := by rw [factor_5_2]; decide
      have factor_5_4 : (47 : ZMod 40156716601) ^ 23 = 12295931019 := by
        calc
          (47 : ZMod 40156716601) ^ 23 = (47 : ZMod 40156716601) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 11 * (47 : ZMod 40156716601) ^ 11) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 12295931019 := by rw [factor_5_3]; decide
      have factor_5_5 : (47 : ZMod 40156716601) ^ 46 = 3241918109 := by
        calc
          (47 : ZMod 40156716601) ^ 46 = (47 : ZMod 40156716601) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 23 * (47 : ZMod 40156716601) ^ 23 := by rw [pow_add]
          _ = 3241918109 := by rw [factor_5_4]; decide
      have factor_5_6 : (47 : ZMod 40156716601) ^ 92 = 29281754274 := by
        calc
          (47 : ZMod 40156716601) ^ 92 = (47 : ZMod 40156716601) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 46 * (47 : ZMod 40156716601) ^ 46 := by rw [pow_add]
          _ = 29281754274 := by rw [factor_5_5]; decide
      have factor_5_7 : (47 : ZMod 40156716601) ^ 184 = 1761560768 := by
        calc
          (47 : ZMod 40156716601) ^ 184 = (47 : ZMod 40156716601) ^ (92 + 92) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 92 * (47 : ZMod 40156716601) ^ 92 := by rw [pow_add]
          _ = 1761560768 := by rw [factor_5_6]; decide
      have factor_5_8 : (47 : ZMod 40156716601) ^ 368 = 38551851972 := by
        calc
          (47 : ZMod 40156716601) ^ 368 = (47 : ZMod 40156716601) ^ (184 + 184) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 184 * (47 : ZMod 40156716601) ^ 184 := by rw [pow_add]
          _ = 38551851972 := by rw [factor_5_7]; decide
      have factor_5_9 : (47 : ZMod 40156716601) ^ 736 = 34090133969 := by
        calc
          (47 : ZMod 40156716601) ^ 736 = (47 : ZMod 40156716601) ^ (368 + 368) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 368 * (47 : ZMod 40156716601) ^ 368 := by rw [pow_add]
          _ = 34090133969 := by rw [factor_5_8]; decide
      have factor_5_10 : (47 : ZMod 40156716601) ^ 1472 = 29866993953 := by
        calc
          (47 : ZMod 40156716601) ^ 1472 = (47 : ZMod 40156716601) ^ (736 + 736) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 736 * (47 : ZMod 40156716601) ^ 736 := by rw [pow_add]
          _ = 29866993953 := by rw [factor_5_9]; decide
      have factor_5_11 : (47 : ZMod 40156716601) ^ 2945 = 3119804170 := by
        calc
          (47 : ZMod 40156716601) ^ 2945 = (47 : ZMod 40156716601) ^ (1472 + 1472 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 1472 * (47 : ZMod 40156716601) ^ 1472) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 3119804170 := by rw [factor_5_10]; decide
      have factor_5_12 : (47 : ZMod 40156716601) ^ 5891 = 29434003789 := by
        calc
          (47 : ZMod 40156716601) ^ 5891 = (47 : ZMod 40156716601) ^ (2945 + 2945 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 2945 * (47 : ZMod 40156716601) ^ 2945) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 29434003789 := by rw [factor_5_11]; decide
      have factor_5_13 : (47 : ZMod 40156716601) ^ 11783 = 11029577507 := by
        calc
          (47 : ZMod 40156716601) ^ 11783 = (47 : ZMod 40156716601) ^ (5891 + 5891 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 5891 * (47 : ZMod 40156716601) ^ 5891) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 11029577507 := by rw [factor_5_12]; decide
      have factor_5_14 : (47 : ZMod 40156716601) ^ 23567 = 32541528590 := by
        calc
          (47 : ZMod 40156716601) ^ 23567 = (47 : ZMod 40156716601) ^ (11783 + 11783 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 11783 * (47 : ZMod 40156716601) ^ 11783) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 32541528590 := by rw [factor_5_13]; decide
      have factor_5_15 : (47 : ZMod 40156716601) ^ 47134 = 18818268447 := by
        calc
          (47 : ZMod 40156716601) ^ 47134 = (47 : ZMod 40156716601) ^ (23567 + 23567) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 23567 * (47 : ZMod 40156716601) ^ 23567 := by rw [pow_add]
          _ = 18818268447 := by rw [factor_5_14]; decide
      have factor_5_16 : (47 : ZMod 40156716601) ^ 94268 = 18010497769 := by
        calc
          (47 : ZMod 40156716601) ^ 94268 = (47 : ZMod 40156716601) ^ (47134 + 47134) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 47134 * (47 : ZMod 40156716601) ^ 47134 := by rw [pow_add]
          _ = 18010497769 := by rw [factor_5_15]; decide
      have factor_5_17 : (47 : ZMod 40156716601) ^ 188536 = 39819581559 := by
        calc
          (47 : ZMod 40156716601) ^ 188536 = (47 : ZMod 40156716601) ^ (94268 + 94268) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 94268 * (47 : ZMod 40156716601) ^ 94268 := by rw [pow_add]
          _ = 39819581559 := by rw [factor_5_16]; decide
      have factor_5_18 : (47 : ZMod 40156716601) ^ 377072 = 24152988753 := by
        calc
          (47 : ZMod 40156716601) ^ 377072 = (47 : ZMod 40156716601) ^ (188536 + 188536) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 188536 * (47 : ZMod 40156716601) ^ 188536 := by rw [pow_add]
          _ = 24152988753 := by rw [factor_5_17]; decide
      have factor_5_19 : (47 : ZMod 40156716601) ^ 754145 = 28607746320 := by
        calc
          (47 : ZMod 40156716601) ^ 754145 = (47 : ZMod 40156716601) ^ (377072 + 377072 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 377072 * (47 : ZMod 40156716601) ^ 377072) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 28607746320 := by rw [factor_5_18]; decide
      have factor_5_20 : (47 : ZMod 40156716601) ^ 1508290 = 22655776675 := by
        calc
          (47 : ZMod 40156716601) ^ 1508290 = (47 : ZMod 40156716601) ^ (754145 + 754145) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 754145 * (47 : ZMod 40156716601) ^ 754145 := by rw [pow_add]
          _ = 22655776675 := by rw [factor_5_19]; decide
      have factor_5_21 : (47 : ZMod 40156716601) ^ 3016580 = 36740930701 := by
        calc
          (47 : ZMod 40156716601) ^ 3016580 = (47 : ZMod 40156716601) ^ (1508290 + 1508290) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 1508290 * (47 : ZMod 40156716601) ^ 1508290 := by rw [pow_add]
          _ = 36740930701 := by rw [factor_5_20]; decide
      have factor_5_22 : (47 : ZMod 40156716601) ^ 6033160 = 34904556924 := by
        calc
          (47 : ZMod 40156716601) ^ 6033160 = (47 : ZMod 40156716601) ^ (3016580 + 3016580) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 3016580 * (47 : ZMod 40156716601) ^ 3016580 := by rw [pow_add]
          _ = 34904556924 := by rw [factor_5_21]; decide
      have factor_5_23 : (47 : ZMod 40156716601) ^ 12066321 = 13615327840 := by
        calc
          (47 : ZMod 40156716601) ^ 12066321 = (47 : ZMod 40156716601) ^ (6033160 + 6033160 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 6033160 * (47 : ZMod 40156716601) ^ 6033160) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 13615327840 := by rw [factor_5_22]; decide
      have factor_5_24 : (47 : ZMod 40156716601) ^ 24132642 = 25870531033 := by
        calc
          (47 : ZMod 40156716601) ^ 24132642 = (47 : ZMod 40156716601) ^ (12066321 + 12066321) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 12066321 * (47 : ZMod 40156716601) ^ 12066321 := by rw [pow_add]
          _ = 25870531033 := by rw [factor_5_23]; decide
      have factor_5_25 : (47 : ZMod 40156716601) ^ 48265284 = 37367370238 := by
        calc
          (47 : ZMod 40156716601) ^ 48265284 = (47 : ZMod 40156716601) ^ (24132642 + 24132642) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 24132642 * (47 : ZMod 40156716601) ^ 24132642 := by rw [pow_add]
          _ = 37367370238 := by rw [factor_5_24]; decide
      have factor_5_26 : (47 : ZMod 40156716601) ^ 96530568 = 22956573746 := by
        calc
          (47 : ZMod 40156716601) ^ 96530568 = (47 : ZMod 40156716601) ^ (48265284 + 48265284) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 48265284 * (47 : ZMod 40156716601) ^ 48265284 := by rw [pow_add]
          _ = 22956573746 := by rw [factor_5_25]; decide
      have factor_5_27 : (47 : ZMod 40156716601) ^ 193061137 = 12691359124 := by
        calc
          (47 : ZMod 40156716601) ^ 193061137 = (47 : ZMod 40156716601) ^ (96530568 + 96530568 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 96530568 * (47 : ZMod 40156716601) ^ 96530568) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 12691359124 := by rw [factor_5_26]; decide
      have factor_5_28 : (47 : ZMod 40156716601) ^ 386122275 = 32592078672 := by
        calc
          (47 : ZMod 40156716601) ^ 386122275 = (47 : ZMod 40156716601) ^ (193061137 + 193061137 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 193061137 * (47 : ZMod 40156716601) ^ 193061137) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 32592078672 := by rw [factor_5_27]; decide
      have factor_5_29 : (47 : ZMod 40156716601) ^ 772244550 = 18617572037 := by
        calc
          (47 : ZMod 40156716601) ^ 772244550 = (47 : ZMod 40156716601) ^ (386122275 + 386122275) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 386122275 * (47 : ZMod 40156716601) ^ 386122275 := by rw [pow_add]
          _ = 18617572037 := by rw [factor_5_28]; decide
      have factor_5_30 : (47 : ZMod 40156716601) ^ 1544489100 = 20123070865 := by
        calc
          (47 : ZMod 40156716601) ^ 1544489100 = (47 : ZMod 40156716601) ^ (772244550 + 772244550) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 772244550 * (47 : ZMod 40156716601) ^ 772244550 := by rw [pow_add]
          _ = 20123070865 := by rw [factor_5_29]; decide
      have factor_5_31 : (47 : ZMod 40156716601) ^ 3088978200 = 1249006725 := by
        calc
          (47 : ZMod 40156716601) ^ 3088978200 = (47 : ZMod 40156716601) ^ (1544489100 + 1544489100) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 1544489100 * (47 : ZMod 40156716601) ^ 1544489100 := by rw [pow_add]
          _ = 1249006725 := by rw [factor_5_30]; decide
      change (47 : ZMod 40156716601) ^ 3088978200 ≠ 1
      rw [factor_5_31]
      decide
    ·
      have factor_6_0 : (47 : ZMod 40156716601) ^ 1 = 47 := by norm_num
      have factor_6_1 : (47 : ZMod 40156716601) ^ 2 = 2209 := by
        calc
          (47 : ZMod 40156716601) ^ 2 = (47 : ZMod 40156716601) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 1 * (47 : ZMod 40156716601) ^ 1 := by rw [pow_add]
          _ = 2209 := by rw [factor_6_0]; decide
      have factor_6_2 : (47 : ZMod 40156716601) ^ 4 = 4879681 := by
        calc
          (47 : ZMod 40156716601) ^ 4 = (47 : ZMod 40156716601) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 2 * (47 : ZMod 40156716601) ^ 2 := by rw [pow_add]
          _ = 4879681 := by rw [factor_6_1]; decide
      have factor_6_3 : (47 : ZMod 40156716601) ^ 8 = 38510433969 := by
        calc
          (47 : ZMod 40156716601) ^ 8 = (47 : ZMod 40156716601) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 4 * (47 : ZMod 40156716601) ^ 4 := by rw [pow_add]
          _ = 38510433969 := by rw [factor_6_2]; decide
      have factor_6_4 : (47 : ZMod 40156716601) ^ 17 = 3314205949 := by
        calc
          (47 : ZMod 40156716601) ^ 17 = (47 : ZMod 40156716601) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 8 * (47 : ZMod 40156716601) ^ 8) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 3314205949 := by rw [factor_6_3]; decide
      have factor_6_5 : (47 : ZMod 40156716601) ^ 35 = 17376147266 := by
        calc
          (47 : ZMod 40156716601) ^ 35 = (47 : ZMod 40156716601) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 17 * (47 : ZMod 40156716601) ^ 17) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 17376147266 := by rw [factor_6_4]; decide
      have factor_6_6 : (47 : ZMod 40156716601) ^ 70 = 34985357648 := by
        calc
          (47 : ZMod 40156716601) ^ 70 = (47 : ZMod 40156716601) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 35 * (47 : ZMod 40156716601) ^ 35 := by rw [pow_add]
          _ = 34985357648 := by rw [factor_6_5]; decide
      have factor_6_7 : (47 : ZMod 40156716601) ^ 140 = 25692834367 := by
        calc
          (47 : ZMod 40156716601) ^ 140 = (47 : ZMod 40156716601) ^ (70 + 70) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 70 * (47 : ZMod 40156716601) ^ 70 := by rw [pow_add]
          _ = 25692834367 := by rw [factor_6_6]; decide
      have factor_6_8 : (47 : ZMod 40156716601) ^ 281 = 14227920884 := by
        calc
          (47 : ZMod 40156716601) ^ 281 = (47 : ZMod 40156716601) ^ (140 + 140 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 140 * (47 : ZMod 40156716601) ^ 140) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 14227920884 := by rw [factor_6_7]; decide
      have factor_6_9 : (47 : ZMod 40156716601) ^ 563 = 16144504063 := by
        calc
          (47 : ZMod 40156716601) ^ 563 = (47 : ZMod 40156716601) ^ (281 + 281 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 281 * (47 : ZMod 40156716601) ^ 281) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 16144504063 := by rw [factor_6_8]; decide
      have factor_6_10 : (47 : ZMod 40156716601) ^ 1126 = 15777848876 := by
        calc
          (47 : ZMod 40156716601) ^ 1126 = (47 : ZMod 40156716601) ^ (563 + 563) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 563 * (47 : ZMod 40156716601) ^ 563 := by rw [pow_add]
          _ = 15777848876 := by rw [factor_6_9]; decide
      have factor_6_11 : (47 : ZMod 40156716601) ^ 2252 = 27821461334 := by
        calc
          (47 : ZMod 40156716601) ^ 2252 = (47 : ZMod 40156716601) ^ (1126 + 1126) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 1126 * (47 : ZMod 40156716601) ^ 1126 := by rw [pow_add]
          _ = 27821461334 := by rw [factor_6_10]; decide
      have factor_6_12 : (47 : ZMod 40156716601) ^ 4505 = 16834076964 := by
        calc
          (47 : ZMod 40156716601) ^ 4505 = (47 : ZMod 40156716601) ^ (2252 + 2252 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 2252 * (47 : ZMod 40156716601) ^ 2252) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 16834076964 := by rw [factor_6_11]; decide
      have factor_6_13 : (47 : ZMod 40156716601) ^ 9010 = 3222031361 := by
        calc
          (47 : ZMod 40156716601) ^ 9010 = (47 : ZMod 40156716601) ^ (4505 + 4505) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 4505 * (47 : ZMod 40156716601) ^ 4505 := by rw [pow_add]
          _ = 3222031361 := by rw [factor_6_12]; decide
      have factor_6_14 : (47 : ZMod 40156716601) ^ 18021 = 15529603309 := by
        calc
          (47 : ZMod 40156716601) ^ 18021 = (47 : ZMod 40156716601) ^ (9010 + 9010 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 9010 * (47 : ZMod 40156716601) ^ 9010) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 15529603309 := by rw [factor_6_13]; decide
      have factor_6_15 : (47 : ZMod 40156716601) ^ 36043 = 14953621990 := by
        calc
          (47 : ZMod 40156716601) ^ 36043 = (47 : ZMod 40156716601) ^ (18021 + 18021 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 18021 * (47 : ZMod 40156716601) ^ 18021) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 14953621990 := by rw [factor_6_14]; decide
      have factor_6_16 : (47 : ZMod 40156716601) ^ 72087 = 22153493228 := by
        calc
          (47 : ZMod 40156716601) ^ 72087 = (47 : ZMod 40156716601) ^ (36043 + 36043 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 36043 * (47 : ZMod 40156716601) ^ 36043) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 22153493228 := by rw [factor_6_15]; decide
      have factor_6_17 : (47 : ZMod 40156716601) ^ 144174 = 12821915818 := by
        calc
          (47 : ZMod 40156716601) ^ 144174 = (47 : ZMod 40156716601) ^ (72087 + 72087) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 72087 * (47 : ZMod 40156716601) ^ 72087 := by rw [pow_add]
          _ = 12821915818 := by rw [factor_6_16]; decide
      have factor_6_18 : (47 : ZMod 40156716601) ^ 288349 = 33181721708 := by
        calc
          (47 : ZMod 40156716601) ^ 288349 = (47 : ZMod 40156716601) ^ (144174 + 144174 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 144174 * (47 : ZMod 40156716601) ^ 144174) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 33181721708 := by rw [factor_6_17]; decide
      have factor_6_19 : (47 : ZMod 40156716601) ^ 576699 = 2712498850 := by
        calc
          (47 : ZMod 40156716601) ^ 576699 = (47 : ZMod 40156716601) ^ (288349 + 288349 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 288349 * (47 : ZMod 40156716601) ^ 288349) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 2712498850 := by rw [factor_6_18]; decide
      have factor_6_20 : (47 : ZMod 40156716601) ^ 1153398 = 23406525504 := by
        calc
          (47 : ZMod 40156716601) ^ 1153398 = (47 : ZMod 40156716601) ^ (576699 + 576699) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 576699 * (47 : ZMod 40156716601) ^ 576699 := by rw [pow_add]
          _ = 23406525504 := by rw [factor_6_19]; decide
      have factor_6_21 : (47 : ZMod 40156716601) ^ 2306796 = 11537875744 := by
        calc
          (47 : ZMod 40156716601) ^ 2306796 = (47 : ZMod 40156716601) ^ (1153398 + 1153398) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 1153398 * (47 : ZMod 40156716601) ^ 1153398 := by rw [pow_add]
          _ = 11537875744 := by rw [factor_6_20]; decide
      have factor_6_22 : (47 : ZMod 40156716601) ^ 4613593 = 1676487776 := by
        calc
          (47 : ZMod 40156716601) ^ 4613593 = (47 : ZMod 40156716601) ^ (2306796 + 2306796 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 2306796 * (47 : ZMod 40156716601) ^ 2306796) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 1676487776 := by rw [factor_6_21]; decide
      have factor_6_23 : (47 : ZMod 40156716601) ^ 9227186 = 21740405914 := by
        calc
          (47 : ZMod 40156716601) ^ 9227186 = (47 : ZMod 40156716601) ^ (4613593 + 4613593) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 4613593 * (47 : ZMod 40156716601) ^ 4613593 := by rw [pow_add]
          _ = 21740405914 := by rw [factor_6_22]; decide
      have factor_6_24 : (47 : ZMod 40156716601) ^ 18454373 = 27720285878 := by
        calc
          (47 : ZMod 40156716601) ^ 18454373 = (47 : ZMod 40156716601) ^ (9227186 + 9227186 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 9227186 * (47 : ZMod 40156716601) ^ 9227186) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 27720285878 := by rw [factor_6_23]; decide
      have factor_6_25 : (47 : ZMod 40156716601) ^ 36908746 = 37139173070 := by
        calc
          (47 : ZMod 40156716601) ^ 36908746 = (47 : ZMod 40156716601) ^ (18454373 + 18454373) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 18454373 * (47 : ZMod 40156716601) ^ 18454373 := by rw [pow_add]
          _ = 37139173070 := by rw [factor_6_24]; decide
      have factor_6_26 : (47 : ZMod 40156716601) ^ 73817493 = 14020743391 := by
        calc
          (47 : ZMod 40156716601) ^ 73817493 = (47 : ZMod 40156716601) ^ (36908746 + 36908746 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 36908746 * (47 : ZMod 40156716601) ^ 36908746) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 14020743391 := by rw [factor_6_25]; decide
      have factor_6_27 : (47 : ZMod 40156716601) ^ 147634987 = 21003687112 := by
        calc
          (47 : ZMod 40156716601) ^ 147634987 = (47 : ZMod 40156716601) ^ (73817493 + 73817493 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 73817493 * (47 : ZMod 40156716601) ^ 73817493) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 21003687112 := by rw [factor_6_26]; decide
      have factor_6_28 : (47 : ZMod 40156716601) ^ 295269975 = 34958095241 := by
        calc
          (47 : ZMod 40156716601) ^ 295269975 = (47 : ZMod 40156716601) ^ (147634987 + 147634987 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 147634987 * (47 : ZMod 40156716601) ^ 147634987) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 34958095241 := by rw [factor_6_27]; decide
      have factor_6_29 : (47 : ZMod 40156716601) ^ 590539950 = 16017649775 := by
        calc
          (47 : ZMod 40156716601) ^ 590539950 = (47 : ZMod 40156716601) ^ (295269975 + 295269975) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 295269975 * (47 : ZMod 40156716601) ^ 295269975 := by rw [pow_add]
          _ = 16017649775 := by rw [factor_6_28]; decide
      have factor_6_30 : (47 : ZMod 40156716601) ^ 1181079900 = 37221183152 := by
        calc
          (47 : ZMod 40156716601) ^ 1181079900 = (47 : ZMod 40156716601) ^ (590539950 + 590539950) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 590539950 * (47 : ZMod 40156716601) ^ 590539950 := by rw [pow_add]
          _ = 37221183152 := by rw [factor_6_29]; decide
      have factor_6_31 : (47 : ZMod 40156716601) ^ 2362159800 = 40034936244 := by
        calc
          (47 : ZMod 40156716601) ^ 2362159800 = (47 : ZMod 40156716601) ^ (1181079900 + 1181079900) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 1181079900 * (47 : ZMod 40156716601) ^ 1181079900 := by rw [pow_add]
          _ = 40034936244 := by rw [factor_6_30]; decide
      change (47 : ZMod 40156716601) ^ 2362159800 ≠ 1
      rw [factor_6_31]
      decide
    ·
      have factor_7_0 : (47 : ZMod 40156716601) ^ 1 = 47 := by norm_num
      have factor_7_1 : (47 : ZMod 40156716601) ^ 3 = 103823 := by
        calc
          (47 : ZMod 40156716601) ^ 3 = (47 : ZMod 40156716601) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 1 * (47 : ZMod 40156716601) ^ 1) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 103823 := by rw [factor_7_0]; decide
      have factor_7_2 : (47 : ZMod 40156716601) ^ 7 = 24742521251 := by
        calc
          (47 : ZMod 40156716601) ^ 7 = (47 : ZMod 40156716601) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 3 * (47 : ZMod 40156716601) ^ 3) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 24742521251 := by rw [factor_7_1]; decide
      have factor_7_3 : (47 : ZMod 40156716601) ^ 15 = 5745964985 := by
        calc
          (47 : ZMod 40156716601) ^ 15 = (47 : ZMod 40156716601) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 7 * (47 : ZMod 40156716601) ^ 7) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 5745964985 := by rw [factor_7_2]; decide
      have factor_7_4 : (47 : ZMod 40156716601) ^ 31 = 26391513255 := by
        calc
          (47 : ZMod 40156716601) ^ 31 = (47 : ZMod 40156716601) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 15 * (47 : ZMod 40156716601) ^ 15) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 26391513255 := by rw [factor_7_3]; decide
      have factor_7_5 : (47 : ZMod 40156716601) ^ 62 = 23531779552 := by
        calc
          (47 : ZMod 40156716601) ^ 62 = (47 : ZMod 40156716601) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 31 * (47 : ZMod 40156716601) ^ 31 := by rw [pow_add]
          _ = 23531779552 := by rw [factor_7_4]; decide
      have factor_7_6 : (47 : ZMod 40156716601) ^ 125 = 39718450777 := by
        calc
          (47 : ZMod 40156716601) ^ 125 = (47 : ZMod 40156716601) ^ (62 + 62 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 62 * (47 : ZMod 40156716601) ^ 62) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 39718450777 := by rw [factor_7_5]; decide
      have factor_7_7 : (47 : ZMod 40156716601) ^ 251 = 28909416262 := by
        calc
          (47 : ZMod 40156716601) ^ 251 = (47 : ZMod 40156716601) ^ (125 + 125 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 125 * (47 : ZMod 40156716601) ^ 125) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 28909416262 := by rw [factor_7_6]; decide
      have factor_7_8 : (47 : ZMod 40156716601) ^ 503 = 11023097209 := by
        calc
          (47 : ZMod 40156716601) ^ 503 = (47 : ZMod 40156716601) ^ (251 + 251 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 251 * (47 : ZMod 40156716601) ^ 251) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 11023097209 := by rw [factor_7_7]; decide
      have factor_7_9 : (47 : ZMod 40156716601) ^ 1007 = 331159764 := by
        calc
          (47 : ZMod 40156716601) ^ 1007 = (47 : ZMod 40156716601) ^ (503 + 503 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 503 * (47 : ZMod 40156716601) ^ 503) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 331159764 := by rw [factor_7_8]; decide
      have factor_7_10 : (47 : ZMod 40156716601) ^ 2015 = 4808311521 := by
        calc
          (47 : ZMod 40156716601) ^ 2015 = (47 : ZMod 40156716601) ^ (1007 + 1007 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 1007 * (47 : ZMod 40156716601) ^ 1007) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 4808311521 := by rw [factor_7_9]; decide
      have factor_7_11 : (47 : ZMod 40156716601) ^ 4031 = 26327508864 := by
        calc
          (47 : ZMod 40156716601) ^ 4031 = (47 : ZMod 40156716601) ^ (2015 + 2015 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 2015 * (47 : ZMod 40156716601) ^ 2015) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 26327508864 := by rw [factor_7_10]; decide
      have factor_7_12 : (47 : ZMod 40156716601) ^ 8062 = 26402481235 := by
        calc
          (47 : ZMod 40156716601) ^ 8062 = (47 : ZMod 40156716601) ^ (4031 + 4031) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 4031 * (47 : ZMod 40156716601) ^ 4031 := by rw [pow_add]
          _ = 26402481235 := by rw [factor_7_11]; decide
      have factor_7_13 : (47 : ZMod 40156716601) ^ 16124 = 29772162960 := by
        calc
          (47 : ZMod 40156716601) ^ 16124 = (47 : ZMod 40156716601) ^ (8062 + 8062) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 8062 * (47 : ZMod 40156716601) ^ 8062 := by rw [pow_add]
          _ = 29772162960 := by rw [factor_7_12]; decide
      have factor_7_14 : (47 : ZMod 40156716601) ^ 32249 = 20474238086 := by
        calc
          (47 : ZMod 40156716601) ^ 32249 = (47 : ZMod 40156716601) ^ (16124 + 16124 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 16124 * (47 : ZMod 40156716601) ^ 16124) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 20474238086 := by rw [factor_7_13]; decide
      have factor_7_15 : (47 : ZMod 40156716601) ^ 64499 = 6733575943 := by
        calc
          (47 : ZMod 40156716601) ^ 64499 = (47 : ZMod 40156716601) ^ (32249 + 32249 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 32249 * (47 : ZMod 40156716601) ^ 32249) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 6733575943 := by rw [factor_7_14]; decide
      have factor_7_16 : (47 : ZMod 40156716601) ^ 128998 = 10309546652 := by
        calc
          (47 : ZMod 40156716601) ^ 128998 = (47 : ZMod 40156716601) ^ (64499 + 64499) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 64499 * (47 : ZMod 40156716601) ^ 64499 := by rw [pow_add]
          _ = 10309546652 := by rw [factor_7_15]; decide
      have factor_7_17 : (47 : ZMod 40156716601) ^ 257996 = 7170651633 := by
        calc
          (47 : ZMod 40156716601) ^ 257996 = (47 : ZMod 40156716601) ^ (128998 + 128998) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 128998 * (47 : ZMod 40156716601) ^ 128998 := by rw [pow_add]
          _ = 7170651633 := by rw [factor_7_16]; decide
      have factor_7_18 : (47 : ZMod 40156716601) ^ 515993 = 29814845787 := by
        calc
          (47 : ZMod 40156716601) ^ 515993 = (47 : ZMod 40156716601) ^ (257996 + 257996 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 257996 * (47 : ZMod 40156716601) ^ 257996) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 29814845787 := by rw [factor_7_17]; decide
      have factor_7_19 : (47 : ZMod 40156716601) ^ 1031987 = 37379540705 := by
        calc
          (47 : ZMod 40156716601) ^ 1031987 = (47 : ZMod 40156716601) ^ (515993 + 515993 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 515993 * (47 : ZMod 40156716601) ^ 515993) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 37379540705 := by rw [factor_7_18]; decide
      have factor_7_20 : (47 : ZMod 40156716601) ^ 2063975 = 3401835915 := by
        calc
          (47 : ZMod 40156716601) ^ 2063975 = (47 : ZMod 40156716601) ^ (1031987 + 1031987 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 1031987 * (47 : ZMod 40156716601) ^ 1031987) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 3401835915 := by rw [factor_7_19]; decide
      have factor_7_21 : (47 : ZMod 40156716601) ^ 4127951 = 29596646871 := by
        calc
          (47 : ZMod 40156716601) ^ 4127951 = (47 : ZMod 40156716601) ^ (2063975 + 2063975 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 2063975 * (47 : ZMod 40156716601) ^ 2063975) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 29596646871 := by rw [factor_7_20]; decide
      have factor_7_22 : (47 : ZMod 40156716601) ^ 8255903 = 6201205433 := by
        calc
          (47 : ZMod 40156716601) ^ 8255903 = (47 : ZMod 40156716601) ^ (4127951 + 4127951 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 4127951 * (47 : ZMod 40156716601) ^ 4127951) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 6201205433 := by rw [factor_7_21]; decide
      have factor_7_23 : (47 : ZMod 40156716601) ^ 16511807 = 18936976124 := by
        calc
          (47 : ZMod 40156716601) ^ 16511807 = (47 : ZMod 40156716601) ^ (8255903 + 8255903 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 8255903 * (47 : ZMod 40156716601) ^ 8255903) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 18936976124 := by rw [factor_7_22]; decide
      have factor_7_24 : (47 : ZMod 40156716601) ^ 33023615 = 38969558096 := by
        calc
          (47 : ZMod 40156716601) ^ 33023615 = (47 : ZMod 40156716601) ^ (16511807 + 16511807 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 16511807 * (47 : ZMod 40156716601) ^ 16511807) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 38969558096 := by rw [factor_7_23]; decide
      have factor_7_25 : (47 : ZMod 40156716601) ^ 66047231 = 25864899701 := by
        calc
          (47 : ZMod 40156716601) ^ 66047231 = (47 : ZMod 40156716601) ^ (33023615 + 33023615 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 33023615 * (47 : ZMod 40156716601) ^ 33023615) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 25864899701 := by rw [factor_7_24]; decide
      have factor_7_26 : (47 : ZMod 40156716601) ^ 132094462 = 39084463610 := by
        calc
          (47 : ZMod 40156716601) ^ 132094462 = (47 : ZMod 40156716601) ^ (66047231 + 66047231) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 66047231 * (47 : ZMod 40156716601) ^ 66047231 := by rw [pow_add]
          _ = 39084463610 := by rw [factor_7_25]; decide
      have factor_7_27 : (47 : ZMod 40156716601) ^ 264188925 = 21592972165 := by
        calc
          (47 : ZMod 40156716601) ^ 264188925 = (47 : ZMod 40156716601) ^ (132094462 + 132094462 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 132094462 * (47 : ZMod 40156716601) ^ 132094462) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 21592972165 := by rw [factor_7_26]; decide
      have factor_7_28 : (47 : ZMod 40156716601) ^ 528377850 = 31939971453 := by
        calc
          (47 : ZMod 40156716601) ^ 528377850 = (47 : ZMod 40156716601) ^ (264188925 + 264188925) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 264188925 * (47 : ZMod 40156716601) ^ 264188925 := by rw [pow_add]
          _ = 31939971453 := by rw [factor_7_27]; decide
      have factor_7_29 : (47 : ZMod 40156716601) ^ 1056755700 = 16019932317 := by
        calc
          (47 : ZMod 40156716601) ^ 1056755700 = (47 : ZMod 40156716601) ^ (528377850 + 528377850) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 528377850 * (47 : ZMod 40156716601) ^ 528377850 := by rw [pow_add]
          _ = 16019932317 := by rw [factor_7_28]; decide
      have factor_7_30 : (47 : ZMod 40156716601) ^ 2113511400 = 16098669572 := by
        calc
          (47 : ZMod 40156716601) ^ 2113511400 = (47 : ZMod 40156716601) ^ (1056755700 + 1056755700) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 1056755700 * (47 : ZMod 40156716601) ^ 1056755700 := by rw [pow_add]
          _ = 16098669572 := by rw [factor_7_29]; decide
      change (47 : ZMod 40156716601) ^ 2113511400 ≠ 1
      rw [factor_7_30]
      decide
    ·
      have factor_8_0 : (47 : ZMod 40156716601) ^ 1 = 47 := by norm_num
      have factor_8_1 : (47 : ZMod 40156716601) ^ 3 = 103823 := by
        calc
          (47 : ZMod 40156716601) ^ 3 = (47 : ZMod 40156716601) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 1 * (47 : ZMod 40156716601) ^ 1) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 103823 := by rw [factor_8_0]; decide
      have factor_8_2 : (47 : ZMod 40156716601) ^ 6 = 10779215329 := by
        calc
          (47 : ZMod 40156716601) ^ 6 = (47 : ZMod 40156716601) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 3 * (47 : ZMod 40156716601) ^ 3 := by rw [pow_add]
          _ = 10779215329 := by rw [factor_8_1]; decide
      have factor_8_3 : (47 : ZMod 40156716601) ^ 13 = 39595778507 := by
        calc
          (47 : ZMod 40156716601) ^ 13 = (47 : ZMod 40156716601) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 6 * (47 : ZMod 40156716601) ^ 6) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 39595778507 := by rw [factor_8_2]; decide
      have factor_8_4 : (47 : ZMod 40156716601) ^ 26 = 18425439847 := by
        calc
          (47 : ZMod 40156716601) ^ 26 = (47 : ZMod 40156716601) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 13 * (47 : ZMod 40156716601) ^ 13 := by rw [pow_add]
          _ = 18425439847 := by rw [factor_8_3]; decide
      have factor_8_5 : (47 : ZMod 40156716601) ^ 52 = 8723310390 := by
        calc
          (47 : ZMod 40156716601) ^ 52 = (47 : ZMod 40156716601) ^ (26 + 26) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 26 * (47 : ZMod 40156716601) ^ 26 := by rw [pow_add]
          _ = 8723310390 := by rw [factor_8_4]; decide
      have factor_8_6 : (47 : ZMod 40156716601) ^ 104 = 15450455264 := by
        calc
          (47 : ZMod 40156716601) ^ 104 = (47 : ZMod 40156716601) ^ (52 + 52) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 52 * (47 : ZMod 40156716601) ^ 52 := by rw [pow_add]
          _ = 15450455264 := by rw [factor_8_5]; decide
      have factor_8_7 : (47 : ZMod 40156716601) ^ 208 = 9705630430 := by
        calc
          (47 : ZMod 40156716601) ^ 208 = (47 : ZMod 40156716601) ^ (104 + 104) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 104 * (47 : ZMod 40156716601) ^ 104 := by rw [pow_add]
          _ = 9705630430 := by rw [factor_8_6]; decide
      have factor_8_8 : (47 : ZMod 40156716601) ^ 416 = 20811873359 := by
        calc
          (47 : ZMod 40156716601) ^ 416 = (47 : ZMod 40156716601) ^ (208 + 208) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 208 * (47 : ZMod 40156716601) ^ 208 := by rw [pow_add]
          _ = 20811873359 := by rw [factor_8_7]; decide
      have factor_8_9 : (47 : ZMod 40156716601) ^ 832 = 25919604859 := by
        calc
          (47 : ZMod 40156716601) ^ 832 = (47 : ZMod 40156716601) ^ (416 + 416) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 416 * (47 : ZMod 40156716601) ^ 416 := by rw [pow_add]
          _ = 25919604859 := by rw [factor_8_8]; decide
      have factor_8_10 : (47 : ZMod 40156716601) ^ 1665 = 10867396175 := by
        calc
          (47 : ZMod 40156716601) ^ 1665 = (47 : ZMod 40156716601) ^ (832 + 832 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 832 * (47 : ZMod 40156716601) ^ 832) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 10867396175 := by rw [factor_8_9]; decide
      have factor_8_11 : (47 : ZMod 40156716601) ^ 3330 = 17724593064 := by
        calc
          (47 : ZMod 40156716601) ^ 3330 = (47 : ZMod 40156716601) ^ (1665 + 1665) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 1665 * (47 : ZMod 40156716601) ^ 1665 := by rw [pow_add]
          _ = 17724593064 := by rw [factor_8_10]; decide
      have factor_8_12 : (47 : ZMod 40156716601) ^ 6660 = 14189656047 := by
        calc
          (47 : ZMod 40156716601) ^ 6660 = (47 : ZMod 40156716601) ^ (3330 + 3330) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 3330 * (47 : ZMod 40156716601) ^ 3330 := by rw [pow_add]
          _ = 14189656047 := by rw [factor_8_11]; decide
      have factor_8_13 : (47 : ZMod 40156716601) ^ 13320 = 22754568022 := by
        calc
          (47 : ZMod 40156716601) ^ 13320 = (47 : ZMod 40156716601) ^ (6660 + 6660) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 6660 * (47 : ZMod 40156716601) ^ 6660 := by rw [pow_add]
          _ = 22754568022 := by rw [factor_8_12]; decide
      have factor_8_14 : (47 : ZMod 40156716601) ^ 26640 = 39966187126 := by
        calc
          (47 : ZMod 40156716601) ^ 26640 = (47 : ZMod 40156716601) ^ (13320 + 13320) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 13320 * (47 : ZMod 40156716601) ^ 13320 := by rw [pow_add]
          _ = 39966187126 := by rw [factor_8_13]; decide
      have factor_8_15 : (47 : ZMod 40156716601) ^ 53281 = 19818684999 := by
        calc
          (47 : ZMod 40156716601) ^ 53281 = (47 : ZMod 40156716601) ^ (26640 + 26640 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 26640 * (47 : ZMod 40156716601) ^ 26640) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 19818684999 := by rw [factor_8_14]; decide
      have factor_8_16 : (47 : ZMod 40156716601) ^ 106563 = 36432860251 := by
        calc
          (47 : ZMod 40156716601) ^ 106563 = (47 : ZMod 40156716601) ^ (53281 + 53281 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 53281 * (47 : ZMod 40156716601) ^ 53281) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 36432860251 := by rw [factor_8_15]; decide
      have factor_8_17 : (47 : ZMod 40156716601) ^ 213127 = 23555523398 := by
        calc
          (47 : ZMod 40156716601) ^ 213127 = (47 : ZMod 40156716601) ^ (106563 + 106563 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 106563 * (47 : ZMod 40156716601) ^ 106563) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 23555523398 := by rw [factor_8_16]; decide
      have factor_8_18 : (47 : ZMod 40156716601) ^ 426255 = 17868000952 := by
        calc
          (47 : ZMod 40156716601) ^ 426255 = (47 : ZMod 40156716601) ^ (213127 + 213127 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 213127 * (47 : ZMod 40156716601) ^ 213127) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 17868000952 := by rw [factor_8_17]; decide
      have factor_8_19 : (47 : ZMod 40156716601) ^ 852511 = 15680370162 := by
        calc
          (47 : ZMod 40156716601) ^ 852511 = (47 : ZMod 40156716601) ^ (426255 + 426255 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 426255 * (47 : ZMod 40156716601) ^ 426255) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 15680370162 := by rw [factor_8_18]; decide
      have factor_8_20 : (47 : ZMod 40156716601) ^ 1705023 = 1130903952 := by
        calc
          (47 : ZMod 40156716601) ^ 1705023 = (47 : ZMod 40156716601) ^ (852511 + 852511 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 852511 * (47 : ZMod 40156716601) ^ 852511) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 1130903952 := by rw [factor_8_19]; decide
      have factor_8_21 : (47 : ZMod 40156716601) ^ 3410047 = 15432646088 := by
        calc
          (47 : ZMod 40156716601) ^ 3410047 = (47 : ZMod 40156716601) ^ (1705023 + 1705023 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 1705023 * (47 : ZMod 40156716601) ^ 1705023) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 15432646088 := by rw [factor_8_20]; decide
      have factor_8_22 : (47 : ZMod 40156716601) ^ 6820094 = 36182827282 := by
        calc
          (47 : ZMod 40156716601) ^ 6820094 = (47 : ZMod 40156716601) ^ (3410047 + 3410047) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 3410047 * (47 : ZMod 40156716601) ^ 3410047 := by rw [pow_add]
          _ = 36182827282 := by rw [factor_8_21]; decide
      have factor_8_23 : (47 : ZMod 40156716601) ^ 13640189 = 20667644904 := by
        calc
          (47 : ZMod 40156716601) ^ 13640189 = (47 : ZMod 40156716601) ^ (6820094 + 6820094 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 6820094 * (47 : ZMod 40156716601) ^ 6820094) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 20667644904 := by rw [factor_8_22]; decide
      have factor_8_24 : (47 : ZMod 40156716601) ^ 27280378 = 30740611876 := by
        calc
          (47 : ZMod 40156716601) ^ 27280378 = (47 : ZMod 40156716601) ^ (13640189 + 13640189) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 13640189 * (47 : ZMod 40156716601) ^ 13640189 := by rw [pow_add]
          _ = 30740611876 := by rw [factor_8_23]; decide
      have factor_8_25 : (47 : ZMod 40156716601) ^ 54560756 = 13135699784 := by
        calc
          (47 : ZMod 40156716601) ^ 54560756 = (47 : ZMod 40156716601) ^ (27280378 + 27280378) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 27280378 * (47 : ZMod 40156716601) ^ 27280378 := by rw [pow_add]
          _ = 13135699784 := by rw [factor_8_24]; decide
      have factor_8_26 : (47 : ZMod 40156716601) ^ 109121512 = 8202706253 := by
        calc
          (47 : ZMod 40156716601) ^ 109121512 = (47 : ZMod 40156716601) ^ (54560756 + 54560756) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 54560756 * (47 : ZMod 40156716601) ^ 54560756 := by rw [pow_add]
          _ = 8202706253 := by rw [factor_8_25]; decide
      have factor_8_27 : (47 : ZMod 40156716601) ^ 218243025 = 39676654760 := by
        calc
          (47 : ZMod 40156716601) ^ 218243025 = (47 : ZMod 40156716601) ^ (109121512 + 109121512 + 1) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = ((47 : ZMod 40156716601) ^ 109121512 * (47 : ZMod 40156716601) ^ 109121512) * (47 : ZMod 40156716601) := by rw [pow_succ, pow_add]
          _ = 39676654760 := by rw [factor_8_26]; decide
      have factor_8_28 : (47 : ZMod 40156716601) ^ 436486050 = 14767886882 := by
        calc
          (47 : ZMod 40156716601) ^ 436486050 = (47 : ZMod 40156716601) ^ (218243025 + 218243025) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 218243025 * (47 : ZMod 40156716601) ^ 218243025 := by rw [pow_add]
          _ = 14767886882 := by rw [factor_8_27]; decide
      have factor_8_29 : (47 : ZMod 40156716601) ^ 872972100 = 16385293984 := by
        calc
          (47 : ZMod 40156716601) ^ 872972100 = (47 : ZMod 40156716601) ^ (436486050 + 436486050) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 436486050 * (47 : ZMod 40156716601) ^ 436486050 := by rw [pow_add]
          _ = 16385293984 := by rw [factor_8_28]; decide
      have factor_8_30 : (47 : ZMod 40156716601) ^ 1745944200 = 12164457592 := by
        calc
          (47 : ZMod 40156716601) ^ 1745944200 = (47 : ZMod 40156716601) ^ (872972100 + 872972100) :=
            congrArg (fun n : ℕ => (47 : ZMod 40156716601) ^ n) (by norm_num)
          _ = (47 : ZMod 40156716601) ^ 872972100 * (47 : ZMod 40156716601) ^ 872972100 := by rw [pow_add]
          _ = 12164457592 := by rw [factor_8_29]; decide
      change (47 : ZMod 40156716601) ^ 1745944200 ≠ 1
      rw [factor_8_30]
      decide

#print axioms prime_lucas_40156716601

end TotientTailPeriodKiller
end Erdos249257
