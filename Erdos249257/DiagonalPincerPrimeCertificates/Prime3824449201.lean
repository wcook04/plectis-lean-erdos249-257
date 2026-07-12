import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=25 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_3824449201 : Nat.Prime 3824449201 := by
  apply lucas_primality 3824449201 (7 : ZMod 3824449201)
  ·
      have fermat_0 : (7 : ZMod 3824449201) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 3824449201) ^ 3 = 343 := by
        calc
          (7 : ZMod 3824449201) ^ 3 = (7 : ZMod 3824449201) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 1 * (7 : ZMod 3824449201) ^ 1) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 3824449201) ^ 7 = 823543 := by
        calc
          (7 : ZMod 3824449201) ^ 7 = (7 : ZMod 3824449201) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 3 * (7 : ZMod 3824449201) ^ 3) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 3824449201) ^ 14 = 1295564272 := by
        calc
          (7 : ZMod 3824449201) ^ 14 = (7 : ZMod 3824449201) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 7 * (7 : ZMod 3824449201) ^ 7 := by rw [pow_add]
          _ = 1295564272 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 3824449201) ^ 28 = 125775111 := by
        calc
          (7 : ZMod 3824449201) ^ 28 = (7 : ZMod 3824449201) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 14 * (7 : ZMod 3824449201) ^ 14 := by rw [pow_add]
          _ = 125775111 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 3824449201) ^ 56 = 3361029941 := by
        calc
          (7 : ZMod 3824449201) ^ 56 = (7 : ZMod 3824449201) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 28 * (7 : ZMod 3824449201) ^ 28 := by rw [pow_add]
          _ = 3361029941 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 3824449201) ^ 113 = 2525916500 := by
        calc
          (7 : ZMod 3824449201) ^ 113 = (7 : ZMod 3824449201) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 56 * (7 : ZMod 3824449201) ^ 56) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 2525916500 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 3824449201) ^ 227 = 2689040245 := by
        calc
          (7 : ZMod 3824449201) ^ 227 = (7 : ZMod 3824449201) ^ (113 + 113 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 113 * (7 : ZMod 3824449201) ^ 113) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 2689040245 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 3824449201) ^ 455 = 2870243416 := by
        calc
          (7 : ZMod 3824449201) ^ 455 = (7 : ZMod 3824449201) ^ (227 + 227 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 227 * (7 : ZMod 3824449201) ^ 227) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 2870243416 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 3824449201) ^ 911 = 3605732401 := by
        calc
          (7 : ZMod 3824449201) ^ 911 = (7 : ZMod 3824449201) ^ (455 + 455 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 455 * (7 : ZMod 3824449201) ^ 455) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 3605732401 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 3824449201) ^ 1823 = 1932384485 := by
        calc
          (7 : ZMod 3824449201) ^ 1823 = (7 : ZMod 3824449201) ^ (911 + 911 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 911 * (7 : ZMod 3824449201) ^ 911) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1932384485 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 3824449201) ^ 3647 = 988048998 := by
        calc
          (7 : ZMod 3824449201) ^ 3647 = (7 : ZMod 3824449201) ^ (1823 + 1823 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 1823 * (7 : ZMod 3824449201) ^ 1823) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 988048998 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 3824449201) ^ 7294 = 2417833688 := by
        calc
          (7 : ZMod 3824449201) ^ 7294 = (7 : ZMod 3824449201) ^ (3647 + 3647) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 3647 * (7 : ZMod 3824449201) ^ 3647 := by rw [pow_add]
          _ = 2417833688 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 3824449201) ^ 14589 = 1911918202 := by
        calc
          (7 : ZMod 3824449201) ^ 14589 = (7 : ZMod 3824449201) ^ (7294 + 7294 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 7294 * (7 : ZMod 3824449201) ^ 7294) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1911918202 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 3824449201) ^ 29178 = 1137147678 := by
        calc
          (7 : ZMod 3824449201) ^ 29178 = (7 : ZMod 3824449201) ^ (14589 + 14589) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 14589 * (7 : ZMod 3824449201) ^ 14589 := by rw [pow_add]
          _ = 1137147678 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 3824449201) ^ 58356 = 2932076771 := by
        calc
          (7 : ZMod 3824449201) ^ 58356 = (7 : ZMod 3824449201) ^ (29178 + 29178) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 29178 * (7 : ZMod 3824449201) ^ 29178 := by rw [pow_add]
          _ = 2932076771 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 3824449201) ^ 116712 = 1067498445 := by
        calc
          (7 : ZMod 3824449201) ^ 116712 = (7 : ZMod 3824449201) ^ (58356 + 58356) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 58356 * (7 : ZMod 3824449201) ^ 58356 := by rw [pow_add]
          _ = 1067498445 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 3824449201) ^ 233425 = 166572284 := by
        calc
          (7 : ZMod 3824449201) ^ 233425 = (7 : ZMod 3824449201) ^ (116712 + 116712 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 116712 * (7 : ZMod 3824449201) ^ 116712) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 166572284 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 3824449201) ^ 466851 = 2702073290 := by
        calc
          (7 : ZMod 3824449201) ^ 466851 = (7 : ZMod 3824449201) ^ (233425 + 233425 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 233425 * (7 : ZMod 3824449201) ^ 233425) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 2702073290 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 3824449201) ^ 933703 = 1080761025 := by
        calc
          (7 : ZMod 3824449201) ^ 933703 = (7 : ZMod 3824449201) ^ (466851 + 466851 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 466851 * (7 : ZMod 3824449201) ^ 466851) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1080761025 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 3824449201) ^ 1867406 = 3319785163 := by
        calc
          (7 : ZMod 3824449201) ^ 1867406 = (7 : ZMod 3824449201) ^ (933703 + 933703) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 933703 * (7 : ZMod 3824449201) ^ 933703 := by rw [pow_add]
          _ = 3319785163 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 3824449201) ^ 3734813 = 3287615338 := by
        calc
          (7 : ZMod 3824449201) ^ 3734813 = (7 : ZMod 3824449201) ^ (1867406 + 1867406 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 1867406 * (7 : ZMod 3824449201) ^ 1867406) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 3287615338 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 3824449201) ^ 7469627 = 50653798 := by
        calc
          (7 : ZMod 3824449201) ^ 7469627 = (7 : ZMod 3824449201) ^ (3734813 + 3734813 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 3734813 * (7 : ZMod 3824449201) ^ 3734813) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 50653798 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 3824449201) ^ 14939254 = 3405119909 := by
        calc
          (7 : ZMod 3824449201) ^ 14939254 = (7 : ZMod 3824449201) ^ (7469627 + 7469627) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 7469627 * (7 : ZMod 3824449201) ^ 7469627 := by rw [pow_add]
          _ = 3405119909 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 3824449201) ^ 29878509 = 1260827600 := by
        calc
          (7 : ZMod 3824449201) ^ 29878509 = (7 : ZMod 3824449201) ^ (14939254 + 14939254 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 14939254 * (7 : ZMod 3824449201) ^ 14939254) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1260827600 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 3824449201) ^ 59757018 = 1792375900 := by
        calc
          (7 : ZMod 3824449201) ^ 59757018 = (7 : ZMod 3824449201) ^ (29878509 + 29878509) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 29878509 * (7 : ZMod 3824449201) ^ 29878509 := by rw [pow_add]
          _ = 1792375900 := by rw [fermat_24]; decide
      have fermat_26 : (7 : ZMod 3824449201) ^ 119514037 = 16645686 := by
        calc
          (7 : ZMod 3824449201) ^ 119514037 = (7 : ZMod 3824449201) ^ (59757018 + 59757018 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 59757018 * (7 : ZMod 3824449201) ^ 59757018) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 16645686 := by rw [fermat_25]; decide
      have fermat_27 : (7 : ZMod 3824449201) ^ 239028075 = 1746833027 := by
        calc
          (7 : ZMod 3824449201) ^ 239028075 = (7 : ZMod 3824449201) ^ (119514037 + 119514037 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 119514037 * (7 : ZMod 3824449201) ^ 119514037) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1746833027 := by rw [fermat_26]; decide
      have fermat_28 : (7 : ZMod 3824449201) ^ 478056150 = 2542990303 := by
        calc
          (7 : ZMod 3824449201) ^ 478056150 = (7 : ZMod 3824449201) ^ (239028075 + 239028075) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 239028075 * (7 : ZMod 3824449201) ^ 239028075 := by rw [pow_add]
          _ = 2542990303 := by rw [fermat_27]; decide
      have fermat_29 : (7 : ZMod 3824449201) ^ 956112300 = 3504330136 := by
        calc
          (7 : ZMod 3824449201) ^ 956112300 = (7 : ZMod 3824449201) ^ (478056150 + 478056150) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 478056150 * (7 : ZMod 3824449201) ^ 478056150 := by rw [pow_add]
          _ = 3504330136 := by rw [fermat_28]; decide
      have fermat_30 : (7 : ZMod 3824449201) ^ 1912224600 = 3824449200 := by
        calc
          (7 : ZMod 3824449201) ^ 1912224600 = (7 : ZMod 3824449201) ^ (956112300 + 956112300) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 956112300 * (7 : ZMod 3824449201) ^ 956112300 := by rw [pow_add]
          _ = 3824449200 := by rw [fermat_29]; decide
      have fermat_31 : (7 : ZMod 3824449201) ^ 3824449200 = 1 := by
        calc
          (7 : ZMod 3824449201) ^ 3824449200 = (7 : ZMod 3824449201) ^ (1912224600 + 1912224600) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 1912224600 * (7 : ZMod 3824449201) ^ 1912224600 := by rw [pow_add]
          _ = 1 := by rw [fermat_30]; decide
      simpa using fermat_31
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (5, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (5, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod = 3824449201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 3824449201) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 3824449201) ^ 3 = 343 := by
        calc
          (7 : ZMod 3824449201) ^ 3 = (7 : ZMod 3824449201) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 1 * (7 : ZMod 3824449201) ^ 1) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 3824449201) ^ 7 = 823543 := by
        calc
          (7 : ZMod 3824449201) ^ 7 = (7 : ZMod 3824449201) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 3 * (7 : ZMod 3824449201) ^ 3) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 3824449201) ^ 14 = 1295564272 := by
        calc
          (7 : ZMod 3824449201) ^ 14 = (7 : ZMod 3824449201) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 7 * (7 : ZMod 3824449201) ^ 7 := by rw [pow_add]
          _ = 1295564272 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 3824449201) ^ 28 = 125775111 := by
        calc
          (7 : ZMod 3824449201) ^ 28 = (7 : ZMod 3824449201) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 14 * (7 : ZMod 3824449201) ^ 14 := by rw [pow_add]
          _ = 125775111 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 3824449201) ^ 56 = 3361029941 := by
        calc
          (7 : ZMod 3824449201) ^ 56 = (7 : ZMod 3824449201) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 28 * (7 : ZMod 3824449201) ^ 28 := by rw [pow_add]
          _ = 3361029941 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 3824449201) ^ 113 = 2525916500 := by
        calc
          (7 : ZMod 3824449201) ^ 113 = (7 : ZMod 3824449201) ^ (56 + 56 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 56 * (7 : ZMod 3824449201) ^ 56) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 2525916500 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 3824449201) ^ 227 = 2689040245 := by
        calc
          (7 : ZMod 3824449201) ^ 227 = (7 : ZMod 3824449201) ^ (113 + 113 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 113 * (7 : ZMod 3824449201) ^ 113) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 2689040245 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 3824449201) ^ 455 = 2870243416 := by
        calc
          (7 : ZMod 3824449201) ^ 455 = (7 : ZMod 3824449201) ^ (227 + 227 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 227 * (7 : ZMod 3824449201) ^ 227) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 2870243416 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 3824449201) ^ 911 = 3605732401 := by
        calc
          (7 : ZMod 3824449201) ^ 911 = (7 : ZMod 3824449201) ^ (455 + 455 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 455 * (7 : ZMod 3824449201) ^ 455) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 3605732401 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 3824449201) ^ 1823 = 1932384485 := by
        calc
          (7 : ZMod 3824449201) ^ 1823 = (7 : ZMod 3824449201) ^ (911 + 911 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 911 * (7 : ZMod 3824449201) ^ 911) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1932384485 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 3824449201) ^ 3647 = 988048998 := by
        calc
          (7 : ZMod 3824449201) ^ 3647 = (7 : ZMod 3824449201) ^ (1823 + 1823 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 1823 * (7 : ZMod 3824449201) ^ 1823) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 988048998 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 3824449201) ^ 7294 = 2417833688 := by
        calc
          (7 : ZMod 3824449201) ^ 7294 = (7 : ZMod 3824449201) ^ (3647 + 3647) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 3647 * (7 : ZMod 3824449201) ^ 3647 := by rw [pow_add]
          _ = 2417833688 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 3824449201) ^ 14589 = 1911918202 := by
        calc
          (7 : ZMod 3824449201) ^ 14589 = (7 : ZMod 3824449201) ^ (7294 + 7294 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 7294 * (7 : ZMod 3824449201) ^ 7294) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1911918202 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 3824449201) ^ 29178 = 1137147678 := by
        calc
          (7 : ZMod 3824449201) ^ 29178 = (7 : ZMod 3824449201) ^ (14589 + 14589) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 14589 * (7 : ZMod 3824449201) ^ 14589 := by rw [pow_add]
          _ = 1137147678 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 3824449201) ^ 58356 = 2932076771 := by
        calc
          (7 : ZMod 3824449201) ^ 58356 = (7 : ZMod 3824449201) ^ (29178 + 29178) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 29178 * (7 : ZMod 3824449201) ^ 29178 := by rw [pow_add]
          _ = 2932076771 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 3824449201) ^ 116712 = 1067498445 := by
        calc
          (7 : ZMod 3824449201) ^ 116712 = (7 : ZMod 3824449201) ^ (58356 + 58356) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 58356 * (7 : ZMod 3824449201) ^ 58356 := by rw [pow_add]
          _ = 1067498445 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 3824449201) ^ 233425 = 166572284 := by
        calc
          (7 : ZMod 3824449201) ^ 233425 = (7 : ZMod 3824449201) ^ (116712 + 116712 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 116712 * (7 : ZMod 3824449201) ^ 116712) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 166572284 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 3824449201) ^ 466851 = 2702073290 := by
        calc
          (7 : ZMod 3824449201) ^ 466851 = (7 : ZMod 3824449201) ^ (233425 + 233425 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 233425 * (7 : ZMod 3824449201) ^ 233425) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 2702073290 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 3824449201) ^ 933703 = 1080761025 := by
        calc
          (7 : ZMod 3824449201) ^ 933703 = (7 : ZMod 3824449201) ^ (466851 + 466851 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 466851 * (7 : ZMod 3824449201) ^ 466851) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1080761025 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 3824449201) ^ 1867406 = 3319785163 := by
        calc
          (7 : ZMod 3824449201) ^ 1867406 = (7 : ZMod 3824449201) ^ (933703 + 933703) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 933703 * (7 : ZMod 3824449201) ^ 933703 := by rw [pow_add]
          _ = 3319785163 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 3824449201) ^ 3734813 = 3287615338 := by
        calc
          (7 : ZMod 3824449201) ^ 3734813 = (7 : ZMod 3824449201) ^ (1867406 + 1867406 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 1867406 * (7 : ZMod 3824449201) ^ 1867406) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 3287615338 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 3824449201) ^ 7469627 = 50653798 := by
        calc
          (7 : ZMod 3824449201) ^ 7469627 = (7 : ZMod 3824449201) ^ (3734813 + 3734813 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 3734813 * (7 : ZMod 3824449201) ^ 3734813) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 50653798 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 3824449201) ^ 14939254 = 3405119909 := by
        calc
          (7 : ZMod 3824449201) ^ 14939254 = (7 : ZMod 3824449201) ^ (7469627 + 7469627) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 7469627 * (7 : ZMod 3824449201) ^ 7469627 := by rw [pow_add]
          _ = 3405119909 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 3824449201) ^ 29878509 = 1260827600 := by
        calc
          (7 : ZMod 3824449201) ^ 29878509 = (7 : ZMod 3824449201) ^ (14939254 + 14939254 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 14939254 * (7 : ZMod 3824449201) ^ 14939254) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1260827600 := by rw [factor_0_23]; decide
      have factor_0_25 : (7 : ZMod 3824449201) ^ 59757018 = 1792375900 := by
        calc
          (7 : ZMod 3824449201) ^ 59757018 = (7 : ZMod 3824449201) ^ (29878509 + 29878509) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 29878509 * (7 : ZMod 3824449201) ^ 29878509 := by rw [pow_add]
          _ = 1792375900 := by rw [factor_0_24]; decide
      have factor_0_26 : (7 : ZMod 3824449201) ^ 119514037 = 16645686 := by
        calc
          (7 : ZMod 3824449201) ^ 119514037 = (7 : ZMod 3824449201) ^ (59757018 + 59757018 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 59757018 * (7 : ZMod 3824449201) ^ 59757018) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 16645686 := by rw [factor_0_25]; decide
      have factor_0_27 : (7 : ZMod 3824449201) ^ 239028075 = 1746833027 := by
        calc
          (7 : ZMod 3824449201) ^ 239028075 = (7 : ZMod 3824449201) ^ (119514037 + 119514037 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 119514037 * (7 : ZMod 3824449201) ^ 119514037) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1746833027 := by rw [factor_0_26]; decide
      have factor_0_28 : (7 : ZMod 3824449201) ^ 478056150 = 2542990303 := by
        calc
          (7 : ZMod 3824449201) ^ 478056150 = (7 : ZMod 3824449201) ^ (239028075 + 239028075) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 239028075 * (7 : ZMod 3824449201) ^ 239028075 := by rw [pow_add]
          _ = 2542990303 := by rw [factor_0_27]; decide
      have factor_0_29 : (7 : ZMod 3824449201) ^ 956112300 = 3504330136 := by
        calc
          (7 : ZMod 3824449201) ^ 956112300 = (7 : ZMod 3824449201) ^ (478056150 + 478056150) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 478056150 * (7 : ZMod 3824449201) ^ 478056150 := by rw [pow_add]
          _ = 3504330136 := by rw [factor_0_28]; decide
      have factor_0_30 : (7 : ZMod 3824449201) ^ 1912224600 = 3824449200 := by
        calc
          (7 : ZMod 3824449201) ^ 1912224600 = (7 : ZMod 3824449201) ^ (956112300 + 956112300) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 956112300 * (7 : ZMod 3824449201) ^ 956112300 := by rw [pow_add]
          _ = 3824449200 := by rw [factor_0_29]; decide
      change (7 : ZMod 3824449201) ^ 1912224600 ≠ 1
      rw [factor_0_30]
      decide
    ·
      have factor_1_0 : (7 : ZMod 3824449201) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 3824449201) ^ 2 = 49 := by
        calc
          (7 : ZMod 3824449201) ^ 2 = (7 : ZMod 3824449201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 1 * (7 : ZMod 3824449201) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 3824449201) ^ 4 = 2401 := by
        calc
          (7 : ZMod 3824449201) ^ 4 = (7 : ZMod 3824449201) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 2 * (7 : ZMod 3824449201) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 3824449201) ^ 9 = 40353607 := by
        calc
          (7 : ZMod 3824449201) ^ 9 = (7 : ZMod 3824449201) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 4 * (7 : ZMod 3824449201) ^ 4) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 40353607 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 3824449201) ^ 18 = 1372616659 := by
        calc
          (7 : ZMod 3824449201) ^ 18 = (7 : ZMod 3824449201) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 9 * (7 : ZMod 3824449201) ^ 9 := by rw [pow_add]
          _ = 1372616659 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 3824449201) ^ 37 = 3147188664 := by
        calc
          (7 : ZMod 3824449201) ^ 37 = (7 : ZMod 3824449201) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 18 * (7 : ZMod 3824449201) ^ 18) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 3147188664 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 3824449201) ^ 75 = 2130563953 := by
        calc
          (7 : ZMod 3824449201) ^ 75 = (7 : ZMod 3824449201) ^ (37 + 37 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 37 * (7 : ZMod 3824449201) ^ 37) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 2130563953 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 3824449201) ^ 151 = 639850720 := by
        calc
          (7 : ZMod 3824449201) ^ 151 = (7 : ZMod 3824449201) ^ (75 + 75 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 75 * (7 : ZMod 3824449201) ^ 75) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 639850720 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 3824449201) ^ 303 = 2692301368 := by
        calc
          (7 : ZMod 3824449201) ^ 303 = (7 : ZMod 3824449201) ^ (151 + 151 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 151 * (7 : ZMod 3824449201) ^ 151) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 2692301368 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 3824449201) ^ 607 = 331874369 := by
        calc
          (7 : ZMod 3824449201) ^ 607 = (7 : ZMod 3824449201) ^ (303 + 303 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 303 * (7 : ZMod 3824449201) ^ 303) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 331874369 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 3824449201) ^ 1215 = 1103259607 := by
        calc
          (7 : ZMod 3824449201) ^ 1215 = (7 : ZMod 3824449201) ^ (607 + 607 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 607 * (7 : ZMod 3824449201) ^ 607) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1103259607 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 3824449201) ^ 2431 = 2952305359 := by
        calc
          (7 : ZMod 3824449201) ^ 2431 = (7 : ZMod 3824449201) ^ (1215 + 1215 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 1215 * (7 : ZMod 3824449201) ^ 1215) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 2952305359 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 3824449201) ^ 4863 = 1335804723 := by
        calc
          (7 : ZMod 3824449201) ^ 4863 = (7 : ZMod 3824449201) ^ (2431 + 2431 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 2431 * (7 : ZMod 3824449201) ^ 2431) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1335804723 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 3824449201) ^ 9726 = 3746193670 := by
        calc
          (7 : ZMod 3824449201) ^ 9726 = (7 : ZMod 3824449201) ^ (4863 + 4863) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 4863 * (7 : ZMod 3824449201) ^ 4863 := by rw [pow_add]
          _ = 3746193670 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 3824449201) ^ 19452 = 2077846304 := by
        calc
          (7 : ZMod 3824449201) ^ 19452 = (7 : ZMod 3824449201) ^ (9726 + 9726) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 9726 * (7 : ZMod 3824449201) ^ 9726 := by rw [pow_add]
          _ = 2077846304 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 3824449201) ^ 38904 = 3249240795 := by
        calc
          (7 : ZMod 3824449201) ^ 38904 = (7 : ZMod 3824449201) ^ (19452 + 19452) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 19452 * (7 : ZMod 3824449201) ^ 19452 := by rw [pow_add]
          _ = 3249240795 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 3824449201) ^ 77808 = 2751225801 := by
        calc
          (7 : ZMod 3824449201) ^ 77808 = (7 : ZMod 3824449201) ^ (38904 + 38904) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 38904 * (7 : ZMod 3824449201) ^ 38904 := by rw [pow_add]
          _ = 2751225801 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 3824449201) ^ 155617 = 1964564047 := by
        calc
          (7 : ZMod 3824449201) ^ 155617 = (7 : ZMod 3824449201) ^ (77808 + 77808 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 77808 * (7 : ZMod 3824449201) ^ 77808) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1964564047 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 3824449201) ^ 311234 = 1985629772 := by
        calc
          (7 : ZMod 3824449201) ^ 311234 = (7 : ZMod 3824449201) ^ (155617 + 155617) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 155617 * (7 : ZMod 3824449201) ^ 155617 := by rw [pow_add]
          _ = 1985629772 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 3824449201) ^ 622468 = 2049703599 := by
        calc
          (7 : ZMod 3824449201) ^ 622468 = (7 : ZMod 3824449201) ^ (311234 + 311234) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 311234 * (7 : ZMod 3824449201) ^ 311234 := by rw [pow_add]
          _ = 2049703599 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 3824449201) ^ 1244937 = 1594028030 := by
        calc
          (7 : ZMod 3824449201) ^ 1244937 = (7 : ZMod 3824449201) ^ (622468 + 622468 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 622468 * (7 : ZMod 3824449201) ^ 622468) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1594028030 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 3824449201) ^ 2489875 = 3514685914 := by
        calc
          (7 : ZMod 3824449201) ^ 2489875 = (7 : ZMod 3824449201) ^ (1244937 + 1244937 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 1244937 * (7 : ZMod 3824449201) ^ 1244937) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 3514685914 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 3824449201) ^ 4979751 = 2060505694 := by
        calc
          (7 : ZMod 3824449201) ^ 4979751 = (7 : ZMod 3824449201) ^ (2489875 + 2489875 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 2489875 * (7 : ZMod 3824449201) ^ 2489875) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 2060505694 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 3824449201) ^ 9959503 = 2940375737 := by
        calc
          (7 : ZMod 3824449201) ^ 9959503 = (7 : ZMod 3824449201) ^ (4979751 + 4979751 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 4979751 * (7 : ZMod 3824449201) ^ 4979751) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 2940375737 := by rw [factor_1_22]; decide
      have factor_1_24 : (7 : ZMod 3824449201) ^ 19919006 = 3521480088 := by
        calc
          (7 : ZMod 3824449201) ^ 19919006 = (7 : ZMod 3824449201) ^ (9959503 + 9959503) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 9959503 * (7 : ZMod 3824449201) ^ 9959503 := by rw [pow_add]
          _ = 3521480088 := by rw [factor_1_23]; decide
      have factor_1_25 : (7 : ZMod 3824449201) ^ 39838012 = 3236987854 := by
        calc
          (7 : ZMod 3824449201) ^ 39838012 = (7 : ZMod 3824449201) ^ (19919006 + 19919006) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 19919006 * (7 : ZMod 3824449201) ^ 19919006 := by rw [pow_add]
          _ = 3236987854 := by rw [factor_1_24]; decide
      have factor_1_26 : (7 : ZMod 3824449201) ^ 79676025 = 2572888121 := by
        calc
          (7 : ZMod 3824449201) ^ 79676025 = (7 : ZMod 3824449201) ^ (39838012 + 39838012 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 39838012 * (7 : ZMod 3824449201) ^ 39838012) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 2572888121 := by rw [factor_1_25]; decide
      have factor_1_27 : (7 : ZMod 3824449201) ^ 159352050 = 3061068539 := by
        calc
          (7 : ZMod 3824449201) ^ 159352050 = (7 : ZMod 3824449201) ^ (79676025 + 79676025) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 79676025 * (7 : ZMod 3824449201) ^ 79676025 := by rw [pow_add]
          _ = 3061068539 := by rw [factor_1_26]; decide
      have factor_1_28 : (7 : ZMod 3824449201) ^ 318704100 = 1153696952 := by
        calc
          (7 : ZMod 3824449201) ^ 318704100 = (7 : ZMod 3824449201) ^ (159352050 + 159352050) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 159352050 * (7 : ZMod 3824449201) ^ 159352050 := by rw [pow_add]
          _ = 1153696952 := by rw [factor_1_27]; decide
      have factor_1_29 : (7 : ZMod 3824449201) ^ 637408200 = 3758022778 := by
        calc
          (7 : ZMod 3824449201) ^ 637408200 = (7 : ZMod 3824449201) ^ (318704100 + 318704100) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 318704100 * (7 : ZMod 3824449201) ^ 318704100 := by rw [pow_add]
          _ = 3758022778 := by rw [factor_1_28]; decide
      have factor_1_30 : (7 : ZMod 3824449201) ^ 1274816400 = 3758022777 := by
        calc
          (7 : ZMod 3824449201) ^ 1274816400 = (7 : ZMod 3824449201) ^ (637408200 + 637408200) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 637408200 * (7 : ZMod 3824449201) ^ 637408200 := by rw [pow_add]
          _ = 3758022777 := by rw [factor_1_29]; decide
      change (7 : ZMod 3824449201) ^ 1274816400 ≠ 1
      rw [factor_1_30]
      decide
    ·
      have factor_2_0 : (7 : ZMod 3824449201) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 3824449201) ^ 2 = 49 := by
        calc
          (7 : ZMod 3824449201) ^ 2 = (7 : ZMod 3824449201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 1 * (7 : ZMod 3824449201) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 3824449201) ^ 5 = 16807 := by
        calc
          (7 : ZMod 3824449201) ^ 5 = (7 : ZMod 3824449201) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 2 * (7 : ZMod 3824449201) ^ 2) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 3824449201) ^ 11 = 1977326743 := by
        calc
          (7 : ZMod 3824449201) ^ 11 = (7 : ZMod 3824449201) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 5 * (7 : ZMod 3824449201) ^ 5) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1977326743 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 3824449201) ^ 22 = 2801836198 := by
        calc
          (7 : ZMod 3824449201) ^ 22 = (7 : ZMod 3824449201) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 11 * (7 : ZMod 3824449201) ^ 11 := by rw [pow_add]
          _ = 2801836198 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 3824449201) ^ 45 = 883765135 := by
        calc
          (7 : ZMod 3824449201) ^ 45 = (7 : ZMod 3824449201) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 22 * (7 : ZMod 3824449201) ^ 22) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 883765135 := by rw [factor_2_4]; decide
      have factor_2_6 : (7 : ZMod 3824449201) ^ 91 = 937391181 := by
        calc
          (7 : ZMod 3824449201) ^ 91 = (7 : ZMod 3824449201) ^ (45 + 45 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 45 * (7 : ZMod 3824449201) ^ 45) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 937391181 := by rw [factor_2_5]; decide
      have factor_2_7 : (7 : ZMod 3824449201) ^ 182 = 1805491204 := by
        calc
          (7 : ZMod 3824449201) ^ 182 = (7 : ZMod 3824449201) ^ (91 + 91) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 91 * (7 : ZMod 3824449201) ^ 91 := by rw [pow_add]
          _ = 1805491204 := by rw [factor_2_6]; decide
      have factor_2_8 : (7 : ZMod 3824449201) ^ 364 = 106022378 := by
        calc
          (7 : ZMod 3824449201) ^ 364 = (7 : ZMod 3824449201) ^ (182 + 182) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 182 * (7 : ZMod 3824449201) ^ 182 := by rw [pow_add]
          _ = 106022378 := by rw [factor_2_7]; decide
      have factor_2_9 : (7 : ZMod 3824449201) ^ 729 = 239257928 := by
        calc
          (7 : ZMod 3824449201) ^ 729 = (7 : ZMod 3824449201) ^ (364 + 364 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 364 * (7 : ZMod 3824449201) ^ 364) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 239257928 := by rw [factor_2_8]; decide
      have factor_2_10 : (7 : ZMod 3824449201) ^ 1458 = 470285184 := by
        calc
          (7 : ZMod 3824449201) ^ 1458 = (7 : ZMod 3824449201) ^ (729 + 729) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 729 * (7 : ZMod 3824449201) ^ 729 := by rw [pow_add]
          _ = 470285184 := by rw [factor_2_9]; decide
      have factor_2_11 : (7 : ZMod 3824449201) ^ 2917 = 1481462522 := by
        calc
          (7 : ZMod 3824449201) ^ 2917 = (7 : ZMod 3824449201) ^ (1458 + 1458 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 1458 * (7 : ZMod 3824449201) ^ 1458) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1481462522 := by rw [factor_2_10]; decide
      have factor_2_12 : (7 : ZMod 3824449201) ^ 5835 = 1685529780 := by
        calc
          (7 : ZMod 3824449201) ^ 5835 = (7 : ZMod 3824449201) ^ (2917 + 2917 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 2917 * (7 : ZMod 3824449201) ^ 2917) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1685529780 := by rw [factor_2_11]; decide
      have factor_2_13 : (7 : ZMod 3824449201) ^ 11671 = 604267247 := by
        calc
          (7 : ZMod 3824449201) ^ 11671 = (7 : ZMod 3824449201) ^ (5835 + 5835 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 5835 * (7 : ZMod 3824449201) ^ 5835) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 604267247 := by rw [factor_2_12]; decide
      have factor_2_14 : (7 : ZMod 3824449201) ^ 23342 = 776404109 := by
        calc
          (7 : ZMod 3824449201) ^ 23342 = (7 : ZMod 3824449201) ^ (11671 + 11671) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 11671 * (7 : ZMod 3824449201) ^ 11671 := by rw [pow_add]
          _ = 776404109 := by rw [factor_2_13]; decide
      have factor_2_15 : (7 : ZMod 3824449201) ^ 46685 = 3728470777 := by
        calc
          (7 : ZMod 3824449201) ^ 46685 = (7 : ZMod 3824449201) ^ (23342 + 23342 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 23342 * (7 : ZMod 3824449201) ^ 23342) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 3728470777 := by rw [factor_2_14]; decide
      have factor_2_16 : (7 : ZMod 3824449201) ^ 93370 = 2694305101 := by
        calc
          (7 : ZMod 3824449201) ^ 93370 = (7 : ZMod 3824449201) ^ (46685 + 46685) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 46685 * (7 : ZMod 3824449201) ^ 46685 := by rw [pow_add]
          _ = 2694305101 := by rw [factor_2_15]; decide
      have factor_2_17 : (7 : ZMod 3824449201) ^ 186740 = 3267588298 := by
        calc
          (7 : ZMod 3824449201) ^ 186740 = (7 : ZMod 3824449201) ^ (93370 + 93370) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 93370 * (7 : ZMod 3824449201) ^ 93370 := by rw [pow_add]
          _ = 3267588298 := by rw [factor_2_16]; decide
      have factor_2_18 : (7 : ZMod 3824449201) ^ 373481 = 2271913326 := by
        calc
          (7 : ZMod 3824449201) ^ 373481 = (7 : ZMod 3824449201) ^ (186740 + 186740 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 186740 * (7 : ZMod 3824449201) ^ 186740) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 2271913326 := by rw [factor_2_17]; decide
      have factor_2_19 : (7 : ZMod 3824449201) ^ 746962 = 1885598194 := by
        calc
          (7 : ZMod 3824449201) ^ 746962 = (7 : ZMod 3824449201) ^ (373481 + 373481) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 373481 * (7 : ZMod 3824449201) ^ 373481 := by rw [pow_add]
          _ = 1885598194 := by rw [factor_2_18]; decide
      have factor_2_20 : (7 : ZMod 3824449201) ^ 1493925 = 1356649356 := by
        calc
          (7 : ZMod 3824449201) ^ 1493925 = (7 : ZMod 3824449201) ^ (746962 + 746962 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 746962 * (7 : ZMod 3824449201) ^ 746962) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1356649356 := by rw [factor_2_19]; decide
      have factor_2_21 : (7 : ZMod 3824449201) ^ 2987850 = 2535006827 := by
        calc
          (7 : ZMod 3824449201) ^ 2987850 = (7 : ZMod 3824449201) ^ (1493925 + 1493925) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 1493925 * (7 : ZMod 3824449201) ^ 1493925 := by rw [pow_add]
          _ = 2535006827 := by rw [factor_2_20]; decide
      have factor_2_22 : (7 : ZMod 3824449201) ^ 5975701 = 3375522246 := by
        calc
          (7 : ZMod 3824449201) ^ 5975701 = (7 : ZMod 3824449201) ^ (2987850 + 2987850 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 2987850 * (7 : ZMod 3824449201) ^ 2987850) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 3375522246 := by rw [factor_2_21]; decide
      have factor_2_23 : (7 : ZMod 3824449201) ^ 11951403 = 1161601683 := by
        calc
          (7 : ZMod 3824449201) ^ 11951403 = (7 : ZMod 3824449201) ^ (5975701 + 5975701 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 5975701 * (7 : ZMod 3824449201) ^ 5975701) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1161601683 := by rw [factor_2_22]; decide
      have factor_2_24 : (7 : ZMod 3824449201) ^ 23902807 = 1620931597 := by
        calc
          (7 : ZMod 3824449201) ^ 23902807 = (7 : ZMod 3824449201) ^ (11951403 + 11951403 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 11951403 * (7 : ZMod 3824449201) ^ 11951403) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1620931597 := by rw [factor_2_23]; decide
      have factor_2_25 : (7 : ZMod 3824449201) ^ 47805615 = 2286903423 := by
        calc
          (7 : ZMod 3824449201) ^ 47805615 = (7 : ZMod 3824449201) ^ (23902807 + 23902807 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 23902807 * (7 : ZMod 3824449201) ^ 23902807) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 2286903423 := by rw [factor_2_24]; decide
      have factor_2_26 : (7 : ZMod 3824449201) ^ 95611230 = 1625900764 := by
        calc
          (7 : ZMod 3824449201) ^ 95611230 = (7 : ZMod 3824449201) ^ (47805615 + 47805615) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 47805615 * (7 : ZMod 3824449201) ^ 47805615 := by rw [pow_add]
          _ = 1625900764 := by rw [factor_2_25]; decide
      have factor_2_27 : (7 : ZMod 3824449201) ^ 191222460 = 1683223116 := by
        calc
          (7 : ZMod 3824449201) ^ 191222460 = (7 : ZMod 3824449201) ^ (95611230 + 95611230) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 95611230 * (7 : ZMod 3824449201) ^ 95611230 := by rw [pow_add]
          _ = 1683223116 := by rw [factor_2_26]; decide
      have factor_2_28 : (7 : ZMod 3824449201) ^ 382444920 = 1597502823 := by
        calc
          (7 : ZMod 3824449201) ^ 382444920 = (7 : ZMod 3824449201) ^ (191222460 + 191222460) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 191222460 * (7 : ZMod 3824449201) ^ 191222460 := by rw [pow_add]
          _ = 1597502823 := by rw [factor_2_27]; decide
      have factor_2_29 : (7 : ZMod 3824449201) ^ 764889840 = 150578905 := by
        calc
          (7 : ZMod 3824449201) ^ 764889840 = (7 : ZMod 3824449201) ^ (382444920 + 382444920) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 382444920 * (7 : ZMod 3824449201) ^ 382444920 := by rw [pow_add]
          _ = 150578905 := by rw [factor_2_28]; decide
      change (7 : ZMod 3824449201) ^ 764889840 ≠ 1
      rw [factor_2_29]
      decide
    ·
      have factor_3_0 : (7 : ZMod 3824449201) ^ 1 = 7 := by norm_num
      have factor_3_1 : (7 : ZMod 3824449201) ^ 2 = 49 := by
        calc
          (7 : ZMod 3824449201) ^ 2 = (7 : ZMod 3824449201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 1 * (7 : ZMod 3824449201) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_3_0]; decide
      have factor_3_2 : (7 : ZMod 3824449201) ^ 5 = 16807 := by
        calc
          (7 : ZMod 3824449201) ^ 5 = (7 : ZMod 3824449201) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 2 * (7 : ZMod 3824449201) ^ 2) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_3_1]; decide
      have factor_3_3 : (7 : ZMod 3824449201) ^ 10 = 282475249 := by
        calc
          (7 : ZMod 3824449201) ^ 10 = (7 : ZMod 3824449201) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 5 * (7 : ZMod 3824449201) ^ 5 := by rw [pow_add]
          _ = 282475249 := by rw [factor_3_2]; decide
      have factor_3_4 : (7 : ZMod 3824449201) ^ 20 = 2242579874 := by
        calc
          (7 : ZMod 3824449201) ^ 20 = (7 : ZMod 3824449201) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 10 * (7 : ZMod 3824449201) ^ 10 := by rw [pow_add]
          _ = 2242579874 := by rw [factor_3_3]; decide
      have factor_3_5 : (7 : ZMod 3824449201) ^ 41 = 3112810289 := by
        calc
          (7 : ZMod 3824449201) ^ 41 = (7 : ZMod 3824449201) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 20 * (7 : ZMod 3824449201) ^ 20) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 3112810289 := by rw [factor_3_4]; decide
      have factor_3_6 : (7 : ZMod 3824449201) ^ 82 = 3453966292 := by
        calc
          (7 : ZMod 3824449201) ^ 82 = (7 : ZMod 3824449201) ^ (41 + 41) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 41 * (7 : ZMod 3824449201) ^ 41 := by rw [pow_add]
          _ = 3453966292 := by rw [factor_3_5]; decide
      have factor_3_7 : (7 : ZMod 3824449201) ^ 165 = 2923662638 := by
        calc
          (7 : ZMod 3824449201) ^ 165 = (7 : ZMod 3824449201) ^ (82 + 82 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 82 * (7 : ZMod 3824449201) ^ 82) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 2923662638 := by rw [factor_3_6]; decide
      have factor_3_8 : (7 : ZMod 3824449201) ^ 331 = 3692784617 := by
        calc
          (7 : ZMod 3824449201) ^ 331 = (7 : ZMod 3824449201) ^ (165 + 165 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 165 * (7 : ZMod 3824449201) ^ 165) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 3692784617 := by rw [factor_3_7]; decide
      have factor_3_9 : (7 : ZMod 3824449201) ^ 663 = 3165896411 := by
        calc
          (7 : ZMod 3824449201) ^ 663 = (7 : ZMod 3824449201) ^ (331 + 331 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 331 * (7 : ZMod 3824449201) ^ 331) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 3165896411 := by rw [factor_3_8]; decide
      have factor_3_10 : (7 : ZMod 3824449201) ^ 1326 = 2713224300 := by
        calc
          (7 : ZMod 3824449201) ^ 1326 = (7 : ZMod 3824449201) ^ (663 + 663) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 663 * (7 : ZMod 3824449201) ^ 663 := by rw [pow_add]
          _ = 2713224300 := by rw [factor_3_9]; decide
      have factor_3_11 : (7 : ZMod 3824449201) ^ 2652 = 880749145 := by
        calc
          (7 : ZMod 3824449201) ^ 2652 = (7 : ZMod 3824449201) ^ (1326 + 1326) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 1326 * (7 : ZMod 3824449201) ^ 1326 := by rw [pow_add]
          _ = 880749145 := by rw [factor_3_10]; decide
      have factor_3_12 : (7 : ZMod 3824449201) ^ 5305 = 2654467748 := by
        calc
          (7 : ZMod 3824449201) ^ 5305 = (7 : ZMod 3824449201) ^ (2652 + 2652 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 2652 * (7 : ZMod 3824449201) ^ 2652) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 2654467748 := by rw [factor_3_11]; decide
      have factor_3_13 : (7 : ZMod 3824449201) ^ 10610 = 1469956262 := by
        calc
          (7 : ZMod 3824449201) ^ 10610 = (7 : ZMod 3824449201) ^ (5305 + 5305) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 5305 * (7 : ZMod 3824449201) ^ 5305 := by rw [pow_add]
          _ = 1469956262 := by rw [factor_3_12]; decide
      have factor_3_14 : (7 : ZMod 3824449201) ^ 21220 = 3822956528 := by
        calc
          (7 : ZMod 3824449201) ^ 21220 = (7 : ZMod 3824449201) ^ (10610 + 10610) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 10610 * (7 : ZMod 3824449201) ^ 10610 := by rw [pow_add]
          _ = 3822956528 := by rw [factor_3_13]; decide
      have factor_3_15 : (7 : ZMod 3824449201) ^ 42441 = 404952825 := by
        calc
          (7 : ZMod 3824449201) ^ 42441 = (7 : ZMod 3824449201) ^ (21220 + 21220 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 21220 * (7 : ZMod 3824449201) ^ 21220) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 404952825 := by rw [factor_3_14]; decide
      have factor_3_16 : (7 : ZMod 3824449201) ^ 84882 = 81332487 := by
        calc
          (7 : ZMod 3824449201) ^ 84882 = (7 : ZMod 3824449201) ^ (42441 + 42441) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 42441 * (7 : ZMod 3824449201) ^ 42441 := by rw [pow_add]
          _ = 81332487 := by rw [factor_3_15]; decide
      have factor_3_17 : (7 : ZMod 3824449201) ^ 169764 = 3407747916 := by
        calc
          (7 : ZMod 3824449201) ^ 169764 = (7 : ZMod 3824449201) ^ (84882 + 84882) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 84882 * (7 : ZMod 3824449201) ^ 84882 := by rw [pow_add]
          _ = 3407747916 := by rw [factor_3_16]; decide
      have factor_3_18 : (7 : ZMod 3824449201) ^ 339528 = 680633419 := by
        calc
          (7 : ZMod 3824449201) ^ 339528 = (7 : ZMod 3824449201) ^ (169764 + 169764) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 169764 * (7 : ZMod 3824449201) ^ 169764 := by rw [pow_add]
          _ = 680633419 := by rw [factor_3_17]; decide
      have factor_3_19 : (7 : ZMod 3824449201) ^ 679057 = 1818038161 := by
        calc
          (7 : ZMod 3824449201) ^ 679057 = (7 : ZMod 3824449201) ^ (339528 + 339528 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 339528 * (7 : ZMod 3824449201) ^ 339528) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1818038161 := by rw [factor_3_18]; decide
      have factor_3_20 : (7 : ZMod 3824449201) ^ 1358114 = 2971962089 := by
        calc
          (7 : ZMod 3824449201) ^ 1358114 = (7 : ZMod 3824449201) ^ (679057 + 679057) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 679057 * (7 : ZMod 3824449201) ^ 679057 := by rw [pow_add]
          _ = 2971962089 := by rw [factor_3_19]; decide
      have factor_3_21 : (7 : ZMod 3824449201) ^ 2716228 = 1843278892 := by
        calc
          (7 : ZMod 3824449201) ^ 2716228 = (7 : ZMod 3824449201) ^ (1358114 + 1358114) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 1358114 * (7 : ZMod 3824449201) ^ 1358114 := by rw [pow_add]
          _ = 1843278892 := by rw [factor_3_20]; decide
      have factor_3_22 : (7 : ZMod 3824449201) ^ 5432456 = 2416852546 := by
        calc
          (7 : ZMod 3824449201) ^ 5432456 = (7 : ZMod 3824449201) ^ (2716228 + 2716228) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 2716228 * (7 : ZMod 3824449201) ^ 2716228 := by rw [pow_add]
          _ = 2416852546 := by rw [factor_3_21]; decide
      have factor_3_23 : (7 : ZMod 3824449201) ^ 10864912 = 3345721286 := by
        calc
          (7 : ZMod 3824449201) ^ 10864912 = (7 : ZMod 3824449201) ^ (5432456 + 5432456) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 5432456 * (7 : ZMod 3824449201) ^ 5432456 := by rw [pow_add]
          _ = 3345721286 := by rw [factor_3_22]; decide
      have factor_3_24 : (7 : ZMod 3824449201) ^ 21729825 = 3287441030 := by
        calc
          (7 : ZMod 3824449201) ^ 21729825 = (7 : ZMod 3824449201) ^ (10864912 + 10864912 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 10864912 * (7 : ZMod 3824449201) ^ 10864912) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 3287441030 := by rw [factor_3_23]; decide
      have factor_3_25 : (7 : ZMod 3824449201) ^ 43459650 = 2525353501 := by
        calc
          (7 : ZMod 3824449201) ^ 43459650 = (7 : ZMod 3824449201) ^ (21729825 + 21729825) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 21729825 * (7 : ZMod 3824449201) ^ 21729825 := by rw [pow_add]
          _ = 2525353501 := by rw [factor_3_24]; decide
      have factor_3_26 : (7 : ZMod 3824449201) ^ 86919300 = 2489768865 := by
        calc
          (7 : ZMod 3824449201) ^ 86919300 = (7 : ZMod 3824449201) ^ (43459650 + 43459650) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 43459650 * (7 : ZMod 3824449201) ^ 43459650 := by rw [pow_add]
          _ = 2489768865 := by rw [factor_3_25]; decide
      have factor_3_27 : (7 : ZMod 3824449201) ^ 173838600 = 443298158 := by
        calc
          (7 : ZMod 3824449201) ^ 173838600 = (7 : ZMod 3824449201) ^ (86919300 + 86919300) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 86919300 * (7 : ZMod 3824449201) ^ 86919300 := by rw [pow_add]
          _ = 443298158 := by rw [factor_3_26]; decide
      have factor_3_28 : (7 : ZMod 3824449201) ^ 347677200 = 269240750 := by
        calc
          (7 : ZMod 3824449201) ^ 347677200 = (7 : ZMod 3824449201) ^ (173838600 + 173838600) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 173838600 * (7 : ZMod 3824449201) ^ 173838600 := by rw [pow_add]
          _ = 269240750 := by rw [factor_3_27]; decide
      change (7 : ZMod 3824449201) ^ 347677200 ≠ 1
      rw [factor_3_28]
      decide
    ·
      have factor_4_0 : (7 : ZMod 3824449201) ^ 1 = 7 := by norm_num
      have factor_4_1 : (7 : ZMod 3824449201) ^ 2 = 49 := by
        calc
          (7 : ZMod 3824449201) ^ 2 = (7 : ZMod 3824449201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 1 * (7 : ZMod 3824449201) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_4_0]; decide
      have factor_4_2 : (7 : ZMod 3824449201) ^ 4 = 2401 := by
        calc
          (7 : ZMod 3824449201) ^ 4 = (7 : ZMod 3824449201) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 2 * (7 : ZMod 3824449201) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_4_1]; decide
      have factor_4_3 : (7 : ZMod 3824449201) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 3824449201) ^ 8 = (7 : ZMod 3824449201) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 4 * (7 : ZMod 3824449201) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [factor_4_2]; decide
      have factor_4_4 : (7 : ZMod 3824449201) ^ 17 = 742437980 := by
        calc
          (7 : ZMod 3824449201) ^ 17 = (7 : ZMod 3824449201) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 8 * (7 : ZMod 3824449201) ^ 8) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 742437980 := by rw [factor_4_3]; decide
      have factor_4_5 : (7 : ZMod 3824449201) ^ 35 = 3654527590 := by
        calc
          (7 : ZMod 3824449201) ^ 35 = (7 : ZMod 3824449201) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 17 * (7 : ZMod 3824449201) ^ 17) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 3654527590 := by rw [factor_4_4]; decide
      have factor_4_6 : (7 : ZMod 3824449201) ^ 70 = 1538826445 := by
        calc
          (7 : ZMod 3824449201) ^ 70 = (7 : ZMod 3824449201) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 35 * (7 : ZMod 3824449201) ^ 35 := by rw [pow_add]
          _ = 1538826445 := by rw [factor_4_5]; decide
      have factor_4_7 : (7 : ZMod 3824449201) ^ 140 = 124914541 := by
        calc
          (7 : ZMod 3824449201) ^ 140 = (7 : ZMod 3824449201) ^ (70 + 70) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 70 * (7 : ZMod 3824449201) ^ 70 := by rw [pow_add]
          _ = 124914541 := by rw [factor_4_6]; decide
      have factor_4_8 : (7 : ZMod 3824449201) ^ 280 = 722187510 := by
        calc
          (7 : ZMod 3824449201) ^ 280 = (7 : ZMod 3824449201) ^ (140 + 140) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 140 * (7 : ZMod 3824449201) ^ 140 := by rw [pow_add]
          _ = 722187510 := by rw [factor_4_7]; decide
      have factor_4_9 : (7 : ZMod 3824449201) ^ 561 = 1498652664 := by
        calc
          (7 : ZMod 3824449201) ^ 561 = (7 : ZMod 3824449201) ^ (280 + 280 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 280 * (7 : ZMod 3824449201) ^ 280) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1498652664 := by rw [factor_4_8]; decide
      have factor_4_10 : (7 : ZMod 3824449201) ^ 1122 = 1517913296 := by
        calc
          (7 : ZMod 3824449201) ^ 1122 = (7 : ZMod 3824449201) ^ (561 + 561) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 561 * (7 : ZMod 3824449201) ^ 561 := by rw [pow_add]
          _ = 1517913296 := by rw [factor_4_9]; decide
      have factor_4_11 : (7 : ZMod 3824449201) ^ 2244 = 1131244433 := by
        calc
          (7 : ZMod 3824449201) ^ 2244 = (7 : ZMod 3824449201) ^ (1122 + 1122) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 1122 * (7 : ZMod 3824449201) ^ 1122 := by rw [pow_add]
          _ = 1131244433 := by rw [factor_4_10]; decide
      have factor_4_12 : (7 : ZMod 3824449201) ^ 4488 = 1434869162 := by
        calc
          (7 : ZMod 3824449201) ^ 4488 = (7 : ZMod 3824449201) ^ (2244 + 2244) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 2244 * (7 : ZMod 3824449201) ^ 2244 := by rw [pow_add]
          _ = 1434869162 := by rw [factor_4_11]; decide
      have factor_4_13 : (7 : ZMod 3824449201) ^ 8977 = 3637956692 := by
        calc
          (7 : ZMod 3824449201) ^ 8977 = (7 : ZMod 3824449201) ^ (4488 + 4488 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 4488 * (7 : ZMod 3824449201) ^ 4488) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 3637956692 := by rw [factor_4_12]; decide
      have factor_4_14 : (7 : ZMod 3824449201) ^ 17955 = 768622923 := by
        calc
          (7 : ZMod 3824449201) ^ 17955 = (7 : ZMod 3824449201) ^ (8977 + 8977 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 8977 * (7 : ZMod 3824449201) ^ 8977) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 768622923 := by rw [factor_4_13]; decide
      have factor_4_15 : (7 : ZMod 3824449201) ^ 35911 = 1583505588 := by
        calc
          (7 : ZMod 3824449201) ^ 35911 = (7 : ZMod 3824449201) ^ (17955 + 17955 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 17955 * (7 : ZMod 3824449201) ^ 17955) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1583505588 := by rw [factor_4_14]; decide
      have factor_4_16 : (7 : ZMod 3824449201) ^ 71823 = 3736254426 := by
        calc
          (7 : ZMod 3824449201) ^ 71823 = (7 : ZMod 3824449201) ^ (35911 + 35911 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 35911 * (7 : ZMod 3824449201) ^ 35911) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 3736254426 := by rw [factor_4_15]; decide
      have factor_4_17 : (7 : ZMod 3824449201) ^ 143646 = 574338785 := by
        calc
          (7 : ZMod 3824449201) ^ 143646 = (7 : ZMod 3824449201) ^ (71823 + 71823) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 71823 * (7 : ZMod 3824449201) ^ 71823 := by rw [pow_add]
          _ = 574338785 := by rw [factor_4_16]; decide
      have factor_4_18 : (7 : ZMod 3824449201) ^ 287293 = 1630591251 := by
        calc
          (7 : ZMod 3824449201) ^ 287293 = (7 : ZMod 3824449201) ^ (143646 + 143646 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 143646 * (7 : ZMod 3824449201) ^ 143646) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1630591251 := by rw [factor_4_17]; decide
      have factor_4_19 : (7 : ZMod 3824449201) ^ 574586 = 2465674104 := by
        calc
          (7 : ZMod 3824449201) ^ 574586 = (7 : ZMod 3824449201) ^ (287293 + 287293) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 287293 * (7 : ZMod 3824449201) ^ 287293 := by rw [pow_add]
          _ = 2465674104 := by rw [factor_4_18]; decide
      have factor_4_20 : (7 : ZMod 3824449201) ^ 1149173 = 1287248908 := by
        calc
          (7 : ZMod 3824449201) ^ 1149173 = (7 : ZMod 3824449201) ^ (574586 + 574586 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 574586 * (7 : ZMod 3824449201) ^ 574586) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1287248908 := by rw [factor_4_19]; decide
      have factor_4_21 : (7 : ZMod 3824449201) ^ 2298346 = 432668110 := by
        calc
          (7 : ZMod 3824449201) ^ 2298346 = (7 : ZMod 3824449201) ^ (1149173 + 1149173) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 1149173 * (7 : ZMod 3824449201) ^ 1149173 := by rw [pow_add]
          _ = 432668110 := by rw [factor_4_20]; decide
      have factor_4_22 : (7 : ZMod 3824449201) ^ 4596693 = 1967403226 := by
        calc
          (7 : ZMod 3824449201) ^ 4596693 = (7 : ZMod 3824449201) ^ (2298346 + 2298346 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 2298346 * (7 : ZMod 3824449201) ^ 2298346) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1967403226 := by rw [factor_4_21]; decide
      have factor_4_23 : (7 : ZMod 3824449201) ^ 9193387 = 1640087885 := by
        calc
          (7 : ZMod 3824449201) ^ 9193387 = (7 : ZMod 3824449201) ^ (4596693 + 4596693 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 4596693 * (7 : ZMod 3824449201) ^ 4596693) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1640087885 := by rw [factor_4_22]; decide
      have factor_4_24 : (7 : ZMod 3824449201) ^ 18386775 = 867780265 := by
        calc
          (7 : ZMod 3824449201) ^ 18386775 = (7 : ZMod 3824449201) ^ (9193387 + 9193387 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 9193387 * (7 : ZMod 3824449201) ^ 9193387) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 867780265 := by rw [factor_4_23]; decide
      have factor_4_25 : (7 : ZMod 3824449201) ^ 36773550 = 651504392 := by
        calc
          (7 : ZMod 3824449201) ^ 36773550 = (7 : ZMod 3824449201) ^ (18386775 + 18386775) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 18386775 * (7 : ZMod 3824449201) ^ 18386775 := by rw [pow_add]
          _ = 651504392 := by rw [factor_4_24]; decide
      have factor_4_26 : (7 : ZMod 3824449201) ^ 73547100 = 1984913078 := by
        calc
          (7 : ZMod 3824449201) ^ 73547100 = (7 : ZMod 3824449201) ^ (36773550 + 36773550) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 36773550 * (7 : ZMod 3824449201) ^ 36773550 := by rw [pow_add]
          _ = 1984913078 := by rw [factor_4_25]; decide
      have factor_4_27 : (7 : ZMod 3824449201) ^ 147094200 = 3378252171 := by
        calc
          (7 : ZMod 3824449201) ^ 147094200 = (7 : ZMod 3824449201) ^ (73547100 + 73547100) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 73547100 * (7 : ZMod 3824449201) ^ 73547100 := by rw [pow_add]
          _ = 3378252171 := by rw [factor_4_26]; decide
      have factor_4_28 : (7 : ZMod 3824449201) ^ 294188400 = 1350222863 := by
        calc
          (7 : ZMod 3824449201) ^ 294188400 = (7 : ZMod 3824449201) ^ (147094200 + 147094200) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 147094200 * (7 : ZMod 3824449201) ^ 147094200 := by rw [pow_add]
          _ = 1350222863 := by rw [factor_4_27]; decide
      change (7 : ZMod 3824449201) ^ 294188400 ≠ 1
      rw [factor_4_28]
      decide
    ·
      have factor_5_0 : (7 : ZMod 3824449201) ^ 1 = 7 := by norm_num
      have factor_5_1 : (7 : ZMod 3824449201) ^ 3 = 343 := by
        calc
          (7 : ZMod 3824449201) ^ 3 = (7 : ZMod 3824449201) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 1 * (7 : ZMod 3824449201) ^ 1) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_5_0]; decide
      have factor_5_2 : (7 : ZMod 3824449201) ^ 6 = 117649 := by
        calc
          (7 : ZMod 3824449201) ^ 6 = (7 : ZMod 3824449201) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 3 * (7 : ZMod 3824449201) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_5_1]; decide
      have factor_5_3 : (7 : ZMod 3824449201) ^ 13 = 1277780382 := by
        calc
          (7 : ZMod 3824449201) ^ 13 = (7 : ZMod 3824449201) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 6 * (7 : ZMod 3824449201) ^ 6) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1277780382 := by rw [factor_5_2]; decide
      have factor_5_4 : (7 : ZMod 3824449201) ^ 26 = 2566839 := by
        calc
          (7 : ZMod 3824449201) ^ 26 = (7 : ZMod 3824449201) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 13 * (7 : ZMod 3824449201) ^ 13 := by rw [pow_add]
          _ = 2566839 := by rw [factor_5_3]; decide
      have factor_5_5 : (7 : ZMod 3824449201) ^ 53 = 1604248588 := by
        calc
          (7 : ZMod 3824449201) ^ 53 = (7 : ZMod 3824449201) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 26 * (7 : ZMod 3824449201) ^ 26) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1604248588 := by rw [factor_5_4]; decide
      have factor_5_6 : (7 : ZMod 3824449201) ^ 107 = 322981315 := by
        calc
          (7 : ZMod 3824449201) ^ 107 = (7 : ZMod 3824449201) ^ (53 + 53 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 53 * (7 : ZMod 3824449201) ^ 53) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 322981315 := by rw [factor_5_5]; decide
      have factor_5_7 : (7 : ZMod 3824449201) ^ 214 = 2837764498 := by
        calc
          (7 : ZMod 3824449201) ^ 214 = (7 : ZMod 3824449201) ^ (107 + 107) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 107 * (7 : ZMod 3824449201) ^ 107 := by rw [pow_add]
          _ = 2837764498 := by rw [factor_5_6]; decide
      have factor_5_8 : (7 : ZMod 3824449201) ^ 429 = 3491079572 := by
        calc
          (7 : ZMod 3824449201) ^ 429 = (7 : ZMod 3824449201) ^ (214 + 214 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 214 * (7 : ZMod 3824449201) ^ 214) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 3491079572 := by rw [factor_5_7]; decide
      have factor_5_9 : (7 : ZMod 3824449201) ^ 858 = 1524722074 := by
        calc
          (7 : ZMod 3824449201) ^ 858 = (7 : ZMod 3824449201) ^ (429 + 429) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 429 * (7 : ZMod 3824449201) ^ 429 := by rw [pow_add]
          _ = 1524722074 := by rw [factor_5_8]; decide
      have factor_5_10 : (7 : ZMod 3824449201) ^ 1716 = 1619219001 := by
        calc
          (7 : ZMod 3824449201) ^ 1716 = (7 : ZMod 3824449201) ^ (858 + 858) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 858 * (7 : ZMod 3824449201) ^ 858 := by rw [pow_add]
          _ = 1619219001 := by rw [factor_5_9]; decide
      have factor_5_11 : (7 : ZMod 3824449201) ^ 3432 = 643562227 := by
        calc
          (7 : ZMod 3824449201) ^ 3432 = (7 : ZMod 3824449201) ^ (1716 + 1716) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 1716 * (7 : ZMod 3824449201) ^ 1716 := by rw [pow_add]
          _ = 643562227 := by rw [factor_5_10]; decide
      have factor_5_12 : (7 : ZMod 3824449201) ^ 6865 = 1685316289 := by
        calc
          (7 : ZMod 3824449201) ^ 6865 = (7 : ZMod 3824449201) ^ (3432 + 3432 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 3432 * (7 : ZMod 3824449201) ^ 3432) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1685316289 := by rw [factor_5_11]; decide
      have factor_5_13 : (7 : ZMod 3824449201) ^ 13730 = 3033408841 := by
        calc
          (7 : ZMod 3824449201) ^ 13730 = (7 : ZMod 3824449201) ^ (6865 + 6865) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 6865 * (7 : ZMod 3824449201) ^ 6865 := by rw [pow_add]
          _ = 3033408841 := by rw [factor_5_12]; decide
      have factor_5_14 : (7 : ZMod 3824449201) ^ 27461 = 2222859099 := by
        calc
          (7 : ZMod 3824449201) ^ 27461 = (7 : ZMod 3824449201) ^ (13730 + 13730 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 13730 * (7 : ZMod 3824449201) ^ 13730) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 2222859099 := by rw [factor_5_13]; decide
      have factor_5_15 : (7 : ZMod 3824449201) ^ 54923 = 1288124838 := by
        calc
          (7 : ZMod 3824449201) ^ 54923 = (7 : ZMod 3824449201) ^ (27461 + 27461 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 27461 * (7 : ZMod 3824449201) ^ 27461) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1288124838 := by rw [factor_5_14]; decide
      have factor_5_16 : (7 : ZMod 3824449201) ^ 109847 = 148688687 := by
        calc
          (7 : ZMod 3824449201) ^ 109847 = (7 : ZMod 3824449201) ^ (54923 + 54923 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 54923 * (7 : ZMod 3824449201) ^ 54923) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 148688687 := by rw [factor_5_15]; decide
      have factor_5_17 : (7 : ZMod 3824449201) ^ 219694 = 3242931983 := by
        calc
          (7 : ZMod 3824449201) ^ 219694 = (7 : ZMod 3824449201) ^ (109847 + 109847) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 109847 * (7 : ZMod 3824449201) ^ 109847 := by rw [pow_add]
          _ = 3242931983 := by rw [factor_5_16]; decide
      have factor_5_18 : (7 : ZMod 3824449201) ^ 439389 = 1633972875 := by
        calc
          (7 : ZMod 3824449201) ^ 439389 = (7 : ZMod 3824449201) ^ (219694 + 219694 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 219694 * (7 : ZMod 3824449201) ^ 219694) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1633972875 := by rw [factor_5_17]; decide
      have factor_5_19 : (7 : ZMod 3824449201) ^ 878779 = 2575034724 := by
        calc
          (7 : ZMod 3824449201) ^ 878779 = (7 : ZMod 3824449201) ^ (439389 + 439389 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 439389 * (7 : ZMod 3824449201) ^ 439389) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 2575034724 := by rw [factor_5_18]; decide
      have factor_5_20 : (7 : ZMod 3824449201) ^ 1757559 = 2825084378 := by
        calc
          (7 : ZMod 3824449201) ^ 1757559 = (7 : ZMod 3824449201) ^ (878779 + 878779 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 878779 * (7 : ZMod 3824449201) ^ 878779) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 2825084378 := by rw [factor_5_19]; decide
      have factor_5_21 : (7 : ZMod 3824449201) ^ 3515118 = 3352927030 := by
        calc
          (7 : ZMod 3824449201) ^ 3515118 = (7 : ZMod 3824449201) ^ (1757559 + 1757559) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 1757559 * (7 : ZMod 3824449201) ^ 1757559 := by rw [pow_add]
          _ = 3352927030 := by rw [factor_5_20]; decide
      have factor_5_22 : (7 : ZMod 3824449201) ^ 7030237 = 3479127078 := by
        calc
          (7 : ZMod 3824449201) ^ 7030237 = (7 : ZMod 3824449201) ^ (3515118 + 3515118 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 3515118 * (7 : ZMod 3824449201) ^ 3515118) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 3479127078 := by rw [factor_5_21]; decide
      have factor_5_23 : (7 : ZMod 3824449201) ^ 14060475 = 773254395 := by
        calc
          (7 : ZMod 3824449201) ^ 14060475 = (7 : ZMod 3824449201) ^ (7030237 + 7030237 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 7030237 * (7 : ZMod 3824449201) ^ 7030237) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 773254395 := by rw [factor_5_22]; decide
      have factor_5_24 : (7 : ZMod 3824449201) ^ 28120950 = 1150341141 := by
        calc
          (7 : ZMod 3824449201) ^ 28120950 = (7 : ZMod 3824449201) ^ (14060475 + 14060475) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 14060475 * (7 : ZMod 3824449201) ^ 14060475 := by rw [pow_add]
          _ = 1150341141 := by rw [factor_5_23]; decide
      have factor_5_25 : (7 : ZMod 3824449201) ^ 56241900 = 3101920462 := by
        calc
          (7 : ZMod 3824449201) ^ 56241900 = (7 : ZMod 3824449201) ^ (28120950 + 28120950) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 28120950 * (7 : ZMod 3824449201) ^ 28120950 := by rw [pow_add]
          _ = 3101920462 := by rw [factor_5_24]; decide
      have factor_5_26 : (7 : ZMod 3824449201) ^ 112483800 = 2875865386 := by
        calc
          (7 : ZMod 3824449201) ^ 112483800 = (7 : ZMod 3824449201) ^ (56241900 + 56241900) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 56241900 * (7 : ZMod 3824449201) ^ 56241900 := by rw [pow_add]
          _ = 2875865386 := by rw [factor_5_25]; decide
      have factor_5_27 : (7 : ZMod 3824449201) ^ 224967600 = 1426197173 := by
        calc
          (7 : ZMod 3824449201) ^ 224967600 = (7 : ZMod 3824449201) ^ (112483800 + 112483800) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 112483800 * (7 : ZMod 3824449201) ^ 112483800 := by rw [pow_add]
          _ = 1426197173 := by rw [factor_5_26]; decide
      change (7 : ZMod 3824449201) ^ 224967600 ≠ 1
      rw [factor_5_27]
      decide
    ·
      have factor_6_0 : (7 : ZMod 3824449201) ^ 1 = 7 := by norm_num
      have factor_6_1 : (7 : ZMod 3824449201) ^ 2 = 49 := by
        calc
          (7 : ZMod 3824449201) ^ 2 = (7 : ZMod 3824449201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 1 * (7 : ZMod 3824449201) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_6_0]; decide
      have factor_6_2 : (7 : ZMod 3824449201) ^ 5 = 16807 := by
        calc
          (7 : ZMod 3824449201) ^ 5 = (7 : ZMod 3824449201) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 2 * (7 : ZMod 3824449201) ^ 2) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_6_1]; decide
      have factor_6_3 : (7 : ZMod 3824449201) ^ 11 = 1977326743 := by
        calc
          (7 : ZMod 3824449201) ^ 11 = (7 : ZMod 3824449201) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 5 * (7 : ZMod 3824449201) ^ 5) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1977326743 := by rw [factor_6_2]; decide
      have factor_6_4 : (7 : ZMod 3824449201) ^ 23 = 490607381 := by
        calc
          (7 : ZMod 3824449201) ^ 23 = (7 : ZMod 3824449201) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 11 * (7 : ZMod 3824449201) ^ 11) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 490607381 := by rw [factor_6_3]; decide
      have factor_6_5 : (7 : ZMod 3824449201) ^ 47 = 1235550404 := by
        calc
          (7 : ZMod 3824449201) ^ 47 = (7 : ZMod 3824449201) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 23 * (7 : ZMod 3824449201) ^ 23) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1235550404 := by rw [factor_6_4]; decide
      have factor_6_6 : (7 : ZMod 3824449201) ^ 95 = 1900095393 := by
        calc
          (7 : ZMod 3824449201) ^ 95 = (7 : ZMod 3824449201) ^ (47 + 47 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 47 * (7 : ZMod 3824449201) ^ 47) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1900095393 := by rw [factor_6_5]; decide
      have factor_6_7 : (7 : ZMod 3824449201) ^ 191 = 3768457821 := by
        calc
          (7 : ZMod 3824449201) ^ 191 = (7 : ZMod 3824449201) ^ (95 + 95 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 95 * (7 : ZMod 3824449201) ^ 95) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 3768457821 := by rw [factor_6_6]; decide
      have factor_6_8 : (7 : ZMod 3824449201) ^ 383 = 2204107856 := by
        calc
          (7 : ZMod 3824449201) ^ 383 = (7 : ZMod 3824449201) ^ (191 + 191 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 191 * (7 : ZMod 3824449201) ^ 191) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 2204107856 := by rw [factor_6_7]; decide
      have factor_6_9 : (7 : ZMod 3824449201) ^ 767 = 633794661 := by
        calc
          (7 : ZMod 3824449201) ^ 767 = (7 : ZMod 3824449201) ^ (383 + 383 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 383 * (7 : ZMod 3824449201) ^ 383) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 633794661 := by rw [factor_6_8]; decide
      have factor_6_10 : (7 : ZMod 3824449201) ^ 1535 = 2402065639 := by
        calc
          (7 : ZMod 3824449201) ^ 1535 = (7 : ZMod 3824449201) ^ (767 + 767 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 767 * (7 : ZMod 3824449201) ^ 767) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 2402065639 := by rw [factor_6_9]; decide
      have factor_6_11 : (7 : ZMod 3824449201) ^ 3071 = 3538155188 := by
        calc
          (7 : ZMod 3824449201) ^ 3071 = (7 : ZMod 3824449201) ^ (1535 + 1535 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 1535 * (7 : ZMod 3824449201) ^ 1535) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 3538155188 := by rw [factor_6_10]; decide
      have factor_6_12 : (7 : ZMod 3824449201) ^ 6142 = 1336583318 := by
        calc
          (7 : ZMod 3824449201) ^ 6142 = (7 : ZMod 3824449201) ^ (3071 + 3071) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 3071 * (7 : ZMod 3824449201) ^ 3071 := by rw [pow_add]
          _ = 1336583318 := by rw [factor_6_11]; decide
      have factor_6_13 : (7 : ZMod 3824449201) ^ 12285 = 3196032869 := by
        calc
          (7 : ZMod 3824449201) ^ 12285 = (7 : ZMod 3824449201) ^ (6142 + 6142 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 6142 * (7 : ZMod 3824449201) ^ 6142) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 3196032869 := by rw [factor_6_12]; decide
      have factor_6_14 : (7 : ZMod 3824449201) ^ 24571 = 1245070105 := by
        calc
          (7 : ZMod 3824449201) ^ 24571 = (7 : ZMod 3824449201) ^ (12285 + 12285 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 12285 * (7 : ZMod 3824449201) ^ 12285) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1245070105 := by rw [factor_6_13]; decide
      have factor_6_15 : (7 : ZMod 3824449201) ^ 49142 = 521362524 := by
        calc
          (7 : ZMod 3824449201) ^ 49142 = (7 : ZMod 3824449201) ^ (24571 + 24571) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 24571 * (7 : ZMod 3824449201) ^ 24571 := by rw [pow_add]
          _ = 521362524 := by rw [factor_6_14]; decide
      have factor_6_16 : (7 : ZMod 3824449201) ^ 98284 = 1866471782 := by
        calc
          (7 : ZMod 3824449201) ^ 98284 = (7 : ZMod 3824449201) ^ (49142 + 49142) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 49142 * (7 : ZMod 3824449201) ^ 49142 := by rw [pow_add]
          _ = 1866471782 := by rw [factor_6_15]; decide
      have factor_6_17 : (7 : ZMod 3824449201) ^ 196569 = 503060431 := by
        calc
          (7 : ZMod 3824449201) ^ 196569 = (7 : ZMod 3824449201) ^ (98284 + 98284 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 98284 * (7 : ZMod 3824449201) ^ 98284) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 503060431 := by rw [factor_6_16]; decide
      have factor_6_18 : (7 : ZMod 3824449201) ^ 393138 = 695837794 := by
        calc
          (7 : ZMod 3824449201) ^ 393138 = (7 : ZMod 3824449201) ^ (196569 + 196569) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 196569 * (7 : ZMod 3824449201) ^ 196569 := by rw [pow_add]
          _ = 695837794 := by rw [factor_6_17]; decide
      have factor_6_19 : (7 : ZMod 3824449201) ^ 786276 = 1642462923 := by
        calc
          (7 : ZMod 3824449201) ^ 786276 = (7 : ZMod 3824449201) ^ (393138 + 393138) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 393138 * (7 : ZMod 3824449201) ^ 393138 := by rw [pow_add]
          _ = 1642462923 := by rw [factor_6_18]; decide
      have factor_6_20 : (7 : ZMod 3824449201) ^ 1572553 = 1204138814 := by
        calc
          (7 : ZMod 3824449201) ^ 1572553 = (7 : ZMod 3824449201) ^ (786276 + 786276 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 786276 * (7 : ZMod 3824449201) ^ 786276) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1204138814 := by rw [factor_6_19]; decide
      have factor_6_21 : (7 : ZMod 3824449201) ^ 3145106 = 2438100433 := by
        calc
          (7 : ZMod 3824449201) ^ 3145106 = (7 : ZMod 3824449201) ^ (1572553 + 1572553) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 1572553 * (7 : ZMod 3824449201) ^ 1572553 := by rw [pow_add]
          _ = 2438100433 := by rw [factor_6_20]; decide
      have factor_6_22 : (7 : ZMod 3824449201) ^ 6290212 = 125584695 := by
        calc
          (7 : ZMod 3824449201) ^ 6290212 = (7 : ZMod 3824449201) ^ (3145106 + 3145106) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 3145106 * (7 : ZMod 3824449201) ^ 3145106 := by rw [pow_add]
          _ = 125584695 := by rw [factor_6_21]; decide
      have factor_6_23 : (7 : ZMod 3824449201) ^ 12580425 = 951032914 := by
        calc
          (7 : ZMod 3824449201) ^ 12580425 = (7 : ZMod 3824449201) ^ (6290212 + 6290212 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 6290212 * (7 : ZMod 3824449201) ^ 6290212) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 951032914 := by rw [factor_6_22]; decide
      have factor_6_24 : (7 : ZMod 3824449201) ^ 25160850 = 191338668 := by
        calc
          (7 : ZMod 3824449201) ^ 25160850 = (7 : ZMod 3824449201) ^ (12580425 + 12580425) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 12580425 * (7 : ZMod 3824449201) ^ 12580425 := by rw [pow_add]
          _ = 191338668 := by rw [factor_6_23]; decide
      have factor_6_25 : (7 : ZMod 3824449201) ^ 50321700 = 1256489077 := by
        calc
          (7 : ZMod 3824449201) ^ 50321700 = (7 : ZMod 3824449201) ^ (25160850 + 25160850) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 25160850 * (7 : ZMod 3824449201) ^ 25160850 := by rw [pow_add]
          _ = 1256489077 := by rw [factor_6_24]; decide
      have factor_6_26 : (7 : ZMod 3824449201) ^ 100643400 = 3005282318 := by
        calc
          (7 : ZMod 3824449201) ^ 100643400 = (7 : ZMod 3824449201) ^ (50321700 + 50321700) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 50321700 * (7 : ZMod 3824449201) ^ 50321700 := by rw [pow_add]
          _ = 3005282318 := by rw [factor_6_25]; decide
      have factor_6_27 : (7 : ZMod 3824449201) ^ 201286800 = 1820799398 := by
        calc
          (7 : ZMod 3824449201) ^ 201286800 = (7 : ZMod 3824449201) ^ (100643400 + 100643400) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 100643400 * (7 : ZMod 3824449201) ^ 100643400 := by rw [pow_add]
          _ = 1820799398 := by rw [factor_6_26]; decide
      change (7 : ZMod 3824449201) ^ 201286800 ≠ 1
      rw [factor_6_27]
      decide
    ·
      have factor_7_0 : (7 : ZMod 3824449201) ^ 1 = 7 := by norm_num
      have factor_7_1 : (7 : ZMod 3824449201) ^ 2 = 49 := by
        calc
          (7 : ZMod 3824449201) ^ 2 = (7 : ZMod 3824449201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 1 * (7 : ZMod 3824449201) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_7_0]; decide
      have factor_7_2 : (7 : ZMod 3824449201) ^ 4 = 2401 := by
        calc
          (7 : ZMod 3824449201) ^ 4 = (7 : ZMod 3824449201) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 2 * (7 : ZMod 3824449201) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_7_1]; decide
      have factor_7_3 : (7 : ZMod 3824449201) ^ 9 = 40353607 := by
        calc
          (7 : ZMod 3824449201) ^ 9 = (7 : ZMod 3824449201) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 4 * (7 : ZMod 3824449201) ^ 4) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 40353607 := by rw [factor_7_2]; decide
      have factor_7_4 : (7 : ZMod 3824449201) ^ 19 = 1959418211 := by
        calc
          (7 : ZMod 3824449201) ^ 19 = (7 : ZMod 3824449201) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 9 * (7 : ZMod 3824449201) ^ 9) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1959418211 := by rw [factor_7_3]; decide
      have factor_7_5 : (7 : ZMod 3824449201) ^ 39 = 1234276496 := by
        calc
          (7 : ZMod 3824449201) ^ 39 = (7 : ZMod 3824449201) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 19 * (7 : ZMod 3824449201) ^ 19) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1234276496 := by rw [factor_7_4]; decide
      have factor_7_6 : (7 : ZMod 3824449201) ^ 79 = 2195469416 := by
        calc
          (7 : ZMod 3824449201) ^ 79 = (7 : ZMod 3824449201) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 39 * (7 : ZMod 3824449201) ^ 39) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 2195469416 := by rw [factor_7_5]; decide
      have factor_7_7 : (7 : ZMod 3824449201) ^ 158 = 497239577 := by
        calc
          (7 : ZMod 3824449201) ^ 158 = (7 : ZMod 3824449201) ^ (79 + 79) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 79 * (7 : ZMod 3824449201) ^ 79 := by rw [pow_add]
          _ = 497239577 := by rw [factor_7_6]; decide
      have factor_7_8 : (7 : ZMod 3824449201) ^ 317 = 1961185607 := by
        calc
          (7 : ZMod 3824449201) ^ 317 = (7 : ZMod 3824449201) ^ (158 + 158 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 158 * (7 : ZMod 3824449201) ^ 158) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1961185607 := by rw [factor_7_7]; decide
      have factor_7_9 : (7 : ZMod 3824449201) ^ 634 = 2968846339 := by
        calc
          (7 : ZMod 3824449201) ^ 634 = (7 : ZMod 3824449201) ^ (317 + 317) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 317 * (7 : ZMod 3824449201) ^ 317 := by rw [pow_add]
          _ = 2968846339 := by rw [factor_7_8]; decide
      have factor_7_10 : (7 : ZMod 3824449201) ^ 1268 = 2054032224 := by
        calc
          (7 : ZMod 3824449201) ^ 1268 = (7 : ZMod 3824449201) ^ (634 + 634) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 634 * (7 : ZMod 3824449201) ^ 634 := by rw [pow_add]
          _ = 2054032224 := by rw [factor_7_9]; decide
      have factor_7_11 : (7 : ZMod 3824449201) ^ 2537 = 2194785746 := by
        calc
          (7 : ZMod 3824449201) ^ 2537 = (7 : ZMod 3824449201) ^ (1268 + 1268 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 1268 * (7 : ZMod 3824449201) ^ 1268) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 2194785746 := by rw [factor_7_10]; decide
      have factor_7_12 : (7 : ZMod 3824449201) ^ 5074 = 3674767053 := by
        calc
          (7 : ZMod 3824449201) ^ 5074 = (7 : ZMod 3824449201) ^ (2537 + 2537) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 2537 * (7 : ZMod 3824449201) ^ 2537 := by rw [pow_add]
          _ = 3674767053 := by rw [factor_7_11]; decide
      have factor_7_13 : (7 : ZMod 3824449201) ^ 10148 = 1446820011 := by
        calc
          (7 : ZMod 3824449201) ^ 10148 = (7 : ZMod 3824449201) ^ (5074 + 5074) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 5074 * (7 : ZMod 3824449201) ^ 5074 := by rw [pow_add]
          _ = 1446820011 := by rw [factor_7_12]; decide
      have factor_7_14 : (7 : ZMod 3824449201) ^ 20297 = 2291097806 := by
        calc
          (7 : ZMod 3824449201) ^ 20297 = (7 : ZMod 3824449201) ^ (10148 + 10148 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 10148 * (7 : ZMod 3824449201) ^ 10148) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 2291097806 := by rw [factor_7_13]; decide
      have factor_7_15 : (7 : ZMod 3824449201) ^ 40595 = 2492958919 := by
        calc
          (7 : ZMod 3824449201) ^ 40595 = (7 : ZMod 3824449201) ^ (20297 + 20297 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 20297 * (7 : ZMod 3824449201) ^ 20297) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 2492958919 := by rw [factor_7_14]; decide
      have factor_7_16 : (7 : ZMod 3824449201) ^ 81191 = 2026578867 := by
        calc
          (7 : ZMod 3824449201) ^ 81191 = (7 : ZMod 3824449201) ^ (40595 + 40595 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 40595 * (7 : ZMod 3824449201) ^ 40595) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 2026578867 := by rw [factor_7_15]; decide
      have factor_7_17 : (7 : ZMod 3824449201) ^ 162383 = 1586218431 := by
        calc
          (7 : ZMod 3824449201) ^ 162383 = (7 : ZMod 3824449201) ^ (81191 + 81191 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 81191 * (7 : ZMod 3824449201) ^ 81191) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1586218431 := by rw [factor_7_16]; decide
      have factor_7_18 : (7 : ZMod 3824449201) ^ 324766 = 995263202 := by
        calc
          (7 : ZMod 3824449201) ^ 324766 = (7 : ZMod 3824449201) ^ (162383 + 162383) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 162383 * (7 : ZMod 3824449201) ^ 162383 := by rw [pow_add]
          _ = 995263202 := by rw [factor_7_17]; decide
      have factor_7_19 : (7 : ZMod 3824449201) ^ 649532 = 3346888891 := by
        calc
          (7 : ZMod 3824449201) ^ 649532 = (7 : ZMod 3824449201) ^ (324766 + 324766) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 324766 * (7 : ZMod 3824449201) ^ 324766 := by rw [pow_add]
          _ = 3346888891 := by rw [factor_7_18]; decide
      have factor_7_20 : (7 : ZMod 3824449201) ^ 1299065 = 537679639 := by
        calc
          (7 : ZMod 3824449201) ^ 1299065 = (7 : ZMod 3824449201) ^ (649532 + 649532 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 649532 * (7 : ZMod 3824449201) ^ 649532) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 537679639 := by rw [factor_7_19]; decide
      have factor_7_21 : (7 : ZMod 3824449201) ^ 2598131 = 3020281664 := by
        calc
          (7 : ZMod 3824449201) ^ 2598131 = (7 : ZMod 3824449201) ^ (1299065 + 1299065 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 1299065 * (7 : ZMod 3824449201) ^ 1299065) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 3020281664 := by rw [factor_7_20]; decide
      have factor_7_22 : (7 : ZMod 3824449201) ^ 5196262 = 3458201135 := by
        calc
          (7 : ZMod 3824449201) ^ 5196262 = (7 : ZMod 3824449201) ^ (2598131 + 2598131) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 2598131 * (7 : ZMod 3824449201) ^ 2598131 := by rw [pow_add]
          _ = 3458201135 := by rw [factor_7_21]; decide
      have factor_7_23 : (7 : ZMod 3824449201) ^ 10392525 = 1190626879 := by
        calc
          (7 : ZMod 3824449201) ^ 10392525 = (7 : ZMod 3824449201) ^ (5196262 + 5196262 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = ((7 : ZMod 3824449201) ^ 5196262 * (7 : ZMod 3824449201) ^ 5196262) * (7 : ZMod 3824449201) := by rw [pow_succ, pow_add]
          _ = 1190626879 := by rw [factor_7_22]; decide
      have factor_7_24 : (7 : ZMod 3824449201) ^ 20785050 = 2976121283 := by
        calc
          (7 : ZMod 3824449201) ^ 20785050 = (7 : ZMod 3824449201) ^ (10392525 + 10392525) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 10392525 * (7 : ZMod 3824449201) ^ 10392525 := by rw [pow_add]
          _ = 2976121283 := by rw [factor_7_23]; decide
      have factor_7_25 : (7 : ZMod 3824449201) ^ 41570100 = 846846355 := by
        calc
          (7 : ZMod 3824449201) ^ 41570100 = (7 : ZMod 3824449201) ^ (20785050 + 20785050) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 20785050 * (7 : ZMod 3824449201) ^ 20785050 := by rw [pow_add]
          _ = 846846355 := by rw [factor_7_24]; decide
      have factor_7_26 : (7 : ZMod 3824449201) ^ 83140200 = 1506815954 := by
        calc
          (7 : ZMod 3824449201) ^ 83140200 = (7 : ZMod 3824449201) ^ (41570100 + 41570100) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 41570100 * (7 : ZMod 3824449201) ^ 41570100 := by rw [pow_add]
          _ = 1506815954 := by rw [factor_7_25]; decide
      have factor_7_27 : (7 : ZMod 3824449201) ^ 166280400 = 2529521341 := by
        calc
          (7 : ZMod 3824449201) ^ 166280400 = (7 : ZMod 3824449201) ^ (83140200 + 83140200) :=
            congrArg (fun n : ℕ => (7 : ZMod 3824449201) ^ n) (by norm_num)
          _ = (7 : ZMod 3824449201) ^ 83140200 * (7 : ZMod 3824449201) ^ 83140200 := by rw [pow_add]
          _ = 2529521341 := by rw [factor_7_26]; decide
      change (7 : ZMod 3824449201) ^ 166280400 ≠ 1
      rw [factor_7_27]
      decide

#print axioms prime_lucas_3824449201

end TotientTailPeriodKiller
end Erdos249257
