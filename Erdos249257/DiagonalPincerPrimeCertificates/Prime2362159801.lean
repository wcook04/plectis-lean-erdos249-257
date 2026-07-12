import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=27 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_2362159801 : Nat.Prime 2362159801 := by
  apply lucas_primality 2362159801 (37 : ZMod 2362159801)
  ·
      have fermat_0 : (37 : ZMod 2362159801) ^ 1 = 37 := by norm_num
      have fermat_1 : (37 : ZMod 2362159801) ^ 2 = 1369 := by
        calc
          (37 : ZMod 2362159801) ^ 2 = (37 : ZMod 2362159801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 1 * (37 : ZMod 2362159801) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [fermat_0]; decide
      have fermat_2 : (37 : ZMod 2362159801) ^ 4 = 1874161 := by
        calc
          (37 : ZMod 2362159801) ^ 4 = (37 : ZMod 2362159801) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 2 * (37 : ZMod 2362159801) ^ 2 := by rw [pow_add]
          _ = 1874161 := by rw [fermat_1]; decide
      have fermat_3 : (37 : ZMod 2362159801) ^ 8 = 2309989635 := by
        calc
          (37 : ZMod 2362159801) ^ 8 = (37 : ZMod 2362159801) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 4 * (37 : ZMod 2362159801) ^ 4 := by rw [pow_add]
          _ = 2309989635 := by rw [fermat_2]; decide
      have fermat_4 : (37 : ZMod 2362159801) ^ 17 = 1872690457 := by
        calc
          (37 : ZMod 2362159801) ^ 17 = (37 : ZMod 2362159801) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 8 * (37 : ZMod 2362159801) ^ 8) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1872690457 := by rw [fermat_3]; decide
      have fermat_5 : (37 : ZMod 2362159801) ^ 35 = 657887126 := by
        calc
          (37 : ZMod 2362159801) ^ 35 = (37 : ZMod 2362159801) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 17 * (37 : ZMod 2362159801) ^ 17) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 657887126 := by rw [fermat_4]; decide
      have fermat_6 : (37 : ZMod 2362159801) ^ 70 = 1027051176 := by
        calc
          (37 : ZMod 2362159801) ^ 70 = (37 : ZMod 2362159801) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 35 * (37 : ZMod 2362159801) ^ 35 := by rw [pow_add]
          _ = 1027051176 := by rw [fermat_5]; decide
      have fermat_7 : (37 : ZMod 2362159801) ^ 140 = 1727815041 := by
        calc
          (37 : ZMod 2362159801) ^ 140 = (37 : ZMod 2362159801) ^ (70 + 70) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 70 * (37 : ZMod 2362159801) ^ 70 := by rw [pow_add]
          _ = 1727815041 := by rw [fermat_6]; decide
      have fermat_8 : (37 : ZMod 2362159801) ^ 281 = 1996002544 := by
        calc
          (37 : ZMod 2362159801) ^ 281 = (37 : ZMod 2362159801) ^ (140 + 140 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 140 * (37 : ZMod 2362159801) ^ 140) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1996002544 := by rw [fermat_7]; decide
      have fermat_9 : (37 : ZMod 2362159801) ^ 563 = 1434357769 := by
        calc
          (37 : ZMod 2362159801) ^ 563 = (37 : ZMod 2362159801) ^ (281 + 281 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 281 * (37 : ZMod 2362159801) ^ 281) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1434357769 := by rw [fermat_8]; decide
      have fermat_10 : (37 : ZMod 2362159801) ^ 1126 = 1225568729 := by
        calc
          (37 : ZMod 2362159801) ^ 1126 = (37 : ZMod 2362159801) ^ (563 + 563) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 563 * (37 : ZMod 2362159801) ^ 563 := by rw [pow_add]
          _ = 1225568729 := by rw [fermat_9]; decide
      have fermat_11 : (37 : ZMod 2362159801) ^ 2252 = 1573504562 := by
        calc
          (37 : ZMod 2362159801) ^ 2252 = (37 : ZMod 2362159801) ^ (1126 + 1126) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 1126 * (37 : ZMod 2362159801) ^ 1126 := by rw [pow_add]
          _ = 1573504562 := by rw [fermat_10]; decide
      have fermat_12 : (37 : ZMod 2362159801) ^ 4505 = 2268963777 := by
        calc
          (37 : ZMod 2362159801) ^ 4505 = (37 : ZMod 2362159801) ^ (2252 + 2252 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 2252 * (37 : ZMod 2362159801) ^ 2252) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 2268963777 := by rw [fermat_11]; decide
      have fermat_13 : (37 : ZMod 2362159801) ^ 9010 = 290157845 := by
        calc
          (37 : ZMod 2362159801) ^ 9010 = (37 : ZMod 2362159801) ^ (4505 + 4505) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 4505 * (37 : ZMod 2362159801) ^ 4505 := by rw [pow_add]
          _ = 290157845 := by rw [fermat_12]; decide
      have fermat_14 : (37 : ZMod 2362159801) ^ 18021 = 1577919543 := by
        calc
          (37 : ZMod 2362159801) ^ 18021 = (37 : ZMod 2362159801) ^ (9010 + 9010 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 9010 * (37 : ZMod 2362159801) ^ 9010) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1577919543 := by rw [fermat_13]; decide
      have fermat_15 : (37 : ZMod 2362159801) ^ 36043 = 482153780 := by
        calc
          (37 : ZMod 2362159801) ^ 36043 = (37 : ZMod 2362159801) ^ (18021 + 18021 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 18021 * (37 : ZMod 2362159801) ^ 18021) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 482153780 := by rw [fermat_14]; decide
      have fermat_16 : (37 : ZMod 2362159801) ^ 72087 = 1224564333 := by
        calc
          (37 : ZMod 2362159801) ^ 72087 = (37 : ZMod 2362159801) ^ (36043 + 36043 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 36043 * (37 : ZMod 2362159801) ^ 36043) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1224564333 := by rw [fermat_15]; decide
      have fermat_17 : (37 : ZMod 2362159801) ^ 144174 = 531565412 := by
        calc
          (37 : ZMod 2362159801) ^ 144174 = (37 : ZMod 2362159801) ^ (72087 + 72087) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 72087 * (37 : ZMod 2362159801) ^ 72087 := by rw [pow_add]
          _ = 531565412 := by rw [fermat_16]; decide
      have fermat_18 : (37 : ZMod 2362159801) ^ 288349 = 1044823097 := by
        calc
          (37 : ZMod 2362159801) ^ 288349 = (37 : ZMod 2362159801) ^ (144174 + 144174 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 144174 * (37 : ZMod 2362159801) ^ 144174) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1044823097 := by rw [fermat_17]; decide
      have fermat_19 : (37 : ZMod 2362159801) ^ 576699 = 56935834 := by
        calc
          (37 : ZMod 2362159801) ^ 576699 = (37 : ZMod 2362159801) ^ (288349 + 288349 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 288349 * (37 : ZMod 2362159801) ^ 288349) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 56935834 := by rw [fermat_18]; decide
      have fermat_20 : (37 : ZMod 2362159801) ^ 1153398 = 449811415 := by
        calc
          (37 : ZMod 2362159801) ^ 1153398 = (37 : ZMod 2362159801) ^ (576699 + 576699) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 576699 * (37 : ZMod 2362159801) ^ 576699 := by rw [pow_add]
          _ = 449811415 := by rw [fermat_19]; decide
      have fermat_21 : (37 : ZMod 2362159801) ^ 2306796 = 276726032 := by
        calc
          (37 : ZMod 2362159801) ^ 2306796 = (37 : ZMod 2362159801) ^ (1153398 + 1153398) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 1153398 * (37 : ZMod 2362159801) ^ 1153398 := by rw [pow_add]
          _ = 276726032 := by rw [fermat_20]; decide
      have fermat_22 : (37 : ZMod 2362159801) ^ 4613593 = 1197674552 := by
        calc
          (37 : ZMod 2362159801) ^ 4613593 = (37 : ZMod 2362159801) ^ (2306796 + 2306796 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 2306796 * (37 : ZMod 2362159801) ^ 2306796) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1197674552 := by rw [fermat_21]; decide
      have fermat_23 : (37 : ZMod 2362159801) ^ 9227186 = 1278265922 := by
        calc
          (37 : ZMod 2362159801) ^ 9227186 = (37 : ZMod 2362159801) ^ (4613593 + 4613593) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 4613593 * (37 : ZMod 2362159801) ^ 4613593 := by rw [pow_add]
          _ = 1278265922 := by rw [fermat_22]; decide
      have fermat_24 : (37 : ZMod 2362159801) ^ 18454373 = 1660402034 := by
        calc
          (37 : ZMod 2362159801) ^ 18454373 = (37 : ZMod 2362159801) ^ (9227186 + 9227186 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 9227186 * (37 : ZMod 2362159801) ^ 9227186) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1660402034 := by rw [fermat_23]; decide
      have fermat_25 : (37 : ZMod 2362159801) ^ 36908746 = 60261113 := by
        calc
          (37 : ZMod 2362159801) ^ 36908746 = (37 : ZMod 2362159801) ^ (18454373 + 18454373) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 18454373 * (37 : ZMod 2362159801) ^ 18454373 := by rw [pow_add]
          _ = 60261113 := by rw [fermat_24]; decide
      have fermat_26 : (37 : ZMod 2362159801) ^ 73817493 = 1555340916 := by
        calc
          (37 : ZMod 2362159801) ^ 73817493 = (37 : ZMod 2362159801) ^ (36908746 + 36908746 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 36908746 * (37 : ZMod 2362159801) ^ 36908746) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1555340916 := by rw [fermat_25]; decide
      have fermat_27 : (37 : ZMod 2362159801) ^ 147634987 = 229592231 := by
        calc
          (37 : ZMod 2362159801) ^ 147634987 = (37 : ZMod 2362159801) ^ (73817493 + 73817493 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 73817493 * (37 : ZMod 2362159801) ^ 73817493) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 229592231 := by rw [fermat_26]; decide
      have fermat_28 : (37 : ZMod 2362159801) ^ 295269975 = 6473747 := by
        calc
          (37 : ZMod 2362159801) ^ 295269975 = (37 : ZMod 2362159801) ^ (147634987 + 147634987 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 147634987 * (37 : ZMod 2362159801) ^ 147634987) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 6473747 := by rw [fermat_27]; decide
      have fermat_29 : (37 : ZMod 2362159801) ^ 590539950 = 2323190468 := by
        calc
          (37 : ZMod 2362159801) ^ 590539950 = (37 : ZMod 2362159801) ^ (295269975 + 295269975) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 295269975 * (37 : ZMod 2362159801) ^ 295269975 := by rw [pow_add]
          _ = 2323190468 := by rw [fermat_28]; decide
      have fermat_30 : (37 : ZMod 2362159801) ^ 1181079900 = 2362159800 := by
        calc
          (37 : ZMod 2362159801) ^ 1181079900 = (37 : ZMod 2362159801) ^ (590539950 + 590539950) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 590539950 * (37 : ZMod 2362159801) ^ 590539950 := by rw [pow_add]
          _ = 2362159800 := by rw [fermat_29]; decide
      have fermat_31 : (37 : ZMod 2362159801) ^ 2362159800 = 1 := by
        calc
          (37 : ZMod 2362159801) ^ 2362159800 = (37 : ZMod 2362159801) ^ (1181079900 + 1181079900) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 1181079900 * (37 : ZMod 2362159801) ^ 1181079900 := by rw [pow_add]
          _ = 1 := by rw [fermat_30]; decide
      simpa using fermat_31
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 3), (5, 2), (7, 1), (11, 1), (13, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 3), (5, 2), (7, 1), (11, 1), (13, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod = 2362159801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (37 : ZMod 2362159801) ^ 1 = 37 := by norm_num
      have factor_0_1 : (37 : ZMod 2362159801) ^ 2 = 1369 := by
        calc
          (37 : ZMod 2362159801) ^ 2 = (37 : ZMod 2362159801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 1 * (37 : ZMod 2362159801) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_0_0]; decide
      have factor_0_2 : (37 : ZMod 2362159801) ^ 4 = 1874161 := by
        calc
          (37 : ZMod 2362159801) ^ 4 = (37 : ZMod 2362159801) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 2 * (37 : ZMod 2362159801) ^ 2 := by rw [pow_add]
          _ = 1874161 := by rw [factor_0_1]; decide
      have factor_0_3 : (37 : ZMod 2362159801) ^ 8 = 2309989635 := by
        calc
          (37 : ZMod 2362159801) ^ 8 = (37 : ZMod 2362159801) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 4 * (37 : ZMod 2362159801) ^ 4 := by rw [pow_add]
          _ = 2309989635 := by rw [factor_0_2]; decide
      have factor_0_4 : (37 : ZMod 2362159801) ^ 17 = 1872690457 := by
        calc
          (37 : ZMod 2362159801) ^ 17 = (37 : ZMod 2362159801) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 8 * (37 : ZMod 2362159801) ^ 8) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1872690457 := by rw [factor_0_3]; decide
      have factor_0_5 : (37 : ZMod 2362159801) ^ 35 = 657887126 := by
        calc
          (37 : ZMod 2362159801) ^ 35 = (37 : ZMod 2362159801) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 17 * (37 : ZMod 2362159801) ^ 17) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 657887126 := by rw [factor_0_4]; decide
      have factor_0_6 : (37 : ZMod 2362159801) ^ 70 = 1027051176 := by
        calc
          (37 : ZMod 2362159801) ^ 70 = (37 : ZMod 2362159801) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 35 * (37 : ZMod 2362159801) ^ 35 := by rw [pow_add]
          _ = 1027051176 := by rw [factor_0_5]; decide
      have factor_0_7 : (37 : ZMod 2362159801) ^ 140 = 1727815041 := by
        calc
          (37 : ZMod 2362159801) ^ 140 = (37 : ZMod 2362159801) ^ (70 + 70) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 70 * (37 : ZMod 2362159801) ^ 70 := by rw [pow_add]
          _ = 1727815041 := by rw [factor_0_6]; decide
      have factor_0_8 : (37 : ZMod 2362159801) ^ 281 = 1996002544 := by
        calc
          (37 : ZMod 2362159801) ^ 281 = (37 : ZMod 2362159801) ^ (140 + 140 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 140 * (37 : ZMod 2362159801) ^ 140) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1996002544 := by rw [factor_0_7]; decide
      have factor_0_9 : (37 : ZMod 2362159801) ^ 563 = 1434357769 := by
        calc
          (37 : ZMod 2362159801) ^ 563 = (37 : ZMod 2362159801) ^ (281 + 281 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 281 * (37 : ZMod 2362159801) ^ 281) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1434357769 := by rw [factor_0_8]; decide
      have factor_0_10 : (37 : ZMod 2362159801) ^ 1126 = 1225568729 := by
        calc
          (37 : ZMod 2362159801) ^ 1126 = (37 : ZMod 2362159801) ^ (563 + 563) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 563 * (37 : ZMod 2362159801) ^ 563 := by rw [pow_add]
          _ = 1225568729 := by rw [factor_0_9]; decide
      have factor_0_11 : (37 : ZMod 2362159801) ^ 2252 = 1573504562 := by
        calc
          (37 : ZMod 2362159801) ^ 2252 = (37 : ZMod 2362159801) ^ (1126 + 1126) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 1126 * (37 : ZMod 2362159801) ^ 1126 := by rw [pow_add]
          _ = 1573504562 := by rw [factor_0_10]; decide
      have factor_0_12 : (37 : ZMod 2362159801) ^ 4505 = 2268963777 := by
        calc
          (37 : ZMod 2362159801) ^ 4505 = (37 : ZMod 2362159801) ^ (2252 + 2252 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 2252 * (37 : ZMod 2362159801) ^ 2252) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 2268963777 := by rw [factor_0_11]; decide
      have factor_0_13 : (37 : ZMod 2362159801) ^ 9010 = 290157845 := by
        calc
          (37 : ZMod 2362159801) ^ 9010 = (37 : ZMod 2362159801) ^ (4505 + 4505) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 4505 * (37 : ZMod 2362159801) ^ 4505 := by rw [pow_add]
          _ = 290157845 := by rw [factor_0_12]; decide
      have factor_0_14 : (37 : ZMod 2362159801) ^ 18021 = 1577919543 := by
        calc
          (37 : ZMod 2362159801) ^ 18021 = (37 : ZMod 2362159801) ^ (9010 + 9010 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 9010 * (37 : ZMod 2362159801) ^ 9010) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1577919543 := by rw [factor_0_13]; decide
      have factor_0_15 : (37 : ZMod 2362159801) ^ 36043 = 482153780 := by
        calc
          (37 : ZMod 2362159801) ^ 36043 = (37 : ZMod 2362159801) ^ (18021 + 18021 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 18021 * (37 : ZMod 2362159801) ^ 18021) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 482153780 := by rw [factor_0_14]; decide
      have factor_0_16 : (37 : ZMod 2362159801) ^ 72087 = 1224564333 := by
        calc
          (37 : ZMod 2362159801) ^ 72087 = (37 : ZMod 2362159801) ^ (36043 + 36043 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 36043 * (37 : ZMod 2362159801) ^ 36043) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1224564333 := by rw [factor_0_15]; decide
      have factor_0_17 : (37 : ZMod 2362159801) ^ 144174 = 531565412 := by
        calc
          (37 : ZMod 2362159801) ^ 144174 = (37 : ZMod 2362159801) ^ (72087 + 72087) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 72087 * (37 : ZMod 2362159801) ^ 72087 := by rw [pow_add]
          _ = 531565412 := by rw [factor_0_16]; decide
      have factor_0_18 : (37 : ZMod 2362159801) ^ 288349 = 1044823097 := by
        calc
          (37 : ZMod 2362159801) ^ 288349 = (37 : ZMod 2362159801) ^ (144174 + 144174 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 144174 * (37 : ZMod 2362159801) ^ 144174) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1044823097 := by rw [factor_0_17]; decide
      have factor_0_19 : (37 : ZMod 2362159801) ^ 576699 = 56935834 := by
        calc
          (37 : ZMod 2362159801) ^ 576699 = (37 : ZMod 2362159801) ^ (288349 + 288349 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 288349 * (37 : ZMod 2362159801) ^ 288349) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 56935834 := by rw [factor_0_18]; decide
      have factor_0_20 : (37 : ZMod 2362159801) ^ 1153398 = 449811415 := by
        calc
          (37 : ZMod 2362159801) ^ 1153398 = (37 : ZMod 2362159801) ^ (576699 + 576699) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 576699 * (37 : ZMod 2362159801) ^ 576699 := by rw [pow_add]
          _ = 449811415 := by rw [factor_0_19]; decide
      have factor_0_21 : (37 : ZMod 2362159801) ^ 2306796 = 276726032 := by
        calc
          (37 : ZMod 2362159801) ^ 2306796 = (37 : ZMod 2362159801) ^ (1153398 + 1153398) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 1153398 * (37 : ZMod 2362159801) ^ 1153398 := by rw [pow_add]
          _ = 276726032 := by rw [factor_0_20]; decide
      have factor_0_22 : (37 : ZMod 2362159801) ^ 4613593 = 1197674552 := by
        calc
          (37 : ZMod 2362159801) ^ 4613593 = (37 : ZMod 2362159801) ^ (2306796 + 2306796 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 2306796 * (37 : ZMod 2362159801) ^ 2306796) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1197674552 := by rw [factor_0_21]; decide
      have factor_0_23 : (37 : ZMod 2362159801) ^ 9227186 = 1278265922 := by
        calc
          (37 : ZMod 2362159801) ^ 9227186 = (37 : ZMod 2362159801) ^ (4613593 + 4613593) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 4613593 * (37 : ZMod 2362159801) ^ 4613593 := by rw [pow_add]
          _ = 1278265922 := by rw [factor_0_22]; decide
      have factor_0_24 : (37 : ZMod 2362159801) ^ 18454373 = 1660402034 := by
        calc
          (37 : ZMod 2362159801) ^ 18454373 = (37 : ZMod 2362159801) ^ (9227186 + 9227186 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 9227186 * (37 : ZMod 2362159801) ^ 9227186) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1660402034 := by rw [factor_0_23]; decide
      have factor_0_25 : (37 : ZMod 2362159801) ^ 36908746 = 60261113 := by
        calc
          (37 : ZMod 2362159801) ^ 36908746 = (37 : ZMod 2362159801) ^ (18454373 + 18454373) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 18454373 * (37 : ZMod 2362159801) ^ 18454373 := by rw [pow_add]
          _ = 60261113 := by rw [factor_0_24]; decide
      have factor_0_26 : (37 : ZMod 2362159801) ^ 73817493 = 1555340916 := by
        calc
          (37 : ZMod 2362159801) ^ 73817493 = (37 : ZMod 2362159801) ^ (36908746 + 36908746 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 36908746 * (37 : ZMod 2362159801) ^ 36908746) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1555340916 := by rw [factor_0_25]; decide
      have factor_0_27 : (37 : ZMod 2362159801) ^ 147634987 = 229592231 := by
        calc
          (37 : ZMod 2362159801) ^ 147634987 = (37 : ZMod 2362159801) ^ (73817493 + 73817493 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 73817493 * (37 : ZMod 2362159801) ^ 73817493) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 229592231 := by rw [factor_0_26]; decide
      have factor_0_28 : (37 : ZMod 2362159801) ^ 295269975 = 6473747 := by
        calc
          (37 : ZMod 2362159801) ^ 295269975 = (37 : ZMod 2362159801) ^ (147634987 + 147634987 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 147634987 * (37 : ZMod 2362159801) ^ 147634987) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 6473747 := by rw [factor_0_27]; decide
      have factor_0_29 : (37 : ZMod 2362159801) ^ 590539950 = 2323190468 := by
        calc
          (37 : ZMod 2362159801) ^ 590539950 = (37 : ZMod 2362159801) ^ (295269975 + 295269975) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 295269975 * (37 : ZMod 2362159801) ^ 295269975 := by rw [pow_add]
          _ = 2323190468 := by rw [factor_0_28]; decide
      have factor_0_30 : (37 : ZMod 2362159801) ^ 1181079900 = 2362159800 := by
        calc
          (37 : ZMod 2362159801) ^ 1181079900 = (37 : ZMod 2362159801) ^ (590539950 + 590539950) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 590539950 * (37 : ZMod 2362159801) ^ 590539950 := by rw [pow_add]
          _ = 2362159800 := by rw [factor_0_29]; decide
      change (37 : ZMod 2362159801) ^ 1181079900 ≠ 1
      rw [factor_0_30]
      decide
    ·
      have factor_1_0 : (37 : ZMod 2362159801) ^ 1 = 37 := by norm_num
      have factor_1_1 : (37 : ZMod 2362159801) ^ 2 = 1369 := by
        calc
          (37 : ZMod 2362159801) ^ 2 = (37 : ZMod 2362159801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 1 * (37 : ZMod 2362159801) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_1_0]; decide
      have factor_1_2 : (37 : ZMod 2362159801) ^ 5 = 69343957 := by
        calc
          (37 : ZMod 2362159801) ^ 5 = (37 : ZMod 2362159801) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 2 * (37 : ZMod 2362159801) ^ 2) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 69343957 := by rw [factor_1_1]; decide
      have factor_1_3 : (37 : ZMod 2362159801) ^ 11 = 681398921 := by
        calc
          (37 : ZMod 2362159801) ^ 11 = (37 : ZMod 2362159801) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 5 * (37 : ZMod 2362159801) ^ 5) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 681398921 := by rw [factor_1_2]; decide
      have factor_1_4 : (37 : ZMod 2362159801) ^ 23 = 2005481821 := by
        calc
          (37 : ZMod 2362159801) ^ 23 = (37 : ZMod 2362159801) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 11 * (37 : ZMod 2362159801) ^ 11) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 2005481821 := by rw [factor_1_3]; decide
      have factor_1_5 : (37 : ZMod 2362159801) ^ 46 = 863412056 := by
        calc
          (37 : ZMod 2362159801) ^ 46 = (37 : ZMod 2362159801) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 23 * (37 : ZMod 2362159801) ^ 23 := by rw [pow_add]
          _ = 863412056 := by rw [factor_1_4]; decide
      have factor_1_6 : (37 : ZMod 2362159801) ^ 93 = 2286139705 := by
        calc
          (37 : ZMod 2362159801) ^ 93 = (37 : ZMod 2362159801) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 46 * (37 : ZMod 2362159801) ^ 46) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 2286139705 := by rw [factor_1_5]; decide
      have factor_1_7 : (37 : ZMod 2362159801) ^ 187 = 570337206 := by
        calc
          (37 : ZMod 2362159801) ^ 187 = (37 : ZMod 2362159801) ^ (93 + 93 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 93 * (37 : ZMod 2362159801) ^ 93) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 570337206 := by rw [factor_1_6]; decide
      have factor_1_8 : (37 : ZMod 2362159801) ^ 375 = 2310840237 := by
        calc
          (37 : ZMod 2362159801) ^ 375 = (37 : ZMod 2362159801) ^ (187 + 187 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 187 * (37 : ZMod 2362159801) ^ 187) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 2310840237 := by rw [factor_1_7]; decide
      have factor_1_9 : (37 : ZMod 2362159801) ^ 750 = 492545743 := by
        calc
          (37 : ZMod 2362159801) ^ 750 = (37 : ZMod 2362159801) ^ (375 + 375) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 375 * (37 : ZMod 2362159801) ^ 375 := by rw [pow_add]
          _ = 492545743 := by rw [factor_1_8]; decide
      have factor_1_10 : (37 : ZMod 2362159801) ^ 1501 = 636325577 := by
        calc
          (37 : ZMod 2362159801) ^ 1501 = (37 : ZMod 2362159801) ^ (750 + 750 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 750 * (37 : ZMod 2362159801) ^ 750) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 636325577 := by rw [factor_1_9]; decide
      have factor_1_11 : (37 : ZMod 2362159801) ^ 3003 = 1736898499 := by
        calc
          (37 : ZMod 2362159801) ^ 3003 = (37 : ZMod 2362159801) ^ (1501 + 1501 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 1501 * (37 : ZMod 2362159801) ^ 1501) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1736898499 := by rw [factor_1_10]; decide
      have factor_1_12 : (37 : ZMod 2362159801) ^ 6007 = 1392356562 := by
        calc
          (37 : ZMod 2362159801) ^ 6007 = (37 : ZMod 2362159801) ^ (3003 + 3003 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 3003 * (37 : ZMod 2362159801) ^ 3003) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1392356562 := by rw [factor_1_11]; decide
      have factor_1_13 : (37 : ZMod 2362159801) ^ 12014 = 1220316393 := by
        calc
          (37 : ZMod 2362159801) ^ 12014 = (37 : ZMod 2362159801) ^ (6007 + 6007) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 6007 * (37 : ZMod 2362159801) ^ 6007 := by rw [pow_add]
          _ = 1220316393 := by rw [factor_1_12]; decide
      have factor_1_14 : (37 : ZMod 2362159801) ^ 24029 = 1701819635 := by
        calc
          (37 : ZMod 2362159801) ^ 24029 = (37 : ZMod 2362159801) ^ (12014 + 12014 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 12014 * (37 : ZMod 2362159801) ^ 12014) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1701819635 := by rw [factor_1_13]; decide
      have factor_1_15 : (37 : ZMod 2362159801) ^ 48058 = 816798712 := by
        calc
          (37 : ZMod 2362159801) ^ 48058 = (37 : ZMod 2362159801) ^ (24029 + 24029) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 24029 * (37 : ZMod 2362159801) ^ 24029 := by rw [pow_add]
          _ = 816798712 := by rw [factor_1_14]; decide
      have factor_1_16 : (37 : ZMod 2362159801) ^ 96116 = 1100521449 := by
        calc
          (37 : ZMod 2362159801) ^ 96116 = (37 : ZMod 2362159801) ^ (48058 + 48058) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 48058 * (37 : ZMod 2362159801) ^ 48058 := by rw [pow_add]
          _ = 1100521449 := by rw [factor_1_15]; decide
      have factor_1_17 : (37 : ZMod 2362159801) ^ 192233 = 154229878 := by
        calc
          (37 : ZMod 2362159801) ^ 192233 = (37 : ZMod 2362159801) ^ (96116 + 96116 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 96116 * (37 : ZMod 2362159801) ^ 96116) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 154229878 := by rw [factor_1_16]; decide
      have factor_1_18 : (37 : ZMod 2362159801) ^ 384466 = 558216924 := by
        calc
          (37 : ZMod 2362159801) ^ 384466 = (37 : ZMod 2362159801) ^ (192233 + 192233) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 192233 * (37 : ZMod 2362159801) ^ 192233 := by rw [pow_add]
          _ = 558216924 := by rw [factor_1_17]; decide
      have factor_1_19 : (37 : ZMod 2362159801) ^ 768932 = 503740404 := by
        calc
          (37 : ZMod 2362159801) ^ 768932 = (37 : ZMod 2362159801) ^ (384466 + 384466) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 384466 * (37 : ZMod 2362159801) ^ 384466 := by rw [pow_add]
          _ = 503740404 := by rw [factor_1_18]; decide
      have factor_1_20 : (37 : ZMod 2362159801) ^ 1537864 = 1609845680 := by
        calc
          (37 : ZMod 2362159801) ^ 1537864 = (37 : ZMod 2362159801) ^ (768932 + 768932) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 768932 * (37 : ZMod 2362159801) ^ 768932 := by rw [pow_add]
          _ = 1609845680 := by rw [factor_1_19]; decide
      have factor_1_21 : (37 : ZMod 2362159801) ^ 3075728 = 1150259351 := by
        calc
          (37 : ZMod 2362159801) ^ 3075728 = (37 : ZMod 2362159801) ^ (1537864 + 1537864) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 1537864 * (37 : ZMod 2362159801) ^ 1537864 := by rw [pow_add]
          _ = 1150259351 := by rw [factor_1_20]; decide
      have factor_1_22 : (37 : ZMod 2362159801) ^ 6151457 = 656249428 := by
        calc
          (37 : ZMod 2362159801) ^ 6151457 = (37 : ZMod 2362159801) ^ (3075728 + 3075728 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 3075728 * (37 : ZMod 2362159801) ^ 3075728) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 656249428 := by rw [factor_1_21]; decide
      have factor_1_23 : (37 : ZMod 2362159801) ^ 12302915 = 531573314 := by
        calc
          (37 : ZMod 2362159801) ^ 12302915 = (37 : ZMod 2362159801) ^ (6151457 + 6151457 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 6151457 * (37 : ZMod 2362159801) ^ 6151457) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 531573314 := by rw [factor_1_22]; decide
      have factor_1_24 : (37 : ZMod 2362159801) ^ 24605831 = 920644832 := by
        calc
          (37 : ZMod 2362159801) ^ 24605831 = (37 : ZMod 2362159801) ^ (12302915 + 12302915 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 12302915 * (37 : ZMod 2362159801) ^ 12302915) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 920644832 := by rw [factor_1_23]; decide
      have factor_1_25 : (37 : ZMod 2362159801) ^ 49211662 = 846972410 := by
        calc
          (37 : ZMod 2362159801) ^ 49211662 = (37 : ZMod 2362159801) ^ (24605831 + 24605831) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 24605831 * (37 : ZMod 2362159801) ^ 24605831 := by rw [pow_add]
          _ = 846972410 := by rw [factor_1_24]; decide
      have factor_1_26 : (37 : ZMod 2362159801) ^ 98423325 = 1895229959 := by
        calc
          (37 : ZMod 2362159801) ^ 98423325 = (37 : ZMod 2362159801) ^ (49211662 + 49211662 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 49211662 * (37 : ZMod 2362159801) ^ 49211662) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1895229959 := by rw [factor_1_25]; decide
      have factor_1_27 : (37 : ZMod 2362159801) ^ 196846650 = 1659918604 := by
        calc
          (37 : ZMod 2362159801) ^ 196846650 = (37 : ZMod 2362159801) ^ (98423325 + 98423325) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 98423325 * (37 : ZMod 2362159801) ^ 98423325 := by rw [pow_add]
          _ = 1659918604 := by rw [factor_1_26]; decide
      have factor_1_28 : (37 : ZMod 2362159801) ^ 393693300 = 1730847497 := by
        calc
          (37 : ZMod 2362159801) ^ 393693300 = (37 : ZMod 2362159801) ^ (196846650 + 196846650) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 196846650 * (37 : ZMod 2362159801) ^ 196846650 := by rw [pow_add]
          _ = 1730847497 := by rw [factor_1_27]; decide
      have factor_1_29 : (37 : ZMod 2362159801) ^ 787386600 = 1730847496 := by
        calc
          (37 : ZMod 2362159801) ^ 787386600 = (37 : ZMod 2362159801) ^ (393693300 + 393693300) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 393693300 * (37 : ZMod 2362159801) ^ 393693300 := by rw [pow_add]
          _ = 1730847496 := by rw [factor_1_28]; decide
      change (37 : ZMod 2362159801) ^ 787386600 ≠ 1
      rw [factor_1_29]
      decide
    ·
      have factor_2_0 : (37 : ZMod 2362159801) ^ 1 = 37 := by norm_num
      have factor_2_1 : (37 : ZMod 2362159801) ^ 3 = 50653 := by
        calc
          (37 : ZMod 2362159801) ^ 3 = (37 : ZMod 2362159801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 1 * (37 : ZMod 2362159801) ^ 1) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 50653 := by rw [factor_2_0]; decide
      have factor_2_2 : (37 : ZMod 2362159801) ^ 7 = 445485093 := by
        calc
          (37 : ZMod 2362159801) ^ 7 = (37 : ZMod 2362159801) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 3 * (37 : ZMod 2362159801) ^ 3) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 445485093 := by rw [factor_2_1]; decide
      have factor_2_3 : (37 : ZMod 2362159801) ^ 14 = 1382693002 := by
        calc
          (37 : ZMod 2362159801) ^ 14 = (37 : ZMod 2362159801) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 7 * (37 : ZMod 2362159801) ^ 7 := by rw [pow_add]
          _ = 1382693002 := by rw [factor_2_2]; decide
      have factor_2_4 : (37 : ZMod 2362159801) ^ 28 = 1758204039 := by
        calc
          (37 : ZMod 2362159801) ^ 28 = (37 : ZMod 2362159801) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 14 * (37 : ZMod 2362159801) ^ 14 := by rw [pow_add]
          _ = 1758204039 := by rw [factor_2_3]; decide
      have factor_2_5 : (37 : ZMod 2362159801) ^ 56 = 272319156 := by
        calc
          (37 : ZMod 2362159801) ^ 56 = (37 : ZMod 2362159801) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 28 * (37 : ZMod 2362159801) ^ 28 := by rw [pow_add]
          _ = 272319156 := by rw [factor_2_4]; decide
      have factor_2_6 : (37 : ZMod 2362159801) ^ 112 = 2342844704 := by
        calc
          (37 : ZMod 2362159801) ^ 112 = (37 : ZMod 2362159801) ^ (56 + 56) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 56 * (37 : ZMod 2362159801) ^ 56 := by rw [pow_add]
          _ = 2342844704 := by rw [factor_2_5]; decide
      have factor_2_7 : (37 : ZMod 2362159801) ^ 225 = 1068989856 := by
        calc
          (37 : ZMod 2362159801) ^ 225 = (37 : ZMod 2362159801) ^ (112 + 112 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 112 * (37 : ZMod 2362159801) ^ 112) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1068989856 := by rw [factor_2_6]; decide
      have factor_2_8 : (37 : ZMod 2362159801) ^ 450 = 682180294 := by
        calc
          (37 : ZMod 2362159801) ^ 450 = (37 : ZMod 2362159801) ^ (225 + 225) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 225 * (37 : ZMod 2362159801) ^ 225 := by rw [pow_add]
          _ = 682180294 := by rw [factor_2_7]; decide
      have factor_2_9 : (37 : ZMod 2362159801) ^ 901 = 1743601001 := by
        calc
          (37 : ZMod 2362159801) ^ 901 = (37 : ZMod 2362159801) ^ (450 + 450 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 450 * (37 : ZMod 2362159801) ^ 450) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1743601001 := by rw [factor_2_8]; decide
      have factor_2_10 : (37 : ZMod 2362159801) ^ 1802 = 251375041 := by
        calc
          (37 : ZMod 2362159801) ^ 1802 = (37 : ZMod 2362159801) ^ (901 + 901) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 901 * (37 : ZMod 2362159801) ^ 901 := by rw [pow_add]
          _ = 251375041 := by rw [factor_2_9]; decide
      have factor_2_11 : (37 : ZMod 2362159801) ^ 3604 = 1946419389 := by
        calc
          (37 : ZMod 2362159801) ^ 3604 = (37 : ZMod 2362159801) ^ (1802 + 1802) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 1802 * (37 : ZMod 2362159801) ^ 1802 := by rw [pow_add]
          _ = 1946419389 := by rw [factor_2_10]; decide
      have factor_2_12 : (37 : ZMod 2362159801) ^ 7208 = 66751981 := by
        calc
          (37 : ZMod 2362159801) ^ 7208 = (37 : ZMod 2362159801) ^ (3604 + 3604) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 3604 * (37 : ZMod 2362159801) ^ 3604 := by rw [pow_add]
          _ = 66751981 := by rw [factor_2_11]; decide
      have factor_2_13 : (37 : ZMod 2362159801) ^ 14417 = 914992927 := by
        calc
          (37 : ZMod 2362159801) ^ 14417 = (37 : ZMod 2362159801) ^ (7208 + 7208 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 7208 * (37 : ZMod 2362159801) ^ 7208) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 914992927 := by rw [factor_2_12]; decide
      have factor_2_14 : (37 : ZMod 2362159801) ^ 28834 = 2129302819 := by
        calc
          (37 : ZMod 2362159801) ^ 28834 = (37 : ZMod 2362159801) ^ (14417 + 14417) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 14417 * (37 : ZMod 2362159801) ^ 14417 := by rw [pow_add]
          _ = 2129302819 := by rw [factor_2_13]; decide
      have factor_2_15 : (37 : ZMod 2362159801) ^ 57669 = 276662917 := by
        calc
          (37 : ZMod 2362159801) ^ 57669 = (37 : ZMod 2362159801) ^ (28834 + 28834 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 28834 * (37 : ZMod 2362159801) ^ 28834) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 276662917 := by rw [factor_2_14]; decide
      have factor_2_16 : (37 : ZMod 2362159801) ^ 115339 = 1444467443 := by
        calc
          (37 : ZMod 2362159801) ^ 115339 = (37 : ZMod 2362159801) ^ (57669 + 57669 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 57669 * (37 : ZMod 2362159801) ^ 57669) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1444467443 := by rw [factor_2_15]; decide
      have factor_2_17 : (37 : ZMod 2362159801) ^ 230679 = 1758601132 := by
        calc
          (37 : ZMod 2362159801) ^ 230679 = (37 : ZMod 2362159801) ^ (115339 + 115339 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 115339 * (37 : ZMod 2362159801) ^ 115339) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1758601132 := by rw [factor_2_16]; decide
      have factor_2_18 : (37 : ZMod 2362159801) ^ 461359 = 342995938 := by
        calc
          (37 : ZMod 2362159801) ^ 461359 = (37 : ZMod 2362159801) ^ (230679 + 230679 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 230679 * (37 : ZMod 2362159801) ^ 230679) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 342995938 := by rw [factor_2_17]; decide
      have factor_2_19 : (37 : ZMod 2362159801) ^ 922718 = 2053997334 := by
        calc
          (37 : ZMod 2362159801) ^ 922718 = (37 : ZMod 2362159801) ^ (461359 + 461359) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 461359 * (37 : ZMod 2362159801) ^ 461359 := by rw [pow_add]
          _ = 2053997334 := by rw [factor_2_18]; decide
      have factor_2_20 : (37 : ZMod 2362159801) ^ 1845437 = 837769757 := by
        calc
          (37 : ZMod 2362159801) ^ 1845437 = (37 : ZMod 2362159801) ^ (922718 + 922718 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 922718 * (37 : ZMod 2362159801) ^ 922718) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 837769757 := by rw [factor_2_19]; decide
      have factor_2_21 : (37 : ZMod 2362159801) ^ 3690874 = 1040714842 := by
        calc
          (37 : ZMod 2362159801) ^ 3690874 = (37 : ZMod 2362159801) ^ (1845437 + 1845437) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 1845437 * (37 : ZMod 2362159801) ^ 1845437 := by rw [pow_add]
          _ = 1040714842 := by rw [factor_2_20]; decide
      have factor_2_22 : (37 : ZMod 2362159801) ^ 7381749 = 1778048935 := by
        calc
          (37 : ZMod 2362159801) ^ 7381749 = (37 : ZMod 2362159801) ^ (3690874 + 3690874 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 3690874 * (37 : ZMod 2362159801) ^ 3690874) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1778048935 := by rw [factor_2_21]; decide
      have factor_2_23 : (37 : ZMod 2362159801) ^ 14763498 = 1085540613 := by
        calc
          (37 : ZMod 2362159801) ^ 14763498 = (37 : ZMod 2362159801) ^ (7381749 + 7381749) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 7381749 * (37 : ZMod 2362159801) ^ 7381749 := by rw [pow_add]
          _ = 1085540613 := by rw [factor_2_22]; decide
      have factor_2_24 : (37 : ZMod 2362159801) ^ 29526997 = 136328536 := by
        calc
          (37 : ZMod 2362159801) ^ 29526997 = (37 : ZMod 2362159801) ^ (14763498 + 14763498 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 14763498 * (37 : ZMod 2362159801) ^ 14763498) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 136328536 := by rw [factor_2_23]; decide
      have factor_2_25 : (37 : ZMod 2362159801) ^ 59053995 = 1947614609 := by
        calc
          (37 : ZMod 2362159801) ^ 59053995 = (37 : ZMod 2362159801) ^ (29526997 + 29526997 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 29526997 * (37 : ZMod 2362159801) ^ 29526997) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1947614609 := by rw [factor_2_24]; decide
      have factor_2_26 : (37 : ZMod 2362159801) ^ 118107990 = 147616614 := by
        calc
          (37 : ZMod 2362159801) ^ 118107990 = (37 : ZMod 2362159801) ^ (59053995 + 59053995) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 59053995 * (37 : ZMod 2362159801) ^ 59053995 := by rw [pow_add]
          _ = 147616614 := by rw [factor_2_25]; decide
      have factor_2_27 : (37 : ZMod 2362159801) ^ 236215980 = 402178106 := by
        calc
          (37 : ZMod 2362159801) ^ 236215980 = (37 : ZMod 2362159801) ^ (118107990 + 118107990) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 118107990 * (37 : ZMod 2362159801) ^ 118107990 := by rw [pow_add]
          _ = 402178106 := by rw [factor_2_26]; decide
      have factor_2_28 : (37 : ZMod 2362159801) ^ 472431960 = 1894931941 := by
        calc
          (37 : ZMod 2362159801) ^ 472431960 = (37 : ZMod 2362159801) ^ (236215980 + 236215980) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 236215980 * (37 : ZMod 2362159801) ^ 236215980 := by rw [pow_add]
          _ = 1894931941 := by rw [factor_2_27]; decide
      change (37 : ZMod 2362159801) ^ 472431960 ≠ 1
      rw [factor_2_28]
      decide
    ·
      have factor_3_0 : (37 : ZMod 2362159801) ^ 1 = 37 := by norm_num
      have factor_3_1 : (37 : ZMod 2362159801) ^ 2 = 1369 := by
        calc
          (37 : ZMod 2362159801) ^ 2 = (37 : ZMod 2362159801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 1 * (37 : ZMod 2362159801) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_3_0]; decide
      have factor_3_2 : (37 : ZMod 2362159801) ^ 5 = 69343957 := by
        calc
          (37 : ZMod 2362159801) ^ 5 = (37 : ZMod 2362159801) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 2 * (37 : ZMod 2362159801) ^ 2) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 69343957 := by rw [factor_3_1]; decide
      have factor_3_3 : (37 : ZMod 2362159801) ^ 10 = 1805996577 := by
        calc
          (37 : ZMod 2362159801) ^ 10 = (37 : ZMod 2362159801) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 5 * (37 : ZMod 2362159801) ^ 5 := by rw [pow_add]
          _ = 1805996577 := by rw [factor_3_2]; decide
      have factor_3_4 : (37 : ZMod 2362159801) ^ 20 = 138589664 := by
        calc
          (37 : ZMod 2362159801) ^ 20 = (37 : ZMod 2362159801) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 10 * (37 : ZMod 2362159801) ^ 10 := by rw [pow_add]
          _ = 138589664 := by rw [factor_3_3]; decide
      have factor_3_5 : (37 : ZMod 2362159801) ^ 40 = 404453338 := by
        calc
          (37 : ZMod 2362159801) ^ 40 = (37 : ZMod 2362159801) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 20 * (37 : ZMod 2362159801) ^ 20 := by rw [pow_add]
          _ = 404453338 := by rw [factor_3_4]; decide
      have factor_3_6 : (37 : ZMod 2362159801) ^ 80 = 235459601 := by
        calc
          (37 : ZMod 2362159801) ^ 80 = (37 : ZMod 2362159801) ^ (40 + 40) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 40 * (37 : ZMod 2362159801) ^ 40 := by rw [pow_add]
          _ = 235459601 := by rw [factor_3_5]; decide
      have factor_3_7 : (37 : ZMod 2362159801) ^ 160 = 915481437 := by
        calc
          (37 : ZMod 2362159801) ^ 160 = (37 : ZMod 2362159801) ^ (80 + 80) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 80 * (37 : ZMod 2362159801) ^ 80 := by rw [pow_add]
          _ = 915481437 := by rw [factor_3_6]; decide
      have factor_3_8 : (37 : ZMod 2362159801) ^ 321 = 472176652 := by
        calc
          (37 : ZMod 2362159801) ^ 321 = (37 : ZMod 2362159801) ^ (160 + 160 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 160 * (37 : ZMod 2362159801) ^ 160) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 472176652 := by rw [factor_3_7]; decide
      have factor_3_9 : (37 : ZMod 2362159801) ^ 643 = 262550883 := by
        calc
          (37 : ZMod 2362159801) ^ 643 = (37 : ZMod 2362159801) ^ (321 + 321 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 321 * (37 : ZMod 2362159801) ^ 321) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 262550883 := by rw [factor_3_8]; decide
      have factor_3_10 : (37 : ZMod 2362159801) ^ 1287 = 1729719933 := by
        calc
          (37 : ZMod 2362159801) ^ 1287 = (37 : ZMod 2362159801) ^ (643 + 643 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 643 * (37 : ZMod 2362159801) ^ 643) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1729719933 := by rw [factor_3_9]; decide
      have factor_3_11 : (37 : ZMod 2362159801) ^ 2574 = 2095762259 := by
        calc
          (37 : ZMod 2362159801) ^ 2574 = (37 : ZMod 2362159801) ^ (1287 + 1287) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 1287 * (37 : ZMod 2362159801) ^ 1287 := by rw [pow_add]
          _ = 2095762259 := by rw [factor_3_10]; decide
      have factor_3_12 : (37 : ZMod 2362159801) ^ 5149 = 2342874765 := by
        calc
          (37 : ZMod 2362159801) ^ 5149 = (37 : ZMod 2362159801) ^ (2574 + 2574 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 2574 * (37 : ZMod 2362159801) ^ 2574) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 2342874765 := by rw [factor_3_11]; decide
      have factor_3_13 : (37 : ZMod 2362159801) ^ 10298 = 1493050 := by
        calc
          (37 : ZMod 2362159801) ^ 10298 = (37 : ZMod 2362159801) ^ (5149 + 5149) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 5149 * (37 : ZMod 2362159801) ^ 5149 := by rw [pow_add]
          _ = 1493050 := by rw [factor_3_12]; decide
      have factor_3_14 : (37 : ZMod 2362159801) ^ 20596 = 1681610157 := by
        calc
          (37 : ZMod 2362159801) ^ 20596 = (37 : ZMod 2362159801) ^ (10298 + 10298) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 10298 * (37 : ZMod 2362159801) ^ 10298 := by rw [pow_add]
          _ = 1681610157 := by rw [factor_3_13]; decide
      have factor_3_15 : (37 : ZMod 2362159801) ^ 41192 = 868304698 := by
        calc
          (37 : ZMod 2362159801) ^ 41192 = (37 : ZMod 2362159801) ^ (20596 + 20596) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 20596 * (37 : ZMod 2362159801) ^ 20596 := by rw [pow_add]
          _ = 868304698 := by rw [factor_3_14]; decide
      have factor_3_16 : (37 : ZMod 2362159801) ^ 82385 = 469813640 := by
        calc
          (37 : ZMod 2362159801) ^ 82385 = (37 : ZMod 2362159801) ^ (41192 + 41192 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 41192 * (37 : ZMod 2362159801) ^ 41192) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 469813640 := by rw [factor_3_15]; decide
      have factor_3_17 : (37 : ZMod 2362159801) ^ 164771 = 285032450 := by
        calc
          (37 : ZMod 2362159801) ^ 164771 = (37 : ZMod 2362159801) ^ (82385 + 82385 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 82385 * (37 : ZMod 2362159801) ^ 82385) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 285032450 := by rw [factor_3_16]; decide
      have factor_3_18 : (37 : ZMod 2362159801) ^ 329542 = 1691915566 := by
        calc
          (37 : ZMod 2362159801) ^ 329542 = (37 : ZMod 2362159801) ^ (164771 + 164771) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 164771 * (37 : ZMod 2362159801) ^ 164771 := by rw [pow_add]
          _ = 1691915566 := by rw [factor_3_17]; decide
      have factor_3_19 : (37 : ZMod 2362159801) ^ 659084 = 1550502904 := by
        calc
          (37 : ZMod 2362159801) ^ 659084 = (37 : ZMod 2362159801) ^ (329542 + 329542) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 329542 * (37 : ZMod 2362159801) ^ 329542 := by rw [pow_add]
          _ = 1550502904 := by rw [factor_3_18]; decide
      have factor_3_20 : (37 : ZMod 2362159801) ^ 1318169 = 1347251392 := by
        calc
          (37 : ZMod 2362159801) ^ 1318169 = (37 : ZMod 2362159801) ^ (659084 + 659084 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 659084 * (37 : ZMod 2362159801) ^ 659084) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1347251392 := by rw [factor_3_19]; decide
      have factor_3_21 : (37 : ZMod 2362159801) ^ 2636339 = 2059298530 := by
        calc
          (37 : ZMod 2362159801) ^ 2636339 = (37 : ZMod 2362159801) ^ (1318169 + 1318169 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 1318169 * (37 : ZMod 2362159801) ^ 1318169) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 2059298530 := by rw [factor_3_20]; decide
      have factor_3_22 : (37 : ZMod 2362159801) ^ 5272678 = 190377874 := by
        calc
          (37 : ZMod 2362159801) ^ 5272678 = (37 : ZMod 2362159801) ^ (2636339 + 2636339) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 2636339 * (37 : ZMod 2362159801) ^ 2636339 := by rw [pow_add]
          _ = 190377874 := by rw [factor_3_21]; decide
      have factor_3_23 : (37 : ZMod 2362159801) ^ 10545356 = 2142590804 := by
        calc
          (37 : ZMod 2362159801) ^ 10545356 = (37 : ZMod 2362159801) ^ (5272678 + 5272678) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 5272678 * (37 : ZMod 2362159801) ^ 5272678 := by rw [pow_add]
          _ = 2142590804 := by rw [factor_3_22]; decide
      have factor_3_24 : (37 : ZMod 2362159801) ^ 21090712 = 1466200091 := by
        calc
          (37 : ZMod 2362159801) ^ 21090712 = (37 : ZMod 2362159801) ^ (10545356 + 10545356) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 10545356 * (37 : ZMod 2362159801) ^ 10545356 := by rw [pow_add]
          _ = 1466200091 := by rw [factor_3_23]; decide
      have factor_3_25 : (37 : ZMod 2362159801) ^ 42181425 = 2094203825 := by
        calc
          (37 : ZMod 2362159801) ^ 42181425 = (37 : ZMod 2362159801) ^ (21090712 + 21090712 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 21090712 * (37 : ZMod 2362159801) ^ 21090712) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 2094203825 := by rw [factor_3_24]; decide
      have factor_3_26 : (37 : ZMod 2362159801) ^ 84362850 = 2065812894 := by
        calc
          (37 : ZMod 2362159801) ^ 84362850 = (37 : ZMod 2362159801) ^ (42181425 + 42181425) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 42181425 * (37 : ZMod 2362159801) ^ 42181425 := by rw [pow_add]
          _ = 2065812894 := by rw [factor_3_25]; decide
      have factor_3_27 : (37 : ZMod 2362159801) ^ 168725700 = 1991782179 := by
        calc
          (37 : ZMod 2362159801) ^ 168725700 = (37 : ZMod 2362159801) ^ (84362850 + 84362850) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 84362850 * (37 : ZMod 2362159801) ^ 84362850 := by rw [pow_add]
          _ = 1991782179 := by rw [factor_3_26]; decide
      have factor_3_28 : (37 : ZMod 2362159801) ^ 337451400 = 1200019890 := by
        calc
          (37 : ZMod 2362159801) ^ 337451400 = (37 : ZMod 2362159801) ^ (168725700 + 168725700) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 168725700 * (37 : ZMod 2362159801) ^ 168725700 := by rw [pow_add]
          _ = 1200019890 := by rw [factor_3_27]; decide
      change (37 : ZMod 2362159801) ^ 337451400 ≠ 1
      rw [factor_3_28]
      decide
    ·
      have factor_4_0 : (37 : ZMod 2362159801) ^ 1 = 37 := by norm_num
      have factor_4_1 : (37 : ZMod 2362159801) ^ 3 = 50653 := by
        calc
          (37 : ZMod 2362159801) ^ 3 = (37 : ZMod 2362159801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 1 * (37 : ZMod 2362159801) ^ 1) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 50653 := by rw [factor_4_0]; decide
      have factor_4_2 : (37 : ZMod 2362159801) ^ 6 = 203566608 := by
        calc
          (37 : ZMod 2362159801) ^ 6 = (37 : ZMod 2362159801) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 3 * (37 : ZMod 2362159801) ^ 3 := by rw [pow_add]
          _ = 203566608 := by rw [factor_4_1]; decide
      have factor_4_3 : (37 : ZMod 2362159801) ^ 12 = 1590162067 := by
        calc
          (37 : ZMod 2362159801) ^ 12 = (37 : ZMod 2362159801) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 6 * (37 : ZMod 2362159801) ^ 6 := by rw [pow_add]
          _ = 1590162067 := by rw [factor_4_2]; decide
      have factor_4_4 : (37 : ZMod 2362159801) ^ 25 = 674924187 := by
        calc
          (37 : ZMod 2362159801) ^ 25 = (37 : ZMod 2362159801) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 12 * (37 : ZMod 2362159801) ^ 12) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 674924187 := by rw [factor_4_3]; decide
      have factor_4_5 : (37 : ZMod 2362159801) ^ 51 = 677612724 := by
        calc
          (37 : ZMod 2362159801) ^ 51 = (37 : ZMod 2362159801) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 25 * (37 : ZMod 2362159801) ^ 25) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 677612724 := by rw [factor_4_4]; decide
      have factor_4_6 : (37 : ZMod 2362159801) ^ 102 = 551240768 := by
        calc
          (37 : ZMod 2362159801) ^ 102 = (37 : ZMod 2362159801) ^ (51 + 51) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 51 * (37 : ZMod 2362159801) ^ 51 := by rw [pow_add]
          _ = 551240768 := by rw [factor_4_5]; decide
      have factor_4_7 : (37 : ZMod 2362159801) ^ 204 = 1800033609 := by
        calc
          (37 : ZMod 2362159801) ^ 204 = (37 : ZMod 2362159801) ^ (102 + 102) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 102 * (37 : ZMod 2362159801) ^ 102 := by rw [pow_add]
          _ = 1800033609 := by rw [factor_4_6]; decide
      have factor_4_8 : (37 : ZMod 2362159801) ^ 409 = 433028854 := by
        calc
          (37 : ZMod 2362159801) ^ 409 = (37 : ZMod 2362159801) ^ (204 + 204 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 204 * (37 : ZMod 2362159801) ^ 204) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 433028854 := by rw [factor_4_7]; decide
      have factor_4_9 : (37 : ZMod 2362159801) ^ 819 = 927395130 := by
        calc
          (37 : ZMod 2362159801) ^ 819 = (37 : ZMod 2362159801) ^ (409 + 409 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 409 * (37 : ZMod 2362159801) ^ 409) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 927395130 := by rw [factor_4_8]; decide
      have factor_4_10 : (37 : ZMod 2362159801) ^ 1638 = 284041578 := by
        calc
          (37 : ZMod 2362159801) ^ 1638 = (37 : ZMod 2362159801) ^ (819 + 819) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 819 * (37 : ZMod 2362159801) ^ 819 := by rw [pow_add]
          _ = 284041578 := by rw [factor_4_9]; decide
      have factor_4_11 : (37 : ZMod 2362159801) ^ 3276 = 424219263 := by
        calc
          (37 : ZMod 2362159801) ^ 3276 = (37 : ZMod 2362159801) ^ (1638 + 1638) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 1638 * (37 : ZMod 2362159801) ^ 1638 := by rw [pow_add]
          _ = 424219263 := by rw [factor_4_10]; decide
      have factor_4_12 : (37 : ZMod 2362159801) ^ 6553 = 1128746317 := by
        calc
          (37 : ZMod 2362159801) ^ 6553 = (37 : ZMod 2362159801) ^ (3276 + 3276 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 3276 * (37 : ZMod 2362159801) ^ 3276) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1128746317 := by rw [factor_4_11]; decide
      have factor_4_13 : (37 : ZMod 2362159801) ^ 13106 = 1914461674 := by
        calc
          (37 : ZMod 2362159801) ^ 13106 = (37 : ZMod 2362159801) ^ (6553 + 6553) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 6553 * (37 : ZMod 2362159801) ^ 6553 := by rw [pow_add]
          _ = 1914461674 := by rw [factor_4_12]; decide
      have factor_4_14 : (37 : ZMod 2362159801) ^ 26213 = 915161777 := by
        calc
          (37 : ZMod 2362159801) ^ 26213 = (37 : ZMod 2362159801) ^ (13106 + 13106 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 13106 * (37 : ZMod 2362159801) ^ 13106) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 915161777 := by rw [factor_4_13]; decide
      have factor_4_15 : (37 : ZMod 2362159801) ^ 52427 = 175515469 := by
        calc
          (37 : ZMod 2362159801) ^ 52427 = (37 : ZMod 2362159801) ^ (26213 + 26213 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 26213 * (37 : ZMod 2362159801) ^ 26213) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 175515469 := by rw [factor_4_14]; decide
      have factor_4_16 : (37 : ZMod 2362159801) ^ 104854 = 364472442 := by
        calc
          (37 : ZMod 2362159801) ^ 104854 = (37 : ZMod 2362159801) ^ (52427 + 52427) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 52427 * (37 : ZMod 2362159801) ^ 52427 := by rw [pow_add]
          _ = 364472442 := by rw [factor_4_15]; decide
      have factor_4_17 : (37 : ZMod 2362159801) ^ 209708 = 1496634027 := by
        calc
          (37 : ZMod 2362159801) ^ 209708 = (37 : ZMod 2362159801) ^ (104854 + 104854) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 104854 * (37 : ZMod 2362159801) ^ 104854 := by rw [pow_add]
          _ = 1496634027 := by rw [factor_4_16]; decide
      have factor_4_18 : (37 : ZMod 2362159801) ^ 419417 = 1927106348 := by
        calc
          (37 : ZMod 2362159801) ^ 419417 = (37 : ZMod 2362159801) ^ (209708 + 209708 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 209708 * (37 : ZMod 2362159801) ^ 209708) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1927106348 := by rw [factor_4_17]; decide
      have factor_4_19 : (37 : ZMod 2362159801) ^ 838835 = 334796648 := by
        calc
          (37 : ZMod 2362159801) ^ 838835 = (37 : ZMod 2362159801) ^ (419417 + 419417 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 419417 * (37 : ZMod 2362159801) ^ 419417) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 334796648 := by rw [factor_4_18]; decide
      have factor_4_20 : (37 : ZMod 2362159801) ^ 1677670 = 2012949079 := by
        calc
          (37 : ZMod 2362159801) ^ 1677670 = (37 : ZMod 2362159801) ^ (838835 + 838835) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 838835 * (37 : ZMod 2362159801) ^ 838835 := by rw [pow_add]
          _ = 2012949079 := by rw [factor_4_19]; decide
      have factor_4_21 : (37 : ZMod 2362159801) ^ 3355340 = 1105033395 := by
        calc
          (37 : ZMod 2362159801) ^ 3355340 = (37 : ZMod 2362159801) ^ (1677670 + 1677670) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 1677670 * (37 : ZMod 2362159801) ^ 1677670 := by rw [pow_add]
          _ = 1105033395 := by rw [factor_4_20]; decide
      have factor_4_22 : (37 : ZMod 2362159801) ^ 6710681 = 425270978 := by
        calc
          (37 : ZMod 2362159801) ^ 6710681 = (37 : ZMod 2362159801) ^ (3355340 + 3355340 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 3355340 * (37 : ZMod 2362159801) ^ 3355340) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 425270978 := by rw [factor_4_21]; decide
      have factor_4_23 : (37 : ZMod 2362159801) ^ 13421362 = 918908307 := by
        calc
          (37 : ZMod 2362159801) ^ 13421362 = (37 : ZMod 2362159801) ^ (6710681 + 6710681) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 6710681 * (37 : ZMod 2362159801) ^ 6710681 := by rw [pow_add]
          _ = 918908307 := by rw [factor_4_22]; decide
      have factor_4_24 : (37 : ZMod 2362159801) ^ 26842725 = 1336530256 := by
        calc
          (37 : ZMod 2362159801) ^ 26842725 = (37 : ZMod 2362159801) ^ (13421362 + 13421362 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 13421362 * (37 : ZMod 2362159801) ^ 13421362) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1336530256 := by rw [factor_4_23]; decide
      have factor_4_25 : (37 : ZMod 2362159801) ^ 53685450 = 345899465 := by
        calc
          (37 : ZMod 2362159801) ^ 53685450 = (37 : ZMod 2362159801) ^ (26842725 + 26842725) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 26842725 * (37 : ZMod 2362159801) ^ 26842725 := by rw [pow_add]
          _ = 345899465 := by rw [factor_4_24]; decide
      have factor_4_26 : (37 : ZMod 2362159801) ^ 107370900 = 1142652736 := by
        calc
          (37 : ZMod 2362159801) ^ 107370900 = (37 : ZMod 2362159801) ^ (53685450 + 53685450) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 53685450 * (37 : ZMod 2362159801) ^ 53685450 := by rw [pow_add]
          _ = 1142652736 := by rw [factor_4_25]; decide
      have factor_4_27 : (37 : ZMod 2362159801) ^ 214741800 = 1235369985 := by
        calc
          (37 : ZMod 2362159801) ^ 214741800 = (37 : ZMod 2362159801) ^ (107370900 + 107370900) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 107370900 * (37 : ZMod 2362159801) ^ 107370900 := by rw [pow_add]
          _ = 1235369985 := by rw [factor_4_26]; decide
      change (37 : ZMod 2362159801) ^ 214741800 ≠ 1
      rw [factor_4_27]
      decide
    ·
      have factor_5_0 : (37 : ZMod 2362159801) ^ 1 = 37 := by norm_num
      have factor_5_1 : (37 : ZMod 2362159801) ^ 2 = 1369 := by
        calc
          (37 : ZMod 2362159801) ^ 2 = (37 : ZMod 2362159801) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 1 * (37 : ZMod 2362159801) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_5_0]; decide
      have factor_5_2 : (37 : ZMod 2362159801) ^ 5 = 69343957 := by
        calc
          (37 : ZMod 2362159801) ^ 5 = (37 : ZMod 2362159801) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 2 * (37 : ZMod 2362159801) ^ 2) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 69343957 := by rw [factor_5_1]; decide
      have factor_5_3 : (37 : ZMod 2362159801) ^ 10 = 1805996577 := by
        calc
          (37 : ZMod 2362159801) ^ 10 = (37 : ZMod 2362159801) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 5 * (37 : ZMod 2362159801) ^ 5 := by rw [pow_add]
          _ = 1805996577 := by rw [factor_5_2]; decide
      have factor_5_4 : (37 : ZMod 2362159801) ^ 21 = 403497966 := by
        calc
          (37 : ZMod 2362159801) ^ 21 = (37 : ZMod 2362159801) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 10 * (37 : ZMod 2362159801) ^ 10) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 403497966 := by rw [factor_5_3]; decide
      have factor_5_5 : (37 : ZMod 2362159801) ^ 43 = 2125135442 := by
        calc
          (37 : ZMod 2362159801) ^ 43 = (37 : ZMod 2362159801) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 21 * (37 : ZMod 2362159801) ^ 21) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 2125135442 := by rw [factor_5_4]; decide
      have factor_5_6 : (37 : ZMod 2362159801) ^ 86 = 1024287331 := by
        calc
          (37 : ZMod 2362159801) ^ 86 = (37 : ZMod 2362159801) ^ (43 + 43) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 43 * (37 : ZMod 2362159801) ^ 43 := by rw [pow_add]
          _ = 1024287331 := by rw [factor_5_5]; decide
      have factor_5_7 : (37 : ZMod 2362159801) ^ 173 = 1262782372 := by
        calc
          (37 : ZMod 2362159801) ^ 173 = (37 : ZMod 2362159801) ^ (86 + 86 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 86 * (37 : ZMod 2362159801) ^ 86) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1262782372 := by rw [factor_5_6]; decide
      have factor_5_8 : (37 : ZMod 2362159801) ^ 346 = 2098707835 := by
        calc
          (37 : ZMod 2362159801) ^ 346 = (37 : ZMod 2362159801) ^ (173 + 173) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 173 * (37 : ZMod 2362159801) ^ 173 := by rw [pow_add]
          _ = 2098707835 := by rw [factor_5_7]; decide
      have factor_5_9 : (37 : ZMod 2362159801) ^ 693 = 2066823286 := by
        calc
          (37 : ZMod 2362159801) ^ 693 = (37 : ZMod 2362159801) ^ (346 + 346 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 346 * (37 : ZMod 2362159801) ^ 346) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 2066823286 := by rw [factor_5_8]; decide
      have factor_5_10 : (37 : ZMod 2362159801) ^ 1386 = 1733216442 := by
        calc
          (37 : ZMod 2362159801) ^ 1386 = (37 : ZMod 2362159801) ^ (693 + 693) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 693 * (37 : ZMod 2362159801) ^ 693 := by rw [pow_add]
          _ = 1733216442 := by rw [factor_5_9]; decide
      have factor_5_11 : (37 : ZMod 2362159801) ^ 2772 = 97750836 := by
        calc
          (37 : ZMod 2362159801) ^ 2772 = (37 : ZMod 2362159801) ^ (1386 + 1386) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 1386 * (37 : ZMod 2362159801) ^ 1386 := by rw [pow_add]
          _ = 97750836 := by rw [factor_5_10]; decide
      have factor_5_12 : (37 : ZMod 2362159801) ^ 5545 = 720496617 := by
        calc
          (37 : ZMod 2362159801) ^ 5545 = (37 : ZMod 2362159801) ^ (2772 + 2772 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 2772 * (37 : ZMod 2362159801) ^ 2772) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 720496617 := by rw [factor_5_11]; decide
      have factor_5_13 : (37 : ZMod 2362159801) ^ 11090 = 1155925868 := by
        calc
          (37 : ZMod 2362159801) ^ 11090 = (37 : ZMod 2362159801) ^ (5545 + 5545) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 5545 * (37 : ZMod 2362159801) ^ 5545 := by rw [pow_add]
          _ = 1155925868 := by rw [factor_5_12]; decide
      have factor_5_14 : (37 : ZMod 2362159801) ^ 22180 = 1360494848 := by
        calc
          (37 : ZMod 2362159801) ^ 22180 = (37 : ZMod 2362159801) ^ (11090 + 11090) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 11090 * (37 : ZMod 2362159801) ^ 11090 := by rw [pow_add]
          _ = 1360494848 := by rw [factor_5_13]; decide
      have factor_5_15 : (37 : ZMod 2362159801) ^ 44361 = 2061870076 := by
        calc
          (37 : ZMod 2362159801) ^ 44361 = (37 : ZMod 2362159801) ^ (22180 + 22180 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 22180 * (37 : ZMod 2362159801) ^ 22180) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 2061870076 := by rw [factor_5_14]; decide
      have factor_5_16 : (37 : ZMod 2362159801) ^ 88722 = 1579111474 := by
        calc
          (37 : ZMod 2362159801) ^ 88722 = (37 : ZMod 2362159801) ^ (44361 + 44361) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 44361 * (37 : ZMod 2362159801) ^ 44361 := by rw [pow_add]
          _ = 1579111474 := by rw [factor_5_15]; decide
      have factor_5_17 : (37 : ZMod 2362159801) ^ 177445 = 164407112 := by
        calc
          (37 : ZMod 2362159801) ^ 177445 = (37 : ZMod 2362159801) ^ (88722 + 88722 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 88722 * (37 : ZMod 2362159801) ^ 88722) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 164407112 := by rw [factor_5_16]; decide
      have factor_5_18 : (37 : ZMod 2362159801) ^ 354891 = 2019462500 := by
        calc
          (37 : ZMod 2362159801) ^ 354891 = (37 : ZMod 2362159801) ^ (177445 + 177445 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 177445 * (37 : ZMod 2362159801) ^ 177445) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 2019462500 := by rw [factor_5_17]; decide
      have factor_5_19 : (37 : ZMod 2362159801) ^ 709783 = 1402532230 := by
        calc
          (37 : ZMod 2362159801) ^ 709783 = (37 : ZMod 2362159801) ^ (354891 + 354891 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 354891 * (37 : ZMod 2362159801) ^ 354891) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1402532230 := by rw [factor_5_18]; decide
      have factor_5_20 : (37 : ZMod 2362159801) ^ 1419567 = 2351478909 := by
        calc
          (37 : ZMod 2362159801) ^ 1419567 = (37 : ZMod 2362159801) ^ (709783 + 709783 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 709783 * (37 : ZMod 2362159801) ^ 709783) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 2351478909 := by rw [factor_5_19]; decide
      have factor_5_21 : (37 : ZMod 2362159801) ^ 2839134 = 946326369 := by
        calc
          (37 : ZMod 2362159801) ^ 2839134 = (37 : ZMod 2362159801) ^ (1419567 + 1419567) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 1419567 * (37 : ZMod 2362159801) ^ 1419567 := by rw [pow_add]
          _ = 946326369 := by rw [factor_5_20]; decide
      have factor_5_22 : (37 : ZMod 2362159801) ^ 5678268 = 1095774129 := by
        calc
          (37 : ZMod 2362159801) ^ 5678268 = (37 : ZMod 2362159801) ^ (2839134 + 2839134) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 2839134 * (37 : ZMod 2362159801) ^ 2839134 := by rw [pow_add]
          _ = 1095774129 := by rw [factor_5_21]; decide
      have factor_5_23 : (37 : ZMod 2362159801) ^ 11356537 = 1015255090 := by
        calc
          (37 : ZMod 2362159801) ^ 11356537 = (37 : ZMod 2362159801) ^ (5678268 + 5678268 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 5678268 * (37 : ZMod 2362159801) ^ 5678268) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1015255090 := by rw [factor_5_22]; decide
      have factor_5_24 : (37 : ZMod 2362159801) ^ 22713075 = 2092949070 := by
        calc
          (37 : ZMod 2362159801) ^ 22713075 = (37 : ZMod 2362159801) ^ (11356537 + 11356537 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 11356537 * (37 : ZMod 2362159801) ^ 11356537) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 2092949070 := by rw [factor_5_23]; decide
      have factor_5_25 : (37 : ZMod 2362159801) ^ 45426150 = 723956941 := by
        calc
          (37 : ZMod 2362159801) ^ 45426150 = (37 : ZMod 2362159801) ^ (22713075 + 22713075) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 22713075 * (37 : ZMod 2362159801) ^ 22713075 := by rw [pow_add]
          _ = 723956941 := by rw [factor_5_24]; decide
      have factor_5_26 : (37 : ZMod 2362159801) ^ 90852300 = 298158282 := by
        calc
          (37 : ZMod 2362159801) ^ 90852300 = (37 : ZMod 2362159801) ^ (45426150 + 45426150) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 45426150 * (37 : ZMod 2362159801) ^ 45426150 := by rw [pow_add]
          _ = 298158282 := by rw [factor_5_25]; decide
      have factor_5_27 : (37 : ZMod 2362159801) ^ 181704600 = 607628169 := by
        calc
          (37 : ZMod 2362159801) ^ 181704600 = (37 : ZMod 2362159801) ^ (90852300 + 90852300) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 90852300 * (37 : ZMod 2362159801) ^ 90852300 := by rw [pow_add]
          _ = 607628169 := by rw [factor_5_26]; decide
      change (37 : ZMod 2362159801) ^ 181704600 ≠ 1
      rw [factor_5_27]
      decide
    ·
      have factor_6_0 : (37 : ZMod 2362159801) ^ 1 = 37 := by norm_num
      have factor_6_1 : (37 : ZMod 2362159801) ^ 3 = 50653 := by
        calc
          (37 : ZMod 2362159801) ^ 3 = (37 : ZMod 2362159801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 1 * (37 : ZMod 2362159801) ^ 1) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 50653 := by rw [factor_6_0]; decide
      have factor_6_2 : (37 : ZMod 2362159801) ^ 7 = 445485093 := by
        calc
          (37 : ZMod 2362159801) ^ 7 = (37 : ZMod 2362159801) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 3 * (37 : ZMod 2362159801) ^ 3) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 445485093 := by rw [factor_6_1]; decide
      have factor_6_3 : (37 : ZMod 2362159801) ^ 14 = 1382693002 := by
        calc
          (37 : ZMod 2362159801) ^ 14 = (37 : ZMod 2362159801) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 7 * (37 : ZMod 2362159801) ^ 7 := by rw [pow_add]
          _ = 1382693002 := by rw [factor_6_2]; decide
      have factor_6_4 : (37 : ZMod 2362159801) ^ 29 = 1275234816 := by
        calc
          (37 : ZMod 2362159801) ^ 29 = (37 : ZMod 2362159801) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 14 * (37 : ZMod 2362159801) ^ 14) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1275234816 := by rw [factor_6_3]; decide
      have factor_6_5 : (37 : ZMod 2362159801) ^ 59 = 1131130829 := by
        calc
          (37 : ZMod 2362159801) ^ 59 = (37 : ZMod 2362159801) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 29 * (37 : ZMod 2362159801) ^ 29) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1131130829 := by rw [factor_6_4]; decide
      have factor_6_6 : (37 : ZMod 2362159801) ^ 118 = 695675564 := by
        calc
          (37 : ZMod 2362159801) ^ 118 = (37 : ZMod 2362159801) ^ (59 + 59) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 59 * (37 : ZMod 2362159801) ^ 59 := by rw [pow_add]
          _ = 695675564 := by rw [factor_6_5]; decide
      have factor_6_7 : (37 : ZMod 2362159801) ^ 237 = 530348053 := by
        calc
          (37 : ZMod 2362159801) ^ 237 = (37 : ZMod 2362159801) ^ (118 + 118 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 118 * (37 : ZMod 2362159801) ^ 118) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 530348053 := by rw [factor_6_6]; decide
      have factor_6_8 : (37 : ZMod 2362159801) ^ 474 = 179264377 := by
        calc
          (37 : ZMod 2362159801) ^ 474 = (37 : ZMod 2362159801) ^ (237 + 237) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 237 * (37 : ZMod 2362159801) ^ 237 := by rw [pow_add]
          _ = 179264377 := by rw [factor_6_7]; decide
      have factor_6_9 : (37 : ZMod 2362159801) ^ 948 = 2031989351 := by
        calc
          (37 : ZMod 2362159801) ^ 948 = (37 : ZMod 2362159801) ^ (474 + 474) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 474 * (37 : ZMod 2362159801) ^ 474 := by rw [pow_add]
          _ = 2031989351 := by rw [factor_6_8]; decide
      have factor_6_10 : (37 : ZMod 2362159801) ^ 1897 = 474401694 := by
        calc
          (37 : ZMod 2362159801) ^ 1897 = (37 : ZMod 2362159801) ^ (948 + 948 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 948 * (37 : ZMod 2362159801) ^ 948) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 474401694 := by rw [factor_6_9]; decide
      have factor_6_11 : (37 : ZMod 2362159801) ^ 3794 = 145499308 := by
        calc
          (37 : ZMod 2362159801) ^ 3794 = (37 : ZMod 2362159801) ^ (1897 + 1897) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 1897 * (37 : ZMod 2362159801) ^ 1897 := by rw [pow_add]
          _ = 145499308 := by rw [factor_6_10]; decide
      have factor_6_12 : (37 : ZMod 2362159801) ^ 7588 = 1632828107 := by
        calc
          (37 : ZMod 2362159801) ^ 7588 = (37 : ZMod 2362159801) ^ (3794 + 3794) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 3794 * (37 : ZMod 2362159801) ^ 3794 := by rw [pow_add]
          _ = 1632828107 := by rw [factor_6_11]; decide
      have factor_6_13 : (37 : ZMod 2362159801) ^ 15176 = 551353289 := by
        calc
          (37 : ZMod 2362159801) ^ 15176 = (37 : ZMod 2362159801) ^ (7588 + 7588) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 7588 * (37 : ZMod 2362159801) ^ 7588 := by rw [pow_add]
          _ = 551353289 := by rw [factor_6_12]; decide
      have factor_6_14 : (37 : ZMod 2362159801) ^ 30352 = 1428853184 := by
        calc
          (37 : ZMod 2362159801) ^ 30352 = (37 : ZMod 2362159801) ^ (15176 + 15176) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 15176 * (37 : ZMod 2362159801) ^ 15176 := by rw [pow_add]
          _ = 1428853184 := by rw [factor_6_13]; decide
      have factor_6_15 : (37 : ZMod 2362159801) ^ 60705 = 631541841 := by
        calc
          (37 : ZMod 2362159801) ^ 60705 = (37 : ZMod 2362159801) ^ (30352 + 30352 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 30352 * (37 : ZMod 2362159801) ^ 30352) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 631541841 := by rw [factor_6_14]; decide
      have factor_6_16 : (37 : ZMod 2362159801) ^ 121410 = 1042748646 := by
        calc
          (37 : ZMod 2362159801) ^ 121410 = (37 : ZMod 2362159801) ^ (60705 + 60705) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 60705 * (37 : ZMod 2362159801) ^ 60705 := by rw [pow_add]
          _ = 1042748646 := by rw [factor_6_15]; decide
      have factor_6_17 : (37 : ZMod 2362159801) ^ 242820 = 86835756 := by
        calc
          (37 : ZMod 2362159801) ^ 242820 = (37 : ZMod 2362159801) ^ (121410 + 121410) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 121410 * (37 : ZMod 2362159801) ^ 121410 := by rw [pow_add]
          _ = 86835756 := by rw [factor_6_16]; decide
      have factor_6_18 : (37 : ZMod 2362159801) ^ 485641 = 1970796828 := by
        calc
          (37 : ZMod 2362159801) ^ 485641 = (37 : ZMod 2362159801) ^ (242820 + 242820 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 242820 * (37 : ZMod 2362159801) ^ 242820) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1970796828 := by rw [factor_6_17]; decide
      have factor_6_19 : (37 : ZMod 2362159801) ^ 971282 = 541092256 := by
        calc
          (37 : ZMod 2362159801) ^ 971282 = (37 : ZMod 2362159801) ^ (485641 + 485641) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 485641 * (37 : ZMod 2362159801) ^ 485641 := by rw [pow_add]
          _ = 541092256 := by rw [factor_6_18]; decide
      have factor_6_20 : (37 : ZMod 2362159801) ^ 1942565 = 2203049892 := by
        calc
          (37 : ZMod 2362159801) ^ 1942565 = (37 : ZMod 2362159801) ^ (971282 + 971282 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 971282 * (37 : ZMod 2362159801) ^ 971282) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 2203049892 := by rw [factor_6_19]; decide
      have factor_6_21 : (37 : ZMod 2362159801) ^ 3885131 = 1359408487 := by
        calc
          (37 : ZMod 2362159801) ^ 3885131 = (37 : ZMod 2362159801) ^ (1942565 + 1942565 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 1942565 * (37 : ZMod 2362159801) ^ 1942565) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1359408487 := by rw [factor_6_20]; decide
      have factor_6_22 : (37 : ZMod 2362159801) ^ 7770262 = 2349388118 := by
        calc
          (37 : ZMod 2362159801) ^ 7770262 = (37 : ZMod 2362159801) ^ (3885131 + 3885131) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 3885131 * (37 : ZMod 2362159801) ^ 3885131 := by rw [pow_add]
          _ = 2349388118 := by rw [factor_6_21]; decide
      have factor_6_23 : (37 : ZMod 2362159801) ^ 15540525 = 222664506 := by
        calc
          (37 : ZMod 2362159801) ^ 15540525 = (37 : ZMod 2362159801) ^ (7770262 + 7770262 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 7770262 * (37 : ZMod 2362159801) ^ 7770262) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 222664506 := by rw [factor_6_22]; decide
      have factor_6_24 : (37 : ZMod 2362159801) ^ 31081050 = 1509684190 := by
        calc
          (37 : ZMod 2362159801) ^ 31081050 = (37 : ZMod 2362159801) ^ (15540525 + 15540525) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 15540525 * (37 : ZMod 2362159801) ^ 15540525 := by rw [pow_add]
          _ = 1509684190 := by rw [factor_6_23]; decide
      have factor_6_25 : (37 : ZMod 2362159801) ^ 62162100 = 562973528 := by
        calc
          (37 : ZMod 2362159801) ^ 62162100 = (37 : ZMod 2362159801) ^ (31081050 + 31081050) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 31081050 * (37 : ZMod 2362159801) ^ 31081050 := by rw [pow_add]
          _ = 562973528 := by rw [factor_6_24]; decide
      have factor_6_26 : (37 : ZMod 2362159801) ^ 124324200 = 1861128508 := by
        calc
          (37 : ZMod 2362159801) ^ 124324200 = (37 : ZMod 2362159801) ^ (62162100 + 62162100) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 62162100 * (37 : ZMod 2362159801) ^ 62162100 := by rw [pow_add]
          _ = 1861128508 := by rw [factor_6_25]; decide
      change (37 : ZMod 2362159801) ^ 124324200 ≠ 1
      rw [factor_6_26]
      decide
    ·
      have factor_7_0 : (37 : ZMod 2362159801) ^ 1 = 37 := by norm_num
      have factor_7_1 : (37 : ZMod 2362159801) ^ 3 = 50653 := by
        calc
          (37 : ZMod 2362159801) ^ 3 = (37 : ZMod 2362159801) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 1 * (37 : ZMod 2362159801) ^ 1) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 50653 := by rw [factor_7_0]; decide
      have factor_7_2 : (37 : ZMod 2362159801) ^ 6 = 203566608 := by
        calc
          (37 : ZMod 2362159801) ^ 6 = (37 : ZMod 2362159801) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 3 * (37 : ZMod 2362159801) ^ 3 := by rw [pow_add]
          _ = 203566608 := by rw [factor_7_1]; decide
      have factor_7_3 : (37 : ZMod 2362159801) ^ 12 = 1590162067 := by
        calc
          (37 : ZMod 2362159801) ^ 12 = (37 : ZMod 2362159801) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 6 * (37 : ZMod 2362159801) ^ 6 := by rw [pow_add]
          _ = 1590162067 := by rw [factor_7_2]; decide
      have factor_7_4 : (37 : ZMod 2362159801) ^ 24 = 975873546 := by
        calc
          (37 : ZMod 2362159801) ^ 24 = (37 : ZMod 2362159801) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 12 * (37 : ZMod 2362159801) ^ 12 := by rw [pow_add]
          _ = 975873546 := by rw [factor_7_3]; decide
      have factor_7_5 : (37 : ZMod 2362159801) ^ 48 = 931204164 := by
        calc
          (37 : ZMod 2362159801) ^ 48 = (37 : ZMod 2362159801) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 24 * (37 : ZMod 2362159801) ^ 24 := by rw [pow_add]
          _ = 931204164 := by rw [factor_7_4]; decide
      have factor_7_6 : (37 : ZMod 2362159801) ^ 97 = 2131417660 := by
        calc
          (37 : ZMod 2362159801) ^ 97 = (37 : ZMod 2362159801) ^ (48 + 48 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 48 * (37 : ZMod 2362159801) ^ 48) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 2131417660 := by rw [factor_7_5]; decide
      have factor_7_7 : (37 : ZMod 2362159801) ^ 195 = 172010552 := by
        calc
          (37 : ZMod 2362159801) ^ 195 = (37 : ZMod 2362159801) ^ (97 + 97 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 97 * (37 : ZMod 2362159801) ^ 97) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 172010552 := by rw [factor_7_6]; decide
      have factor_7_8 : (37 : ZMod 2362159801) ^ 391 = 2158409124 := by
        calc
          (37 : ZMod 2362159801) ^ 391 = (37 : ZMod 2362159801) ^ (195 + 195 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 195 * (37 : ZMod 2362159801) ^ 195) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 2158409124 := by rw [factor_7_7]; decide
      have factor_7_9 : (37 : ZMod 2362159801) ^ 783 = 1409490087 := by
        calc
          (37 : ZMod 2362159801) ^ 783 = (37 : ZMod 2362159801) ^ (391 + 391 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 391 * (37 : ZMod 2362159801) ^ 391) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1409490087 := by rw [factor_7_8]; decide
      have factor_7_10 : (37 : ZMod 2362159801) ^ 1567 = 24895348 := by
        calc
          (37 : ZMod 2362159801) ^ 1567 = (37 : ZMod 2362159801) ^ (783 + 783 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 783 * (37 : ZMod 2362159801) ^ 783) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 24895348 := by rw [factor_7_9]; decide
      have factor_7_11 : (37 : ZMod 2362159801) ^ 3134 = 1949934127 := by
        calc
          (37 : ZMod 2362159801) ^ 3134 = (37 : ZMod 2362159801) ^ (1567 + 1567) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 1567 * (37 : ZMod 2362159801) ^ 1567 := by rw [pow_add]
          _ = 1949934127 := by rw [factor_7_10]; decide
      have factor_7_12 : (37 : ZMod 2362159801) ^ 6268 = 227856672 := by
        calc
          (37 : ZMod 2362159801) ^ 6268 = (37 : ZMod 2362159801) ^ (3134 + 3134) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 3134 * (37 : ZMod 2362159801) ^ 3134 := by rw [pow_add]
          _ = 227856672 := by rw [factor_7_11]; decide
      have factor_7_13 : (37 : ZMod 2362159801) ^ 12536 = 1541919866 := by
        calc
          (37 : ZMod 2362159801) ^ 12536 = (37 : ZMod 2362159801) ^ (6268 + 6268) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 6268 * (37 : ZMod 2362159801) ^ 6268 := by rw [pow_add]
          _ = 1541919866 := by rw [factor_7_12]; decide
      have factor_7_14 : (37 : ZMod 2362159801) ^ 25073 = 2320659658 := by
        calc
          (37 : ZMod 2362159801) ^ 25073 = (37 : ZMod 2362159801) ^ (12536 + 12536 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 12536 * (37 : ZMod 2362159801) ^ 12536) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 2320659658 := by rw [factor_7_13]; decide
      have factor_7_15 : (37 : ZMod 2362159801) ^ 50147 = 1834314539 := by
        calc
          (37 : ZMod 2362159801) ^ 50147 = (37 : ZMod 2362159801) ^ (25073 + 25073 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 25073 * (37 : ZMod 2362159801) ^ 25073) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1834314539 := by rw [factor_7_14]; decide
      have factor_7_16 : (37 : ZMod 2362159801) ^ 100295 = 2260319178 := by
        calc
          (37 : ZMod 2362159801) ^ 100295 = (37 : ZMod 2362159801) ^ (50147 + 50147 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 50147 * (37 : ZMod 2362159801) ^ 50147) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 2260319178 := by rw [factor_7_15]; decide
      have factor_7_17 : (37 : ZMod 2362159801) ^ 200591 = 2031334427 := by
        calc
          (37 : ZMod 2362159801) ^ 200591 = (37 : ZMod 2362159801) ^ (100295 + 100295 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 100295 * (37 : ZMod 2362159801) ^ 100295) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 2031334427 := by rw [factor_7_16]; decide
      have factor_7_18 : (37 : ZMod 2362159801) ^ 401182 = 59822897 := by
        calc
          (37 : ZMod 2362159801) ^ 401182 = (37 : ZMod 2362159801) ^ (200591 + 200591) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 200591 * (37 : ZMod 2362159801) ^ 200591 := by rw [pow_add]
          _ = 59822897 := by rw [factor_7_17]; decide
      have factor_7_19 : (37 : ZMod 2362159801) ^ 802364 = 609766564 := by
        calc
          (37 : ZMod 2362159801) ^ 802364 = (37 : ZMod 2362159801) ^ (401182 + 401182) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 401182 * (37 : ZMod 2362159801) ^ 401182 := by rw [pow_add]
          _ = 609766564 := by rw [factor_7_18]; decide
      have factor_7_20 : (37 : ZMod 2362159801) ^ 1604728 = 2235998709 := by
        calc
          (37 : ZMod 2362159801) ^ 1604728 = (37 : ZMod 2362159801) ^ (802364 + 802364) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 802364 * (37 : ZMod 2362159801) ^ 802364 := by rw [pow_add]
          _ = 2235998709 := by rw [factor_7_19]; decide
      have factor_7_21 : (37 : ZMod 2362159801) ^ 3209456 = 1001287100 := by
        calc
          (37 : ZMod 2362159801) ^ 3209456 = (37 : ZMod 2362159801) ^ (1604728 + 1604728) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 1604728 * (37 : ZMod 2362159801) ^ 1604728 := by rw [pow_add]
          _ = 1001287100 := by rw [factor_7_20]; decide
      have factor_7_22 : (37 : ZMod 2362159801) ^ 6418912 = 2292348150 := by
        calc
          (37 : ZMod 2362159801) ^ 6418912 = (37 : ZMod 2362159801) ^ (3209456 + 3209456) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 3209456 * (37 : ZMod 2362159801) ^ 3209456 := by rw [pow_add]
          _ = 2292348150 := by rw [factor_7_21]; decide
      have factor_7_23 : (37 : ZMod 2362159801) ^ 12837825 = 1276758521 := by
        calc
          (37 : ZMod 2362159801) ^ 12837825 = (37 : ZMod 2362159801) ^ (6418912 + 6418912 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = ((37 : ZMod 2362159801) ^ 6418912 * (37 : ZMod 2362159801) ^ 6418912) * (37 : ZMod 2362159801) := by rw [pow_succ, pow_add]
          _ = 1276758521 := by rw [factor_7_22]; decide
      have factor_7_24 : (37 : ZMod 2362159801) ^ 25675650 = 1061854635 := by
        calc
          (37 : ZMod 2362159801) ^ 25675650 = (37 : ZMod 2362159801) ^ (12837825 + 12837825) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 12837825 * (37 : ZMod 2362159801) ^ 12837825 := by rw [pow_add]
          _ = 1061854635 := by rw [factor_7_23]; decide
      have factor_7_25 : (37 : ZMod 2362159801) ^ 51351300 = 605718885 := by
        calc
          (37 : ZMod 2362159801) ^ 51351300 = (37 : ZMod 2362159801) ^ (25675650 + 25675650) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 25675650 * (37 : ZMod 2362159801) ^ 25675650 := by rw [pow_add]
          _ = 605718885 := by rw [factor_7_24]; decide
      have factor_7_26 : (37 : ZMod 2362159801) ^ 102702600 = 1931999633 := by
        calc
          (37 : ZMod 2362159801) ^ 102702600 = (37 : ZMod 2362159801) ^ (51351300 + 51351300) :=
            congrArg (fun n : ℕ => (37 : ZMod 2362159801) ^ n) (by norm_num)
          _ = (37 : ZMod 2362159801) ^ 51351300 * (37 : ZMod 2362159801) ^ 51351300 := by rw [pow_add]
          _ = 1931999633 := by rw [factor_7_25]; decide
      change (37 : ZMod 2362159801) ^ 102702600 ≠ 1
      rw [factor_7_26]
      decide

#print axioms prime_lucas_2362159801

end TotientTailPeriodKiller
end Erdos249257
