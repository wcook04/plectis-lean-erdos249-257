import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=27 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_16062686641 : Nat.Prime 16062686641 := by
  apply lucas_primality 16062686641 (79 : ZMod 16062686641)
  ·
      have fermat_0 : (79 : ZMod 16062686641) ^ 1 = 79 := by norm_num
      have fermat_1 : (79 : ZMod 16062686641) ^ 3 = 493039 := by
        calc
          (79 : ZMod 16062686641) ^ 3 = (79 : ZMod 16062686641) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 1 * (79 : ZMod 16062686641) ^ 1) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 493039 := by rw [fermat_0]; decide
      have fermat_2 : (79 : ZMod 16062686641) ^ 7 = 8998450164 := by
        calc
          (79 : ZMod 16062686641) ^ 7 = (79 : ZMod 16062686641) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 3 * (79 : ZMod 16062686641) ^ 3) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 8998450164 := by rw [fermat_1]; decide
      have fermat_3 : (79 : ZMod 16062686641) ^ 14 = 14713143187 := by
        calc
          (79 : ZMod 16062686641) ^ 14 = (79 : ZMod 16062686641) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 7 * (79 : ZMod 16062686641) ^ 7 := by rw [pow_add]
          _ = 14713143187 := by rw [fermat_2]; decide
      have fermat_4 : (79 : ZMod 16062686641) ^ 29 = 12912813422 := by
        calc
          (79 : ZMod 16062686641) ^ 29 = (79 : ZMod 16062686641) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 14 * (79 : ZMod 16062686641) ^ 14) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 12912813422 := by rw [fermat_3]; decide
      have fermat_5 : (79 : ZMod 16062686641) ^ 59 = 2947626042 := by
        calc
          (79 : ZMod 16062686641) ^ 59 = (79 : ZMod 16062686641) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 29 * (79 : ZMod 16062686641) ^ 29) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 2947626042 := by rw [fermat_4]; decide
      have fermat_6 : (79 : ZMod 16062686641) ^ 119 = 9972289066 := by
        calc
          (79 : ZMod 16062686641) ^ 119 = (79 : ZMod 16062686641) ^ (59 + 59 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 59 * (79 : ZMod 16062686641) ^ 59) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 9972289066 := by rw [fermat_5]; decide
      have fermat_7 : (79 : ZMod 16062686641) ^ 239 = 14030169541 := by
        calc
          (79 : ZMod 16062686641) ^ 239 = (79 : ZMod 16062686641) ^ (119 + 119 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 119 * (79 : ZMod 16062686641) ^ 119) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 14030169541 := by rw [fermat_6]; decide
      have fermat_8 : (79 : ZMod 16062686641) ^ 478 = 7519161480 := by
        calc
          (79 : ZMod 16062686641) ^ 478 = (79 : ZMod 16062686641) ^ (239 + 239) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 239 * (79 : ZMod 16062686641) ^ 239 := by rw [pow_add]
          _ = 7519161480 := by rw [fermat_7]; decide
      have fermat_9 : (79 : ZMod 16062686641) ^ 957 = 8225209508 := by
        calc
          (79 : ZMod 16062686641) ^ 957 = (79 : ZMod 16062686641) ^ (478 + 478 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 478 * (79 : ZMod 16062686641) ^ 478) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 8225209508 := by rw [fermat_8]; decide
      have fermat_10 : (79 : ZMod 16062686641) ^ 1914 = 10055409338 := by
        calc
          (79 : ZMod 16062686641) ^ 1914 = (79 : ZMod 16062686641) ^ (957 + 957) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 957 * (79 : ZMod 16062686641) ^ 957 := by rw [pow_add]
          _ = 10055409338 := by rw [fermat_9]; decide
      have fermat_11 : (79 : ZMod 16062686641) ^ 3829 = 11879287356 := by
        calc
          (79 : ZMod 16062686641) ^ 3829 = (79 : ZMod 16062686641) ^ (1914 + 1914 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 1914 * (79 : ZMod 16062686641) ^ 1914) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 11879287356 := by rw [fermat_10]; decide
      have fermat_12 : (79 : ZMod 16062686641) ^ 7659 = 2925684464 := by
        calc
          (79 : ZMod 16062686641) ^ 7659 = (79 : ZMod 16062686641) ^ (3829 + 3829 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 3829 * (79 : ZMod 16062686641) ^ 3829) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 2925684464 := by rw [fermat_11]; decide
      have fermat_13 : (79 : ZMod 16062686641) ^ 15318 = 15323772502 := by
        calc
          (79 : ZMod 16062686641) ^ 15318 = (79 : ZMod 16062686641) ^ (7659 + 7659) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 7659 * (79 : ZMod 16062686641) ^ 7659 := by rw [pow_add]
          _ = 15323772502 := by rw [fermat_12]; decide
      have fermat_14 : (79 : ZMod 16062686641) ^ 30637 = 3005796462 := by
        calc
          (79 : ZMod 16062686641) ^ 30637 = (79 : ZMod 16062686641) ^ (15318 + 15318 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 15318 * (79 : ZMod 16062686641) ^ 15318) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 3005796462 := by rw [fermat_13]; decide
      have fermat_15 : (79 : ZMod 16062686641) ^ 61274 = 7187400189 := by
        calc
          (79 : ZMod 16062686641) ^ 61274 = (79 : ZMod 16062686641) ^ (30637 + 30637) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 30637 * (79 : ZMod 16062686641) ^ 30637 := by rw [pow_add]
          _ = 7187400189 := by rw [fermat_14]; decide
      have fermat_16 : (79 : ZMod 16062686641) ^ 122548 = 15665633998 := by
        calc
          (79 : ZMod 16062686641) ^ 122548 = (79 : ZMod 16062686641) ^ (61274 + 61274) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 61274 * (79 : ZMod 16062686641) ^ 61274 := by rw [pow_add]
          _ = 15665633998 := by rw [fermat_15]; decide
      have fermat_17 : (79 : ZMod 16062686641) ^ 245097 = 156701446 := by
        calc
          (79 : ZMod 16062686641) ^ 245097 = (79 : ZMod 16062686641) ^ (122548 + 122548 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 122548 * (79 : ZMod 16062686641) ^ 122548) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 156701446 := by rw [fermat_16]; decide
      have fermat_18 : (79 : ZMod 16062686641) ^ 490194 = 8919348037 := by
        calc
          (79 : ZMod 16062686641) ^ 490194 = (79 : ZMod 16062686641) ^ (245097 + 245097) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 245097 * (79 : ZMod 16062686641) ^ 245097 := by rw [pow_add]
          _ = 8919348037 := by rw [fermat_17]; decide
      have fermat_19 : (79 : ZMod 16062686641) ^ 980388 = 4396259768 := by
        calc
          (79 : ZMod 16062686641) ^ 980388 = (79 : ZMod 16062686641) ^ (490194 + 490194) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 490194 * (79 : ZMod 16062686641) ^ 490194 := by rw [pow_add]
          _ = 4396259768 := by rw [fermat_18]; decide
      have fermat_20 : (79 : ZMod 16062686641) ^ 1960777 = 13954888302 := by
        calc
          (79 : ZMod 16062686641) ^ 1960777 = (79 : ZMod 16062686641) ^ (980388 + 980388 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 980388 * (79 : ZMod 16062686641) ^ 980388) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 13954888302 := by rw [fermat_19]; decide
      have fermat_21 : (79 : ZMod 16062686641) ^ 3921554 = 1946358721 := by
        calc
          (79 : ZMod 16062686641) ^ 3921554 = (79 : ZMod 16062686641) ^ (1960777 + 1960777) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 1960777 * (79 : ZMod 16062686641) ^ 1960777 := by rw [pow_add]
          _ = 1946358721 := by rw [fermat_20]; decide
      have fermat_22 : (79 : ZMod 16062686641) ^ 7843108 = 4998910187 := by
        calc
          (79 : ZMod 16062686641) ^ 7843108 = (79 : ZMod 16062686641) ^ (3921554 + 3921554) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 3921554 * (79 : ZMod 16062686641) ^ 3921554 := by rw [pow_add]
          _ = 4998910187 := by rw [fermat_21]; decide
      have fermat_23 : (79 : ZMod 16062686641) ^ 15686217 = 8905608091 := by
        calc
          (79 : ZMod 16062686641) ^ 15686217 = (79 : ZMod 16062686641) ^ (7843108 + 7843108 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 7843108 * (79 : ZMod 16062686641) ^ 7843108) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 8905608091 := by rw [fermat_22]; decide
      have fermat_24 : (79 : ZMod 16062686641) ^ 31372434 = 4969481183 := by
        calc
          (79 : ZMod 16062686641) ^ 31372434 = (79 : ZMod 16062686641) ^ (15686217 + 15686217) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 15686217 * (79 : ZMod 16062686641) ^ 15686217 := by rw [pow_add]
          _ = 4969481183 := by rw [fermat_23]; decide
      have fermat_25 : (79 : ZMod 16062686641) ^ 62744869 = 11180693957 := by
        calc
          (79 : ZMod 16062686641) ^ 62744869 = (79 : ZMod 16062686641) ^ (31372434 + 31372434 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 31372434 * (79 : ZMod 16062686641) ^ 31372434) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 11180693957 := by rw [fermat_24]; decide
      have fermat_26 : (79 : ZMod 16062686641) ^ 125489739 = 13071831099 := by
        calc
          (79 : ZMod 16062686641) ^ 125489739 = (79 : ZMod 16062686641) ^ (62744869 + 62744869 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 62744869 * (79 : ZMod 16062686641) ^ 62744869) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 13071831099 := by rw [fermat_25]; decide
      have fermat_27 : (79 : ZMod 16062686641) ^ 250979478 = 6948597974 := by
        calc
          (79 : ZMod 16062686641) ^ 250979478 = (79 : ZMod 16062686641) ^ (125489739 + 125489739) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 125489739 * (79 : ZMod 16062686641) ^ 125489739 := by rw [pow_add]
          _ = 6948597974 := by rw [fermat_26]; decide
      have fermat_28 : (79 : ZMod 16062686641) ^ 501958957 = 7701227022 := by
        calc
          (79 : ZMod 16062686641) ^ 501958957 = (79 : ZMod 16062686641) ^ (250979478 + 250979478 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 250979478 * (79 : ZMod 16062686641) ^ 250979478) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 7701227022 := by rw [fermat_27]; decide
      have fermat_29 : (79 : ZMod 16062686641) ^ 1003917915 = 7038096710 := by
        calc
          (79 : ZMod 16062686641) ^ 1003917915 = (79 : ZMod 16062686641) ^ (501958957 + 501958957 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 501958957 * (79 : ZMod 16062686641) ^ 501958957) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 7038096710 := by rw [fermat_28]; decide
      have fermat_30 : (79 : ZMod 16062686641) ^ 2007835830 = 14316230205 := by
        calc
          (79 : ZMod 16062686641) ^ 2007835830 = (79 : ZMod 16062686641) ^ (1003917915 + 1003917915) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 1003917915 * (79 : ZMod 16062686641) ^ 1003917915 := by rw [pow_add]
          _ = 14316230205 := by rw [fermat_29]; decide
      have fermat_31 : (79 : ZMod 16062686641) ^ 4015671660 = 7287978581 := by
        calc
          (79 : ZMod 16062686641) ^ 4015671660 = (79 : ZMod 16062686641) ^ (2007835830 + 2007835830) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 2007835830 * (79 : ZMod 16062686641) ^ 2007835830 := by rw [pow_add]
          _ = 7287978581 := by rw [fermat_30]; decide
      have fermat_32 : (79 : ZMod 16062686641) ^ 8031343320 = 16062686640 := by
        calc
          (79 : ZMod 16062686641) ^ 8031343320 = (79 : ZMod 16062686641) ^ (4015671660 + 4015671660) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 4015671660 * (79 : ZMod 16062686641) ^ 4015671660 := by rw [pow_add]
          _ = 16062686640 := by rw [fermat_31]; decide
      have fermat_33 : (79 : ZMod 16062686641) ^ 16062686640 = 1 := by
        calc
          (79 : ZMod 16062686641) ^ 16062686640 = (79 : ZMod 16062686641) ^ (8031343320 + 8031343320) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 8031343320 * (79 : ZMod 16062686641) ^ 8031343320 := by rw [pow_add]
          _ = 1 := by rw [fermat_32]; decide
      simpa using fermat_33
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 3), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 3), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod = 16062686641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (79 : ZMod 16062686641) ^ 1 = 79 := by norm_num
      have factor_0_1 : (79 : ZMod 16062686641) ^ 3 = 493039 := by
        calc
          (79 : ZMod 16062686641) ^ 3 = (79 : ZMod 16062686641) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 1 * (79 : ZMod 16062686641) ^ 1) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 493039 := by rw [factor_0_0]; decide
      have factor_0_2 : (79 : ZMod 16062686641) ^ 7 = 8998450164 := by
        calc
          (79 : ZMod 16062686641) ^ 7 = (79 : ZMod 16062686641) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 3 * (79 : ZMod 16062686641) ^ 3) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 8998450164 := by rw [factor_0_1]; decide
      have factor_0_3 : (79 : ZMod 16062686641) ^ 14 = 14713143187 := by
        calc
          (79 : ZMod 16062686641) ^ 14 = (79 : ZMod 16062686641) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 7 * (79 : ZMod 16062686641) ^ 7 := by rw [pow_add]
          _ = 14713143187 := by rw [factor_0_2]; decide
      have factor_0_4 : (79 : ZMod 16062686641) ^ 29 = 12912813422 := by
        calc
          (79 : ZMod 16062686641) ^ 29 = (79 : ZMod 16062686641) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 14 * (79 : ZMod 16062686641) ^ 14) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 12912813422 := by rw [factor_0_3]; decide
      have factor_0_5 : (79 : ZMod 16062686641) ^ 59 = 2947626042 := by
        calc
          (79 : ZMod 16062686641) ^ 59 = (79 : ZMod 16062686641) ^ (29 + 29 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 29 * (79 : ZMod 16062686641) ^ 29) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 2947626042 := by rw [factor_0_4]; decide
      have factor_0_6 : (79 : ZMod 16062686641) ^ 119 = 9972289066 := by
        calc
          (79 : ZMod 16062686641) ^ 119 = (79 : ZMod 16062686641) ^ (59 + 59 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 59 * (79 : ZMod 16062686641) ^ 59) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 9972289066 := by rw [factor_0_5]; decide
      have factor_0_7 : (79 : ZMod 16062686641) ^ 239 = 14030169541 := by
        calc
          (79 : ZMod 16062686641) ^ 239 = (79 : ZMod 16062686641) ^ (119 + 119 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 119 * (79 : ZMod 16062686641) ^ 119) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 14030169541 := by rw [factor_0_6]; decide
      have factor_0_8 : (79 : ZMod 16062686641) ^ 478 = 7519161480 := by
        calc
          (79 : ZMod 16062686641) ^ 478 = (79 : ZMod 16062686641) ^ (239 + 239) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 239 * (79 : ZMod 16062686641) ^ 239 := by rw [pow_add]
          _ = 7519161480 := by rw [factor_0_7]; decide
      have factor_0_9 : (79 : ZMod 16062686641) ^ 957 = 8225209508 := by
        calc
          (79 : ZMod 16062686641) ^ 957 = (79 : ZMod 16062686641) ^ (478 + 478 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 478 * (79 : ZMod 16062686641) ^ 478) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 8225209508 := by rw [factor_0_8]; decide
      have factor_0_10 : (79 : ZMod 16062686641) ^ 1914 = 10055409338 := by
        calc
          (79 : ZMod 16062686641) ^ 1914 = (79 : ZMod 16062686641) ^ (957 + 957) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 957 * (79 : ZMod 16062686641) ^ 957 := by rw [pow_add]
          _ = 10055409338 := by rw [factor_0_9]; decide
      have factor_0_11 : (79 : ZMod 16062686641) ^ 3829 = 11879287356 := by
        calc
          (79 : ZMod 16062686641) ^ 3829 = (79 : ZMod 16062686641) ^ (1914 + 1914 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 1914 * (79 : ZMod 16062686641) ^ 1914) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 11879287356 := by rw [factor_0_10]; decide
      have factor_0_12 : (79 : ZMod 16062686641) ^ 7659 = 2925684464 := by
        calc
          (79 : ZMod 16062686641) ^ 7659 = (79 : ZMod 16062686641) ^ (3829 + 3829 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 3829 * (79 : ZMod 16062686641) ^ 3829) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 2925684464 := by rw [factor_0_11]; decide
      have factor_0_13 : (79 : ZMod 16062686641) ^ 15318 = 15323772502 := by
        calc
          (79 : ZMod 16062686641) ^ 15318 = (79 : ZMod 16062686641) ^ (7659 + 7659) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 7659 * (79 : ZMod 16062686641) ^ 7659 := by rw [pow_add]
          _ = 15323772502 := by rw [factor_0_12]; decide
      have factor_0_14 : (79 : ZMod 16062686641) ^ 30637 = 3005796462 := by
        calc
          (79 : ZMod 16062686641) ^ 30637 = (79 : ZMod 16062686641) ^ (15318 + 15318 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 15318 * (79 : ZMod 16062686641) ^ 15318) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 3005796462 := by rw [factor_0_13]; decide
      have factor_0_15 : (79 : ZMod 16062686641) ^ 61274 = 7187400189 := by
        calc
          (79 : ZMod 16062686641) ^ 61274 = (79 : ZMod 16062686641) ^ (30637 + 30637) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 30637 * (79 : ZMod 16062686641) ^ 30637 := by rw [pow_add]
          _ = 7187400189 := by rw [factor_0_14]; decide
      have factor_0_16 : (79 : ZMod 16062686641) ^ 122548 = 15665633998 := by
        calc
          (79 : ZMod 16062686641) ^ 122548 = (79 : ZMod 16062686641) ^ (61274 + 61274) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 61274 * (79 : ZMod 16062686641) ^ 61274 := by rw [pow_add]
          _ = 15665633998 := by rw [factor_0_15]; decide
      have factor_0_17 : (79 : ZMod 16062686641) ^ 245097 = 156701446 := by
        calc
          (79 : ZMod 16062686641) ^ 245097 = (79 : ZMod 16062686641) ^ (122548 + 122548 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 122548 * (79 : ZMod 16062686641) ^ 122548) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 156701446 := by rw [factor_0_16]; decide
      have factor_0_18 : (79 : ZMod 16062686641) ^ 490194 = 8919348037 := by
        calc
          (79 : ZMod 16062686641) ^ 490194 = (79 : ZMod 16062686641) ^ (245097 + 245097) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 245097 * (79 : ZMod 16062686641) ^ 245097 := by rw [pow_add]
          _ = 8919348037 := by rw [factor_0_17]; decide
      have factor_0_19 : (79 : ZMod 16062686641) ^ 980388 = 4396259768 := by
        calc
          (79 : ZMod 16062686641) ^ 980388 = (79 : ZMod 16062686641) ^ (490194 + 490194) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 490194 * (79 : ZMod 16062686641) ^ 490194 := by rw [pow_add]
          _ = 4396259768 := by rw [factor_0_18]; decide
      have factor_0_20 : (79 : ZMod 16062686641) ^ 1960777 = 13954888302 := by
        calc
          (79 : ZMod 16062686641) ^ 1960777 = (79 : ZMod 16062686641) ^ (980388 + 980388 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 980388 * (79 : ZMod 16062686641) ^ 980388) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 13954888302 := by rw [factor_0_19]; decide
      have factor_0_21 : (79 : ZMod 16062686641) ^ 3921554 = 1946358721 := by
        calc
          (79 : ZMod 16062686641) ^ 3921554 = (79 : ZMod 16062686641) ^ (1960777 + 1960777) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 1960777 * (79 : ZMod 16062686641) ^ 1960777 := by rw [pow_add]
          _ = 1946358721 := by rw [factor_0_20]; decide
      have factor_0_22 : (79 : ZMod 16062686641) ^ 7843108 = 4998910187 := by
        calc
          (79 : ZMod 16062686641) ^ 7843108 = (79 : ZMod 16062686641) ^ (3921554 + 3921554) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 3921554 * (79 : ZMod 16062686641) ^ 3921554 := by rw [pow_add]
          _ = 4998910187 := by rw [factor_0_21]; decide
      have factor_0_23 : (79 : ZMod 16062686641) ^ 15686217 = 8905608091 := by
        calc
          (79 : ZMod 16062686641) ^ 15686217 = (79 : ZMod 16062686641) ^ (7843108 + 7843108 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 7843108 * (79 : ZMod 16062686641) ^ 7843108) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 8905608091 := by rw [factor_0_22]; decide
      have factor_0_24 : (79 : ZMod 16062686641) ^ 31372434 = 4969481183 := by
        calc
          (79 : ZMod 16062686641) ^ 31372434 = (79 : ZMod 16062686641) ^ (15686217 + 15686217) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 15686217 * (79 : ZMod 16062686641) ^ 15686217 := by rw [pow_add]
          _ = 4969481183 := by rw [factor_0_23]; decide
      have factor_0_25 : (79 : ZMod 16062686641) ^ 62744869 = 11180693957 := by
        calc
          (79 : ZMod 16062686641) ^ 62744869 = (79 : ZMod 16062686641) ^ (31372434 + 31372434 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 31372434 * (79 : ZMod 16062686641) ^ 31372434) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 11180693957 := by rw [factor_0_24]; decide
      have factor_0_26 : (79 : ZMod 16062686641) ^ 125489739 = 13071831099 := by
        calc
          (79 : ZMod 16062686641) ^ 125489739 = (79 : ZMod 16062686641) ^ (62744869 + 62744869 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 62744869 * (79 : ZMod 16062686641) ^ 62744869) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 13071831099 := by rw [factor_0_25]; decide
      have factor_0_27 : (79 : ZMod 16062686641) ^ 250979478 = 6948597974 := by
        calc
          (79 : ZMod 16062686641) ^ 250979478 = (79 : ZMod 16062686641) ^ (125489739 + 125489739) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 125489739 * (79 : ZMod 16062686641) ^ 125489739 := by rw [pow_add]
          _ = 6948597974 := by rw [factor_0_26]; decide
      have factor_0_28 : (79 : ZMod 16062686641) ^ 501958957 = 7701227022 := by
        calc
          (79 : ZMod 16062686641) ^ 501958957 = (79 : ZMod 16062686641) ^ (250979478 + 250979478 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 250979478 * (79 : ZMod 16062686641) ^ 250979478) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 7701227022 := by rw [factor_0_27]; decide
      have factor_0_29 : (79 : ZMod 16062686641) ^ 1003917915 = 7038096710 := by
        calc
          (79 : ZMod 16062686641) ^ 1003917915 = (79 : ZMod 16062686641) ^ (501958957 + 501958957 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 501958957 * (79 : ZMod 16062686641) ^ 501958957) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 7038096710 := by rw [factor_0_28]; decide
      have factor_0_30 : (79 : ZMod 16062686641) ^ 2007835830 = 14316230205 := by
        calc
          (79 : ZMod 16062686641) ^ 2007835830 = (79 : ZMod 16062686641) ^ (1003917915 + 1003917915) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 1003917915 * (79 : ZMod 16062686641) ^ 1003917915 := by rw [pow_add]
          _ = 14316230205 := by rw [factor_0_29]; decide
      have factor_0_31 : (79 : ZMod 16062686641) ^ 4015671660 = 7287978581 := by
        calc
          (79 : ZMod 16062686641) ^ 4015671660 = (79 : ZMod 16062686641) ^ (2007835830 + 2007835830) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 2007835830 * (79 : ZMod 16062686641) ^ 2007835830 := by rw [pow_add]
          _ = 7287978581 := by rw [factor_0_30]; decide
      have factor_0_32 : (79 : ZMod 16062686641) ^ 8031343320 = 16062686640 := by
        calc
          (79 : ZMod 16062686641) ^ 8031343320 = (79 : ZMod 16062686641) ^ (4015671660 + 4015671660) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 4015671660 * (79 : ZMod 16062686641) ^ 4015671660 := by rw [pow_add]
          _ = 16062686640 := by rw [factor_0_31]; decide
      change (79 : ZMod 16062686641) ^ 8031343320 ≠ 1
      rw [factor_0_32]
      decide
    ·
      have factor_1_0 : (79 : ZMod 16062686641) ^ 1 = 79 := by norm_num
      have factor_1_1 : (79 : ZMod 16062686641) ^ 2 = 6241 := by
        calc
          (79 : ZMod 16062686641) ^ 2 = (79 : ZMod 16062686641) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 1 * (79 : ZMod 16062686641) ^ 1 := by rw [pow_add]
          _ = 6241 := by rw [factor_1_0]; decide
      have factor_1_2 : (79 : ZMod 16062686641) ^ 4 = 38950081 := by
        calc
          (79 : ZMod 16062686641) ^ 4 = (79 : ZMod 16062686641) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 2 * (79 : ZMod 16062686641) ^ 2 := by rw [pow_add]
          _ = 38950081 := by rw [factor_1_1]; decide
      have factor_1_3 : (79 : ZMod 16062686641) ^ 9 = 4174976588 := by
        calc
          (79 : ZMod 16062686641) ^ 9 = (79 : ZMod 16062686641) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 4 * (79 : ZMod 16062686641) ^ 4) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 4174976588 := by rw [factor_1_2]; decide
      have factor_1_4 : (79 : ZMod 16062686641) ^ 19 = 2557571804 := by
        calc
          (79 : ZMod 16062686641) ^ 19 = (79 : ZMod 16062686641) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 9 * (79 : ZMod 16062686641) ^ 9) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 2557571804 := by rw [factor_1_3]; decide
      have factor_1_5 : (79 : ZMod 16062686641) ^ 39 = 10151692917 := by
        calc
          (79 : ZMod 16062686641) ^ 39 = (79 : ZMod 16062686641) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 19 * (79 : ZMod 16062686641) ^ 19) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 10151692917 := by rw [factor_1_4]; decide
      have factor_1_6 : (79 : ZMod 16062686641) ^ 79 = 14448837887 := by
        calc
          (79 : ZMod 16062686641) ^ 79 = (79 : ZMod 16062686641) ^ (39 + 39 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 39 * (79 : ZMod 16062686641) ^ 39) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 14448837887 := by rw [factor_1_5]; decide
      have factor_1_7 : (79 : ZMod 16062686641) ^ 159 = 5598683827 := by
        calc
          (79 : ZMod 16062686641) ^ 159 = (79 : ZMod 16062686641) ^ (79 + 79 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 79 * (79 : ZMod 16062686641) ^ 79) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 5598683827 := by rw [factor_1_6]; decide
      have factor_1_8 : (79 : ZMod 16062686641) ^ 319 = 1453462949 := by
        calc
          (79 : ZMod 16062686641) ^ 319 = (79 : ZMod 16062686641) ^ (159 + 159 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 159 * (79 : ZMod 16062686641) ^ 159) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 1453462949 := by rw [factor_1_7]; decide
      have factor_1_9 : (79 : ZMod 16062686641) ^ 638 = 4145233944 := by
        calc
          (79 : ZMod 16062686641) ^ 638 = (79 : ZMod 16062686641) ^ (319 + 319) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 319 * (79 : ZMod 16062686641) ^ 319 := by rw [pow_add]
          _ = 4145233944 := by rw [factor_1_8]; decide
      have factor_1_10 : (79 : ZMod 16062686641) ^ 1276 = 9441673985 := by
        calc
          (79 : ZMod 16062686641) ^ 1276 = (79 : ZMod 16062686641) ^ (638 + 638) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 638 * (79 : ZMod 16062686641) ^ 638 := by rw [pow_add]
          _ = 9441673985 := by rw [factor_1_9]; decide
      have factor_1_11 : (79 : ZMod 16062686641) ^ 2553 = 6801124748 := by
        calc
          (79 : ZMod 16062686641) ^ 2553 = (79 : ZMod 16062686641) ^ (1276 + 1276 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 1276 * (79 : ZMod 16062686641) ^ 1276) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 6801124748 := by rw [factor_1_10]; decide
      have factor_1_12 : (79 : ZMod 16062686641) ^ 5106 = 8348417627 := by
        calc
          (79 : ZMod 16062686641) ^ 5106 = (79 : ZMod 16062686641) ^ (2553 + 2553) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 2553 * (79 : ZMod 16062686641) ^ 2553 := by rw [pow_add]
          _ = 8348417627 := by rw [factor_1_11]; decide
      have factor_1_13 : (79 : ZMod 16062686641) ^ 10212 = 13143751538 := by
        calc
          (79 : ZMod 16062686641) ^ 10212 = (79 : ZMod 16062686641) ^ (5106 + 5106) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 5106 * (79 : ZMod 16062686641) ^ 5106 := by rw [pow_add]
          _ = 13143751538 := by rw [factor_1_12]; decide
      have factor_1_14 : (79 : ZMod 16062686641) ^ 20424 = 4506919178 := by
        calc
          (79 : ZMod 16062686641) ^ 20424 = (79 : ZMod 16062686641) ^ (10212 + 10212) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 10212 * (79 : ZMod 16062686641) ^ 10212 := by rw [pow_add]
          _ = 4506919178 := by rw [factor_1_13]; decide
      have factor_1_15 : (79 : ZMod 16062686641) ^ 40849 = 7600058420 := by
        calc
          (79 : ZMod 16062686641) ^ 40849 = (79 : ZMod 16062686641) ^ (20424 + 20424 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 20424 * (79 : ZMod 16062686641) ^ 20424) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 7600058420 := by rw [factor_1_14]; decide
      have factor_1_16 : (79 : ZMod 16062686641) ^ 81699 = 1135597311 := by
        calc
          (79 : ZMod 16062686641) ^ 81699 = (79 : ZMod 16062686641) ^ (40849 + 40849 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 40849 * (79 : ZMod 16062686641) ^ 40849) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 1135597311 := by rw [factor_1_15]; decide
      have factor_1_17 : (79 : ZMod 16062686641) ^ 163398 = 4849440600 := by
        calc
          (79 : ZMod 16062686641) ^ 163398 = (79 : ZMod 16062686641) ^ (81699 + 81699) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 81699 * (79 : ZMod 16062686641) ^ 81699 := by rw [pow_add]
          _ = 4849440600 := by rw [factor_1_16]; decide
      have factor_1_18 : (79 : ZMod 16062686641) ^ 326796 = 5638678692 := by
        calc
          (79 : ZMod 16062686641) ^ 326796 = (79 : ZMod 16062686641) ^ (163398 + 163398) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 163398 * (79 : ZMod 16062686641) ^ 163398 := by rw [pow_add]
          _ = 5638678692 := by rw [factor_1_17]; decide
      have factor_1_19 : (79 : ZMod 16062686641) ^ 653592 = 5603515131 := by
        calc
          (79 : ZMod 16062686641) ^ 653592 = (79 : ZMod 16062686641) ^ (326796 + 326796) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 326796 * (79 : ZMod 16062686641) ^ 326796 := by rw [pow_add]
          _ = 5603515131 := by rw [factor_1_18]; decide
      have factor_1_20 : (79 : ZMod 16062686641) ^ 1307184 = 5718954228 := by
        calc
          (79 : ZMod 16062686641) ^ 1307184 = (79 : ZMod 16062686641) ^ (653592 + 653592) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 653592 * (79 : ZMod 16062686641) ^ 653592 := by rw [pow_add]
          _ = 5718954228 := by rw [factor_1_19]; decide
      have factor_1_21 : (79 : ZMod 16062686641) ^ 2614369 = 8922601396 := by
        calc
          (79 : ZMod 16062686641) ^ 2614369 = (79 : ZMod 16062686641) ^ (1307184 + 1307184 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 1307184 * (79 : ZMod 16062686641) ^ 1307184) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 8922601396 := by rw [factor_1_20]; decide
      have factor_1_22 : (79 : ZMod 16062686641) ^ 5228739 = 697715907 := by
        calc
          (79 : ZMod 16062686641) ^ 5228739 = (79 : ZMod 16062686641) ^ (2614369 + 2614369 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 2614369 * (79 : ZMod 16062686641) ^ 2614369) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 697715907 := by rw [factor_1_21]; decide
      have factor_1_23 : (79 : ZMod 16062686641) ^ 10457478 = 11902812001 := by
        calc
          (79 : ZMod 16062686641) ^ 10457478 = (79 : ZMod 16062686641) ^ (5228739 + 5228739) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 5228739 * (79 : ZMod 16062686641) ^ 5228739 := by rw [pow_add]
          _ = 11902812001 := by rw [factor_1_22]; decide
      have factor_1_24 : (79 : ZMod 16062686641) ^ 20914956 = 1242408651 := by
        calc
          (79 : ZMod 16062686641) ^ 20914956 = (79 : ZMod 16062686641) ^ (10457478 + 10457478) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 10457478 * (79 : ZMod 16062686641) ^ 10457478 := by rw [pow_add]
          _ = 1242408651 := by rw [factor_1_23]; decide
      have factor_1_25 : (79 : ZMod 16062686641) ^ 41829913 = 4789512536 := by
        calc
          (79 : ZMod 16062686641) ^ 41829913 = (79 : ZMod 16062686641) ^ (20914956 + 20914956 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 20914956 * (79 : ZMod 16062686641) ^ 20914956) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 4789512536 := by rw [factor_1_24]; decide
      have factor_1_26 : (79 : ZMod 16062686641) ^ 83659826 = 4290622710 := by
        calc
          (79 : ZMod 16062686641) ^ 83659826 = (79 : ZMod 16062686641) ^ (41829913 + 41829913) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 41829913 * (79 : ZMod 16062686641) ^ 41829913 := by rw [pow_add]
          _ = 4290622710 := by rw [factor_1_25]; decide
      have factor_1_27 : (79 : ZMod 16062686641) ^ 167319652 = 7840041020 := by
        calc
          (79 : ZMod 16062686641) ^ 167319652 = (79 : ZMod 16062686641) ^ (83659826 + 83659826) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 83659826 * (79 : ZMod 16062686641) ^ 83659826 := by rw [pow_add]
          _ = 7840041020 := by rw [factor_1_26]; decide
      have factor_1_28 : (79 : ZMod 16062686641) ^ 334639305 = 7757323082 := by
        calc
          (79 : ZMod 16062686641) ^ 334639305 = (79 : ZMod 16062686641) ^ (167319652 + 167319652 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 167319652 * (79 : ZMod 16062686641) ^ 167319652) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 7757323082 := by rw [factor_1_27]; decide
      have factor_1_29 : (79 : ZMod 16062686641) ^ 669278610 = 2364680674 := by
        calc
          (79 : ZMod 16062686641) ^ 669278610 = (79 : ZMod 16062686641) ^ (334639305 + 334639305) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 334639305 * (79 : ZMod 16062686641) ^ 334639305 := by rw [pow_add]
          _ = 2364680674 := by rw [factor_1_28]; decide
      have factor_1_30 : (79 : ZMod 16062686641) ^ 1338557220 = 4972063206 := by
        calc
          (79 : ZMod 16062686641) ^ 1338557220 = (79 : ZMod 16062686641) ^ (669278610 + 669278610) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 669278610 * (79 : ZMod 16062686641) ^ 669278610 := by rw [pow_add]
          _ = 4972063206 := by rw [factor_1_29]; decide
      have factor_1_31 : (79 : ZMod 16062686641) ^ 2677114440 = 12188523574 := by
        calc
          (79 : ZMod 16062686641) ^ 2677114440 = (79 : ZMod 16062686641) ^ (1338557220 + 1338557220) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 1338557220 * (79 : ZMod 16062686641) ^ 1338557220 := by rw [pow_add]
          _ = 12188523574 := by rw [factor_1_30]; decide
      have factor_1_32 : (79 : ZMod 16062686641) ^ 5354228880 = 12188523573 := by
        calc
          (79 : ZMod 16062686641) ^ 5354228880 = (79 : ZMod 16062686641) ^ (2677114440 + 2677114440) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 2677114440 * (79 : ZMod 16062686641) ^ 2677114440 := by rw [pow_add]
          _ = 12188523573 := by rw [factor_1_31]; decide
      change (79 : ZMod 16062686641) ^ 5354228880 ≠ 1
      rw [factor_1_32]
      decide
    ·
      have factor_2_0 : (79 : ZMod 16062686641) ^ 1 = 79 := by norm_num
      have factor_2_1 : (79 : ZMod 16062686641) ^ 2 = 6241 := by
        calc
          (79 : ZMod 16062686641) ^ 2 = (79 : ZMod 16062686641) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 1 * (79 : ZMod 16062686641) ^ 1 := by rw [pow_add]
          _ = 6241 := by rw [factor_2_0]; decide
      have factor_2_2 : (79 : ZMod 16062686641) ^ 5 = 3077056399 := by
        calc
          (79 : ZMod 16062686641) ^ 5 = (79 : ZMod 16062686641) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 2 * (79 : ZMod 16062686641) ^ 2) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 3077056399 := by rw [factor_2_1]; decide
      have factor_2_3 : (79 : ZMod 16062686641) ^ 11 = 2351154006 := by
        calc
          (79 : ZMod 16062686641) ^ 11 = (79 : ZMod 16062686641) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 5 * (79 : ZMod 16062686641) ^ 5) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 2351154006 := by rw [factor_2_2]; decide
      have factor_2_4 : (79 : ZMod 16062686641) ^ 23 = 10730902401 := by
        calc
          (79 : ZMod 16062686641) ^ 23 = (79 : ZMod 16062686641) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 11 * (79 : ZMod 16062686641) ^ 11) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 10730902401 := by rw [factor_2_3]; decide
      have factor_2_5 : (79 : ZMod 16062686641) ^ 47 = 1223565325 := by
        calc
          (79 : ZMod 16062686641) ^ 47 = (79 : ZMod 16062686641) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 23 * (79 : ZMod 16062686641) ^ 23) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 1223565325 := by rw [factor_2_4]; decide
      have factor_2_6 : (79 : ZMod 16062686641) ^ 95 = 14564487448 := by
        calc
          (79 : ZMod 16062686641) ^ 95 = (79 : ZMod 16062686641) ^ (47 + 47 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 47 * (79 : ZMod 16062686641) ^ 47) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 14564487448 := by rw [factor_2_5]; decide
      have factor_2_7 : (79 : ZMod 16062686641) ^ 191 = 7299073719 := by
        calc
          (79 : ZMod 16062686641) ^ 191 = (79 : ZMod 16062686641) ^ (95 + 95 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 95 * (79 : ZMod 16062686641) ^ 95) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 7299073719 := by rw [factor_2_6]; decide
      have factor_2_8 : (79 : ZMod 16062686641) ^ 382 = 8588504421 := by
        calc
          (79 : ZMod 16062686641) ^ 382 = (79 : ZMod 16062686641) ^ (191 + 191) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 191 * (79 : ZMod 16062686641) ^ 191 := by rw [pow_add]
          _ = 8588504421 := by rw [factor_2_7]; decide
      have factor_2_9 : (79 : ZMod 16062686641) ^ 765 = 1677128733 := by
        calc
          (79 : ZMod 16062686641) ^ 765 = (79 : ZMod 16062686641) ^ (382 + 382 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 382 * (79 : ZMod 16062686641) ^ 382) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 1677128733 := by rw [factor_2_8]; decide
      have factor_2_10 : (79 : ZMod 16062686641) ^ 1531 = 6638223285 := by
        calc
          (79 : ZMod 16062686641) ^ 1531 = (79 : ZMod 16062686641) ^ (765 + 765 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 765 * (79 : ZMod 16062686641) ^ 765) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 6638223285 := by rw [factor_2_9]; decide
      have factor_2_11 : (79 : ZMod 16062686641) ^ 3063 = 11751112703 := by
        calc
          (79 : ZMod 16062686641) ^ 3063 = (79 : ZMod 16062686641) ^ (1531 + 1531 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 1531 * (79 : ZMod 16062686641) ^ 1531) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 11751112703 := by rw [factor_2_10]; decide
      have factor_2_12 : (79 : ZMod 16062686641) ^ 6127 = 8044306227 := by
        calc
          (79 : ZMod 16062686641) ^ 6127 = (79 : ZMod 16062686641) ^ (3063 + 3063 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 3063 * (79 : ZMod 16062686641) ^ 3063) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 8044306227 := by rw [factor_2_11]; decide
      have factor_2_13 : (79 : ZMod 16062686641) ^ 12254 = 1164304581 := by
        calc
          (79 : ZMod 16062686641) ^ 12254 = (79 : ZMod 16062686641) ^ (6127 + 6127) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 6127 * (79 : ZMod 16062686641) ^ 6127 := by rw [pow_add]
          _ = 1164304581 := by rw [factor_2_12]; decide
      have factor_2_14 : (79 : ZMod 16062686641) ^ 24509 = 3771727576 := by
        calc
          (79 : ZMod 16062686641) ^ 24509 = (79 : ZMod 16062686641) ^ (12254 + 12254 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 12254 * (79 : ZMod 16062686641) ^ 12254) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 3771727576 := by rw [factor_2_13]; decide
      have factor_2_15 : (79 : ZMod 16062686641) ^ 49019 = 8369093062 := by
        calc
          (79 : ZMod 16062686641) ^ 49019 = (79 : ZMod 16062686641) ^ (24509 + 24509 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 24509 * (79 : ZMod 16062686641) ^ 24509) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 8369093062 := by rw [factor_2_14]; decide
      have factor_2_16 : (79 : ZMod 16062686641) ^ 98038 = 12432826107 := by
        calc
          (79 : ZMod 16062686641) ^ 98038 = (79 : ZMod 16062686641) ^ (49019 + 49019) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 49019 * (79 : ZMod 16062686641) ^ 49019 := by rw [pow_add]
          _ = 12432826107 := by rw [factor_2_15]; decide
      have factor_2_17 : (79 : ZMod 16062686641) ^ 196077 = 5830613441 := by
        calc
          (79 : ZMod 16062686641) ^ 196077 = (79 : ZMod 16062686641) ^ (98038 + 98038 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 98038 * (79 : ZMod 16062686641) ^ 98038) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 5830613441 := by rw [factor_2_16]; decide
      have factor_2_18 : (79 : ZMod 16062686641) ^ 392155 = 2942078129 := by
        calc
          (79 : ZMod 16062686641) ^ 392155 = (79 : ZMod 16062686641) ^ (196077 + 196077 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 196077 * (79 : ZMod 16062686641) ^ 196077) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 2942078129 := by rw [factor_2_17]; decide
      have factor_2_19 : (79 : ZMod 16062686641) ^ 784310 = 3903901736 := by
        calc
          (79 : ZMod 16062686641) ^ 784310 = (79 : ZMod 16062686641) ^ (392155 + 392155) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 392155 * (79 : ZMod 16062686641) ^ 392155 := by rw [pow_add]
          _ = 3903901736 := by rw [factor_2_18]; decide
      have factor_2_20 : (79 : ZMod 16062686641) ^ 1568621 = 11711260506 := by
        calc
          (79 : ZMod 16062686641) ^ 1568621 = (79 : ZMod 16062686641) ^ (784310 + 784310 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 784310 * (79 : ZMod 16062686641) ^ 784310) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 11711260506 := by rw [factor_2_19]; decide
      have factor_2_21 : (79 : ZMod 16062686641) ^ 3137243 = 12265590607 := by
        calc
          (79 : ZMod 16062686641) ^ 3137243 = (79 : ZMod 16062686641) ^ (1568621 + 1568621 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 1568621 * (79 : ZMod 16062686641) ^ 1568621) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 12265590607 := by rw [factor_2_20]; decide
      have factor_2_22 : (79 : ZMod 16062686641) ^ 6274486 = 6322275551 := by
        calc
          (79 : ZMod 16062686641) ^ 6274486 = (79 : ZMod 16062686641) ^ (3137243 + 3137243) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 3137243 * (79 : ZMod 16062686641) ^ 3137243 := by rw [pow_add]
          _ = 6322275551 := by rw [factor_2_21]; decide
      have factor_2_23 : (79 : ZMod 16062686641) ^ 12548973 = 6770927347 := by
        calc
          (79 : ZMod 16062686641) ^ 12548973 = (79 : ZMod 16062686641) ^ (6274486 + 6274486 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 6274486 * (79 : ZMod 16062686641) ^ 6274486) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 6770927347 := by rw [factor_2_22]; decide
      have factor_2_24 : (79 : ZMod 16062686641) ^ 25097947 = 15373591615 := by
        calc
          (79 : ZMod 16062686641) ^ 25097947 = (79 : ZMod 16062686641) ^ (12548973 + 12548973 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 12548973 * (79 : ZMod 16062686641) ^ 12548973) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 15373591615 := by rw [factor_2_23]; decide
      have factor_2_25 : (79 : ZMod 16062686641) ^ 50195895 = 13505975340 := by
        calc
          (79 : ZMod 16062686641) ^ 50195895 = (79 : ZMod 16062686641) ^ (25097947 + 25097947 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 25097947 * (79 : ZMod 16062686641) ^ 25097947) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 13505975340 := by rw [factor_2_24]; decide
      have factor_2_26 : (79 : ZMod 16062686641) ^ 100391791 = 6029875957 := by
        calc
          (79 : ZMod 16062686641) ^ 100391791 = (79 : ZMod 16062686641) ^ (50195895 + 50195895 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 50195895 * (79 : ZMod 16062686641) ^ 50195895) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 6029875957 := by rw [factor_2_25]; decide
      have factor_2_27 : (79 : ZMod 16062686641) ^ 200783583 = 6144008751 := by
        calc
          (79 : ZMod 16062686641) ^ 200783583 = (79 : ZMod 16062686641) ^ (100391791 + 100391791 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 100391791 * (79 : ZMod 16062686641) ^ 100391791) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 6144008751 := by rw [factor_2_26]; decide
      have factor_2_28 : (79 : ZMod 16062686641) ^ 401567166 = 3300084674 := by
        calc
          (79 : ZMod 16062686641) ^ 401567166 = (79 : ZMod 16062686641) ^ (200783583 + 200783583) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 200783583 * (79 : ZMod 16062686641) ^ 200783583 := by rw [pow_add]
          _ = 3300084674 := by rw [factor_2_27]; decide
      have factor_2_29 : (79 : ZMod 16062686641) ^ 803134332 = 1305751188 := by
        calc
          (79 : ZMod 16062686641) ^ 803134332 = (79 : ZMod 16062686641) ^ (401567166 + 401567166) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 401567166 * (79 : ZMod 16062686641) ^ 401567166 := by rw [pow_add]
          _ = 1305751188 := by rw [factor_2_28]; decide
      have factor_2_30 : (79 : ZMod 16062686641) ^ 1606268664 = 3499185979 := by
        calc
          (79 : ZMod 16062686641) ^ 1606268664 = (79 : ZMod 16062686641) ^ (803134332 + 803134332) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 803134332 * (79 : ZMod 16062686641) ^ 803134332 := by rw [pow_add]
          _ = 3499185979 := by rw [factor_2_29]; decide
      have factor_2_31 : (79 : ZMod 16062686641) ^ 3212537328 = 11677788732 := by
        calc
          (79 : ZMod 16062686641) ^ 3212537328 = (79 : ZMod 16062686641) ^ (1606268664 + 1606268664) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 1606268664 * (79 : ZMod 16062686641) ^ 1606268664 := by rw [pow_add]
          _ = 11677788732 := by rw [factor_2_30]; decide
      change (79 : ZMod 16062686641) ^ 3212537328 ≠ 1
      rw [factor_2_31]
      decide
    ·
      have factor_3_0 : (79 : ZMod 16062686641) ^ 1 = 79 := by norm_num
      have factor_3_1 : (79 : ZMod 16062686641) ^ 2 = 6241 := by
        calc
          (79 : ZMod 16062686641) ^ 2 = (79 : ZMod 16062686641) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 1 * (79 : ZMod 16062686641) ^ 1 := by rw [pow_add]
          _ = 6241 := by rw [factor_3_0]; decide
      have factor_3_2 : (79 : ZMod 16062686641) ^ 4 = 38950081 := by
        calc
          (79 : ZMod 16062686641) ^ 4 = (79 : ZMod 16062686641) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 2 * (79 : ZMod 16062686641) ^ 2 := by rw [pow_add]
          _ = 38950081 := by rw [factor_3_1]; decide
      have factor_3_3 : (79 : ZMod 16062686641) ^ 8 = 4119350752 := by
        calc
          (79 : ZMod 16062686641) ^ 8 = (79 : ZMod 16062686641) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 4 * (79 : ZMod 16062686641) ^ 4 := by rw [pow_add]
          _ = 4119350752 := by rw [factor_3_2]; decide
      have factor_3_4 : (79 : ZMod 16062686641) ^ 17 = 3176400078 := by
        calc
          (79 : ZMod 16062686641) ^ 17 = (79 : ZMod 16062686641) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 8 * (79 : ZMod 16062686641) ^ 8) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 3176400078 := by rw [factor_3_3]; decide
      have factor_3_5 : (79 : ZMod 16062686641) ^ 34 = 13423208619 := by
        calc
          (79 : ZMod 16062686641) ^ 34 = (79 : ZMod 16062686641) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 17 * (79 : ZMod 16062686641) ^ 17 := by rw [pow_add]
          _ = 13423208619 := by rw [factor_3_4]; decide
      have factor_3_6 : (79 : ZMod 16062686641) ^ 68 = 796336111 := by
        calc
          (79 : ZMod 16062686641) ^ 68 = (79 : ZMod 16062686641) ^ (34 + 34) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 34 * (79 : ZMod 16062686641) ^ 34 := by rw [pow_add]
          _ = 796336111 := by rw [factor_3_5]; decide
      have factor_3_7 : (79 : ZMod 16062686641) ^ 136 = 11451165110 := by
        calc
          (79 : ZMod 16062686641) ^ 136 = (79 : ZMod 16062686641) ^ (68 + 68) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 68 * (79 : ZMod 16062686641) ^ 68 := by rw [pow_add]
          _ = 11451165110 := by rw [factor_3_6]; decide
      have factor_3_8 : (79 : ZMod 16062686641) ^ 273 = 2286924853 := by
        calc
          (79 : ZMod 16062686641) ^ 273 = (79 : ZMod 16062686641) ^ (136 + 136 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 136 * (79 : ZMod 16062686641) ^ 136) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 2286924853 := by rw [factor_3_7]; decide
      have factor_3_9 : (79 : ZMod 16062686641) ^ 547 = 1351195813 := by
        calc
          (79 : ZMod 16062686641) ^ 547 = (79 : ZMod 16062686641) ^ (273 + 273 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 273 * (79 : ZMod 16062686641) ^ 273) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 1351195813 := by rw [factor_3_8]; decide
      have factor_3_10 : (79 : ZMod 16062686641) ^ 1094 = 9240523118 := by
        calc
          (79 : ZMod 16062686641) ^ 1094 = (79 : ZMod 16062686641) ^ (547 + 547) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 547 * (79 : ZMod 16062686641) ^ 547 := by rw [pow_add]
          _ = 9240523118 := by rw [factor_3_9]; decide
      have factor_3_11 : (79 : ZMod 16062686641) ^ 2188 = 9244026541 := by
        calc
          (79 : ZMod 16062686641) ^ 2188 = (79 : ZMod 16062686641) ^ (1094 + 1094) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 1094 * (79 : ZMod 16062686641) ^ 1094 := by rw [pow_add]
          _ = 9244026541 := by rw [factor_3_10]; decide
      have factor_3_12 : (79 : ZMod 16062686641) ^ 4376 = 10817075084 := by
        calc
          (79 : ZMod 16062686641) ^ 4376 = (79 : ZMod 16062686641) ^ (2188 + 2188) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 2188 * (79 : ZMod 16062686641) ^ 2188 := by rw [pow_add]
          _ = 10817075084 := by rw [factor_3_11]; decide
      have factor_3_13 : (79 : ZMod 16062686641) ^ 8753 = 11350247861 := by
        calc
          (79 : ZMod 16062686641) ^ 8753 = (79 : ZMod 16062686641) ^ (4376 + 4376 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 4376 * (79 : ZMod 16062686641) ^ 4376) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 11350247861 := by rw [factor_3_12]; decide
      have factor_3_14 : (79 : ZMod 16062686641) ^ 17506 = 10618704806 := by
        calc
          (79 : ZMod 16062686641) ^ 17506 = (79 : ZMod 16062686641) ^ (8753 + 8753) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 8753 * (79 : ZMod 16062686641) ^ 8753 := by rw [pow_add]
          _ = 10618704806 := by rw [factor_3_13]; decide
      have factor_3_15 : (79 : ZMod 16062686641) ^ 35013 = 7122316956 := by
        calc
          (79 : ZMod 16062686641) ^ 35013 = (79 : ZMod 16062686641) ^ (17506 + 17506 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 17506 * (79 : ZMod 16062686641) ^ 17506) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 7122316956 := by rw [factor_3_14]; decide
      have factor_3_16 : (79 : ZMod 16062686641) ^ 70027 = 11364654348 := by
        calc
          (79 : ZMod 16062686641) ^ 70027 = (79 : ZMod 16062686641) ^ (35013 + 35013 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 35013 * (79 : ZMod 16062686641) ^ 35013) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 11364654348 := by rw [factor_3_15]; decide
      have factor_3_17 : (79 : ZMod 16062686641) ^ 140055 = 12474693158 := by
        calc
          (79 : ZMod 16062686641) ^ 140055 = (79 : ZMod 16062686641) ^ (70027 + 70027 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 70027 * (79 : ZMod 16062686641) ^ 70027) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 12474693158 := by rw [factor_3_16]; decide
      have factor_3_18 : (79 : ZMod 16062686641) ^ 280111 = 5188240680 := by
        calc
          (79 : ZMod 16062686641) ^ 280111 = (79 : ZMod 16062686641) ^ (140055 + 140055 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 140055 * (79 : ZMod 16062686641) ^ 140055) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 5188240680 := by rw [factor_3_17]; decide
      have factor_3_19 : (79 : ZMod 16062686641) ^ 560222 = 11472834796 := by
        calc
          (79 : ZMod 16062686641) ^ 560222 = (79 : ZMod 16062686641) ^ (280111 + 280111) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 280111 * (79 : ZMod 16062686641) ^ 280111 := by rw [pow_add]
          _ = 11472834796 := by rw [factor_3_18]; decide
      have factor_3_20 : (79 : ZMod 16062686641) ^ 1120444 = 6949118532 := by
        calc
          (79 : ZMod 16062686641) ^ 1120444 = (79 : ZMod 16062686641) ^ (560222 + 560222) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 560222 * (79 : ZMod 16062686641) ^ 560222 := by rw [pow_add]
          _ = 6949118532 := by rw [factor_3_19]; decide
      have factor_3_21 : (79 : ZMod 16062686641) ^ 2240888 = 13653415892 := by
        calc
          (79 : ZMod 16062686641) ^ 2240888 = (79 : ZMod 16062686641) ^ (1120444 + 1120444) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 1120444 * (79 : ZMod 16062686641) ^ 1120444 := by rw [pow_add]
          _ = 13653415892 := by rw [factor_3_20]; decide
      have factor_3_22 : (79 : ZMod 16062686641) ^ 4481776 = 5884017585 := by
        calc
          (79 : ZMod 16062686641) ^ 4481776 = (79 : ZMod 16062686641) ^ (2240888 + 2240888) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 2240888 * (79 : ZMod 16062686641) ^ 2240888 := by rw [pow_add]
          _ = 5884017585 := by rw [factor_3_21]; decide
      have factor_3_23 : (79 : ZMod 16062686641) ^ 8963552 = 8418942282 := by
        calc
          (79 : ZMod 16062686641) ^ 8963552 = (79 : ZMod 16062686641) ^ (4481776 + 4481776) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 4481776 * (79 : ZMod 16062686641) ^ 4481776 := by rw [pow_add]
          _ = 8418942282 := by rw [factor_3_22]; decide
      have factor_3_24 : (79 : ZMod 16062686641) ^ 17927105 = 14663787254 := by
        calc
          (79 : ZMod 16062686641) ^ 17927105 = (79 : ZMod 16062686641) ^ (8963552 + 8963552 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 8963552 * (79 : ZMod 16062686641) ^ 8963552) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 14663787254 := by rw [factor_3_23]; decide
      have factor_3_25 : (79 : ZMod 16062686641) ^ 35854211 = 10413776359 := by
        calc
          (79 : ZMod 16062686641) ^ 35854211 = (79 : ZMod 16062686641) ^ (17927105 + 17927105 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 17927105 * (79 : ZMod 16062686641) ^ 17927105) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 10413776359 := by rw [factor_3_24]; decide
      have factor_3_26 : (79 : ZMod 16062686641) ^ 71708422 = 10008799277 := by
        calc
          (79 : ZMod 16062686641) ^ 71708422 = (79 : ZMod 16062686641) ^ (35854211 + 35854211) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 35854211 * (79 : ZMod 16062686641) ^ 35854211 := by rw [pow_add]
          _ = 10008799277 := by rw [factor_3_25]; decide
      have factor_3_27 : (79 : ZMod 16062686641) ^ 143416845 = 7082551854 := by
        calc
          (79 : ZMod 16062686641) ^ 143416845 = (79 : ZMod 16062686641) ^ (71708422 + 71708422 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 71708422 * (79 : ZMod 16062686641) ^ 71708422) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 7082551854 := by rw [factor_3_26]; decide
      have factor_3_28 : (79 : ZMod 16062686641) ^ 286833690 = 15543579148 := by
        calc
          (79 : ZMod 16062686641) ^ 286833690 = (79 : ZMod 16062686641) ^ (143416845 + 143416845) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 143416845 * (79 : ZMod 16062686641) ^ 143416845 := by rw [pow_add]
          _ = 15543579148 := by rw [factor_3_27]; decide
      have factor_3_29 : (79 : ZMod 16062686641) ^ 573667380 = 10891843621 := by
        calc
          (79 : ZMod 16062686641) ^ 573667380 = (79 : ZMod 16062686641) ^ (286833690 + 286833690) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 286833690 * (79 : ZMod 16062686641) ^ 286833690 := by rw [pow_add]
          _ = 10891843621 := by rw [factor_3_28]; decide
      have factor_3_30 : (79 : ZMod 16062686641) ^ 1147334760 = 5278625385 := by
        calc
          (79 : ZMod 16062686641) ^ 1147334760 = (79 : ZMod 16062686641) ^ (573667380 + 573667380) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 573667380 * (79 : ZMod 16062686641) ^ 573667380 := by rw [pow_add]
          _ = 5278625385 := by rw [factor_3_29]; decide
      have factor_3_31 : (79 : ZMod 16062686641) ^ 2294669520 = 11806047827 := by
        calc
          (79 : ZMod 16062686641) ^ 2294669520 = (79 : ZMod 16062686641) ^ (1147334760 + 1147334760) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 1147334760 * (79 : ZMod 16062686641) ^ 1147334760 := by rw [pow_add]
          _ = 11806047827 := by rw [factor_3_30]; decide
      change (79 : ZMod 16062686641) ^ 2294669520 ≠ 1
      rw [factor_3_31]
      decide
    ·
      have factor_4_0 : (79 : ZMod 16062686641) ^ 1 = 79 := by norm_num
      have factor_4_1 : (79 : ZMod 16062686641) ^ 2 = 6241 := by
        calc
          (79 : ZMod 16062686641) ^ 2 = (79 : ZMod 16062686641) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 1 * (79 : ZMod 16062686641) ^ 1 := by rw [pow_add]
          _ = 6241 := by rw [factor_4_0]; decide
      have factor_4_2 : (79 : ZMod 16062686641) ^ 5 = 3077056399 := by
        calc
          (79 : ZMod 16062686641) ^ 5 = (79 : ZMod 16062686641) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 2 * (79 : ZMod 16062686641) ^ 2) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 3077056399 := by rw [factor_4_1]; decide
      have factor_4_3 : (79 : ZMod 16062686641) ^ 10 = 8569417632 := by
        calc
          (79 : ZMod 16062686641) ^ 10 = (79 : ZMod 16062686641) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 5 * (79 : ZMod 16062686641) ^ 5 := by rw [pow_add]
          _ = 8569417632 := by rw [factor_4_2]; decide
      have factor_4_4 : (79 : ZMod 16062686641) ^ 21 = 11557794251 := by
        calc
          (79 : ZMod 16062686641) ^ 21 = (79 : ZMod 16062686641) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 10 * (79 : ZMod 16062686641) ^ 10) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 11557794251 := by rw [factor_4_3]; decide
      have factor_4_5 : (79 : ZMod 16062686641) ^ 43 = 15431463165 := by
        calc
          (79 : ZMod 16062686641) ^ 43 = (79 : ZMod 16062686641) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 21 * (79 : ZMod 16062686641) ^ 21) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 15431463165 := by rw [factor_4_4]; decide
      have factor_4_6 : (79 : ZMod 16062686641) ^ 87 = 7453442017 := by
        calc
          (79 : ZMod 16062686641) ^ 87 = (79 : ZMod 16062686641) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 43 * (79 : ZMod 16062686641) ^ 43) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 7453442017 := by rw [factor_4_5]; decide
      have factor_4_7 : (79 : ZMod 16062686641) ^ 174 = 9307800033 := by
        calc
          (79 : ZMod 16062686641) ^ 174 = (79 : ZMod 16062686641) ^ (87 + 87) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 87 * (79 : ZMod 16062686641) ^ 87 := by rw [pow_add]
          _ = 9307800033 := by rw [factor_4_6]; decide
      have factor_4_8 : (79 : ZMod 16062686641) ^ 348 = 1234724597 := by
        calc
          (79 : ZMod 16062686641) ^ 348 = (79 : ZMod 16062686641) ^ (174 + 174) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 174 * (79 : ZMod 16062686641) ^ 174 := by rw [pow_add]
          _ = 1234724597 := by rw [factor_4_7]; decide
      have factor_4_9 : (79 : ZMod 16062686641) ^ 696 = 15867698696 := by
        calc
          (79 : ZMod 16062686641) ^ 696 = (79 : ZMod 16062686641) ^ (348 + 348) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 348 * (79 : ZMod 16062686641) ^ 348 := by rw [pow_add]
          _ = 15867698696 := by rw [factor_4_8]; decide
      have factor_4_10 : (79 : ZMod 16062686641) ^ 1392 = 15792195871 := by
        calc
          (79 : ZMod 16062686641) ^ 1392 = (79 : ZMod 16062686641) ^ (696 + 696) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 696 * (79 : ZMod 16062686641) ^ 696 := by rw [pow_add]
          _ = 15792195871 := by rw [factor_4_9]; decide
      have factor_4_11 : (79 : ZMod 16062686641) ^ 2785 = 62531962 := by
        calc
          (79 : ZMod 16062686641) ^ 2785 = (79 : ZMod 16062686641) ^ (1392 + 1392 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 1392 * (79 : ZMod 16062686641) ^ 1392) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 62531962 := by rw [factor_4_10]; decide
      have factor_4_12 : (79 : ZMod 16062686641) ^ 5570 = 10086430968 := by
        calc
          (79 : ZMod 16062686641) ^ 5570 = (79 : ZMod 16062686641) ^ (2785 + 2785) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 2785 * (79 : ZMod 16062686641) ^ 2785 := by rw [pow_add]
          _ = 10086430968 := by rw [factor_4_11]; decide
      have factor_4_13 : (79 : ZMod 16062686641) ^ 11140 = 2480639402 := by
        calc
          (79 : ZMod 16062686641) ^ 11140 = (79 : ZMod 16062686641) ^ (5570 + 5570) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 5570 * (79 : ZMod 16062686641) ^ 5570 := by rw [pow_add]
          _ = 2480639402 := by rw [factor_4_12]; decide
      have factor_4_14 : (79 : ZMod 16062686641) ^ 22281 = 7910070934 := by
        calc
          (79 : ZMod 16062686641) ^ 22281 = (79 : ZMod 16062686641) ^ (11140 + 11140 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 11140 * (79 : ZMod 16062686641) ^ 11140) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 7910070934 := by rw [factor_4_13]; decide
      have factor_4_15 : (79 : ZMod 16062686641) ^ 44563 = 12605647919 := by
        calc
          (79 : ZMod 16062686641) ^ 44563 = (79 : ZMod 16062686641) ^ (22281 + 22281 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 22281 * (79 : ZMod 16062686641) ^ 22281) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 12605647919 := by rw [factor_4_14]; decide
      have factor_4_16 : (79 : ZMod 16062686641) ^ 89126 = 15638510175 := by
        calc
          (79 : ZMod 16062686641) ^ 89126 = (79 : ZMod 16062686641) ^ (44563 + 44563) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 44563 * (79 : ZMod 16062686641) ^ 44563 := by rw [pow_add]
          _ = 15638510175 := by rw [factor_4_15]; decide
      have factor_4_17 : (79 : ZMod 16062686641) ^ 178252 = 3905060168 := by
        calc
          (79 : ZMod 16062686641) ^ 178252 = (79 : ZMod 16062686641) ^ (89126 + 89126) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 89126 * (79 : ZMod 16062686641) ^ 89126 := by rw [pow_add]
          _ = 3905060168 := by rw [factor_4_16]; decide
      have factor_4_18 : (79 : ZMod 16062686641) ^ 356504 = 987464118 := by
        calc
          (79 : ZMod 16062686641) ^ 356504 = (79 : ZMod 16062686641) ^ (178252 + 178252) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 178252 * (79 : ZMod 16062686641) ^ 178252 := by rw [pow_add]
          _ = 987464118 := by rw [factor_4_17]; decide
      have factor_4_19 : (79 : ZMod 16062686641) ^ 713009 = 10423573277 := by
        calc
          (79 : ZMod 16062686641) ^ 713009 = (79 : ZMod 16062686641) ^ (356504 + 356504 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 356504 * (79 : ZMod 16062686641) ^ 356504) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 10423573277 := by rw [factor_4_18]; decide
      have factor_4_20 : (79 : ZMod 16062686641) ^ 1426019 = 8828833992 := by
        calc
          (79 : ZMod 16062686641) ^ 1426019 = (79 : ZMod 16062686641) ^ (713009 + 713009 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 713009 * (79 : ZMod 16062686641) ^ 713009) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 8828833992 := by rw [factor_4_19]; decide
      have factor_4_21 : (79 : ZMod 16062686641) ^ 2852039 = 9657073865 := by
        calc
          (79 : ZMod 16062686641) ^ 2852039 = (79 : ZMod 16062686641) ^ (1426019 + 1426019 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 1426019 * (79 : ZMod 16062686641) ^ 1426019) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 9657073865 := by rw [factor_4_20]; decide
      have factor_4_22 : (79 : ZMod 16062686641) ^ 5704079 = 9730540831 := by
        calc
          (79 : ZMod 16062686641) ^ 5704079 = (79 : ZMod 16062686641) ^ (2852039 + 2852039 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 2852039 * (79 : ZMod 16062686641) ^ 2852039) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 9730540831 := by rw [factor_4_21]; decide
      have factor_4_23 : (79 : ZMod 16062686641) ^ 11408158 = 11404702726 := by
        calc
          (79 : ZMod 16062686641) ^ 11408158 = (79 : ZMod 16062686641) ^ (5704079 + 5704079) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 5704079 * (79 : ZMod 16062686641) ^ 5704079 := by rw [pow_add]
          _ = 11404702726 := by rw [factor_4_22]; decide
      have factor_4_24 : (79 : ZMod 16062686641) ^ 22816316 = 9064347859 := by
        calc
          (79 : ZMod 16062686641) ^ 22816316 = (79 : ZMod 16062686641) ^ (11408158 + 11408158) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 11408158 * (79 : ZMod 16062686641) ^ 11408158 := by rw [pow_add]
          _ = 9064347859 := by rw [factor_4_23]; decide
      have factor_4_25 : (79 : ZMod 16062686641) ^ 45632632 = 15918376075 := by
        calc
          (79 : ZMod 16062686641) ^ 45632632 = (79 : ZMod 16062686641) ^ (22816316 + 22816316) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 22816316 * (79 : ZMod 16062686641) ^ 22816316 := by rw [pow_add]
          _ = 15918376075 := by rw [factor_4_24]; decide
      have factor_4_26 : (79 : ZMod 16062686641) ^ 91265265 = 6048711555 := by
        calc
          (79 : ZMod 16062686641) ^ 91265265 = (79 : ZMod 16062686641) ^ (45632632 + 45632632 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 45632632 * (79 : ZMod 16062686641) ^ 45632632) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 6048711555 := by rw [factor_4_25]; decide
      have factor_4_27 : (79 : ZMod 16062686641) ^ 182530530 = 3514870920 := by
        calc
          (79 : ZMod 16062686641) ^ 182530530 = (79 : ZMod 16062686641) ^ (91265265 + 91265265) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 91265265 * (79 : ZMod 16062686641) ^ 91265265 := by rw [pow_add]
          _ = 3514870920 := by rw [factor_4_26]; decide
      have factor_4_28 : (79 : ZMod 16062686641) ^ 365061060 = 4734880463 := by
        calc
          (79 : ZMod 16062686641) ^ 365061060 = (79 : ZMod 16062686641) ^ (182530530 + 182530530) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 182530530 * (79 : ZMod 16062686641) ^ 182530530 := by rw [pow_add]
          _ = 4734880463 := by rw [factor_4_27]; decide
      have factor_4_29 : (79 : ZMod 16062686641) ^ 730122120 = 8143102189 := by
        calc
          (79 : ZMod 16062686641) ^ 730122120 = (79 : ZMod 16062686641) ^ (365061060 + 365061060) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 365061060 * (79 : ZMod 16062686641) ^ 365061060 := by rw [pow_add]
          _ = 8143102189 := by rw [factor_4_28]; decide
      have factor_4_30 : (79 : ZMod 16062686641) ^ 1460244240 = 731733211 := by
        calc
          (79 : ZMod 16062686641) ^ 1460244240 = (79 : ZMod 16062686641) ^ (730122120 + 730122120) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 730122120 * (79 : ZMod 16062686641) ^ 730122120 := by rw [pow_add]
          _ = 731733211 := by rw [factor_4_29]; decide
      change (79 : ZMod 16062686641) ^ 1460244240 ≠ 1
      rw [factor_4_30]
      decide
    ·
      have factor_5_0 : (79 : ZMod 16062686641) ^ 1 = 79 := by norm_num
      have factor_5_1 : (79 : ZMod 16062686641) ^ 2 = 6241 := by
        calc
          (79 : ZMod 16062686641) ^ 2 = (79 : ZMod 16062686641) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 1 * (79 : ZMod 16062686641) ^ 1 := by rw [pow_add]
          _ = 6241 := by rw [factor_5_0]; decide
      have factor_5_2 : (79 : ZMod 16062686641) ^ 4 = 38950081 := by
        calc
          (79 : ZMod 16062686641) ^ 4 = (79 : ZMod 16062686641) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 2 * (79 : ZMod 16062686641) ^ 2 := by rw [pow_add]
          _ = 38950081 := by rw [factor_5_1]; decide
      have factor_5_3 : (79 : ZMod 16062686641) ^ 9 = 4174976588 := by
        calc
          (79 : ZMod 16062686641) ^ 9 = (79 : ZMod 16062686641) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 4 * (79 : ZMod 16062686641) ^ 4) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 4174976588 := by rw [factor_5_2]; decide
      have factor_5_4 : (79 : ZMod 16062686641) ^ 18 = 9995306547 := by
        calc
          (79 : ZMod 16062686641) ^ 18 = (79 : ZMod 16062686641) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 9 * (79 : ZMod 16062686641) ^ 9 := by rw [pow_add]
          _ = 9995306547 := by rw [factor_5_3]; decide
      have factor_5_5 : (79 : ZMod 16062686641) ^ 36 = 7334158364 := by
        calc
          (79 : ZMod 16062686641) ^ 36 = (79 : ZMod 16062686641) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 18 * (79 : ZMod 16062686641) ^ 18 := by rw [pow_add]
          _ = 7334158364 := by rw [factor_5_4]; decide
      have factor_5_6 : (79 : ZMod 16062686641) ^ 73 = 6739154174 := by
        calc
          (79 : ZMod 16062686641) ^ 73 = (79 : ZMod 16062686641) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 36 * (79 : ZMod 16062686641) ^ 36) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 6739154174 := by rw [factor_5_5]; decide
      have factor_5_7 : (79 : ZMod 16062686641) ^ 147 = 8533362834 := by
        calc
          (79 : ZMod 16062686641) ^ 147 = (79 : ZMod 16062686641) ^ (73 + 73 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 73 * (79 : ZMod 16062686641) ^ 73) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 8533362834 := by rw [factor_5_6]; decide
      have factor_5_8 : (79 : ZMod 16062686641) ^ 294 = 2396441740 := by
        calc
          (79 : ZMod 16062686641) ^ 294 = (79 : ZMod 16062686641) ^ (147 + 147) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 147 * (79 : ZMod 16062686641) ^ 147 := by rw [pow_add]
          _ = 2396441740 := by rw [factor_5_7]; decide
      have factor_5_9 : (79 : ZMod 16062686641) ^ 589 = 10882769553 := by
        calc
          (79 : ZMod 16062686641) ^ 589 = (79 : ZMod 16062686641) ^ (294 + 294 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 294 * (79 : ZMod 16062686641) ^ 294) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 10882769553 := by rw [factor_5_8]; decide
      have factor_5_10 : (79 : ZMod 16062686641) ^ 1178 = 14190205660 := by
        calc
          (79 : ZMod 16062686641) ^ 1178 = (79 : ZMod 16062686641) ^ (589 + 589) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 589 * (79 : ZMod 16062686641) ^ 589 := by rw [pow_add]
          _ = 14190205660 := by rw [factor_5_9]; decide
      have factor_5_11 : (79 : ZMod 16062686641) ^ 2356 = 3206157165 := by
        calc
          (79 : ZMod 16062686641) ^ 2356 = (79 : ZMod 16062686641) ^ (1178 + 1178) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 1178 * (79 : ZMod 16062686641) ^ 1178 := by rw [pow_add]
          _ = 3206157165 := by rw [factor_5_10]; decide
      have factor_5_12 : (79 : ZMod 16062686641) ^ 4713 = 5065539463 := by
        calc
          (79 : ZMod 16062686641) ^ 4713 = (79 : ZMod 16062686641) ^ (2356 + 2356 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 2356 * (79 : ZMod 16062686641) ^ 2356) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 5065539463 := by rw [factor_5_11]; decide
      have factor_5_13 : (79 : ZMod 16062686641) ^ 9426 = 1650726340 := by
        calc
          (79 : ZMod 16062686641) ^ 9426 = (79 : ZMod 16062686641) ^ (4713 + 4713) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 4713 * (79 : ZMod 16062686641) ^ 4713 := by rw [pow_add]
          _ = 1650726340 := by rw [factor_5_12]; decide
      have factor_5_14 : (79 : ZMod 16062686641) ^ 18853 = 11702152106 := by
        calc
          (79 : ZMod 16062686641) ^ 18853 = (79 : ZMod 16062686641) ^ (9426 + 9426 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 9426 * (79 : ZMod 16062686641) ^ 9426) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 11702152106 := by rw [factor_5_13]; decide
      have factor_5_15 : (79 : ZMod 16062686641) ^ 37707 = 5792286006 := by
        calc
          (79 : ZMod 16062686641) ^ 37707 = (79 : ZMod 16062686641) ^ (18853 + 18853 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 18853 * (79 : ZMod 16062686641) ^ 18853) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 5792286006 := by rw [factor_5_14]; decide
      have factor_5_16 : (79 : ZMod 16062686641) ^ 75414 = 1092454180 := by
        calc
          (79 : ZMod 16062686641) ^ 75414 = (79 : ZMod 16062686641) ^ (37707 + 37707) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 37707 * (79 : ZMod 16062686641) ^ 37707 := by rw [pow_add]
          _ = 1092454180 := by rw [factor_5_15]; decide
      have factor_5_17 : (79 : ZMod 16062686641) ^ 150829 = 803545849 := by
        calc
          (79 : ZMod 16062686641) ^ 150829 = (79 : ZMod 16062686641) ^ (75414 + 75414 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 75414 * (79 : ZMod 16062686641) ^ 75414) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 803545849 := by rw [factor_5_16]; decide
      have factor_5_18 : (79 : ZMod 16062686641) ^ 301658 = 13497983003 := by
        calc
          (79 : ZMod 16062686641) ^ 301658 = (79 : ZMod 16062686641) ^ (150829 + 150829) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 150829 * (79 : ZMod 16062686641) ^ 150829 := by rw [pow_add]
          _ = 13497983003 := by rw [factor_5_17]; decide
      have factor_5_19 : (79 : ZMod 16062686641) ^ 603316 = 4379283612 := by
        calc
          (79 : ZMod 16062686641) ^ 603316 = (79 : ZMod 16062686641) ^ (301658 + 301658) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 301658 * (79 : ZMod 16062686641) ^ 301658 := by rw [pow_add]
          _ = 4379283612 := by rw [factor_5_18]; decide
      have factor_5_20 : (79 : ZMod 16062686641) ^ 1206632 = 6190044749 := by
        calc
          (79 : ZMod 16062686641) ^ 1206632 = (79 : ZMod 16062686641) ^ (603316 + 603316) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 603316 * (79 : ZMod 16062686641) ^ 603316 := by rw [pow_add]
          _ = 6190044749 := by rw [factor_5_19]; decide
      have factor_5_21 : (79 : ZMod 16062686641) ^ 2413264 = 2300145537 := by
        calc
          (79 : ZMod 16062686641) ^ 2413264 = (79 : ZMod 16062686641) ^ (1206632 + 1206632) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 1206632 * (79 : ZMod 16062686641) ^ 1206632 := by rw [pow_add]
          _ = 2300145537 := by rw [factor_5_20]; decide
      have factor_5_22 : (79 : ZMod 16062686641) ^ 4826528 = 8870198635 := by
        calc
          (79 : ZMod 16062686641) ^ 4826528 = (79 : ZMod 16062686641) ^ (2413264 + 2413264) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 2413264 * (79 : ZMod 16062686641) ^ 2413264 := by rw [pow_add]
          _ = 8870198635 := by rw [factor_5_21]; decide
      have factor_5_23 : (79 : ZMod 16062686641) ^ 9653056 = 10483260718 := by
        calc
          (79 : ZMod 16062686641) ^ 9653056 = (79 : ZMod 16062686641) ^ (4826528 + 4826528) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 4826528 * (79 : ZMod 16062686641) ^ 4826528 := by rw [pow_add]
          _ = 10483260718 := by rw [factor_5_22]; decide
      have factor_5_24 : (79 : ZMod 16062686641) ^ 19306113 = 7789429882 := by
        calc
          (79 : ZMod 16062686641) ^ 19306113 = (79 : ZMod 16062686641) ^ (9653056 + 9653056 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 9653056 * (79 : ZMod 16062686641) ^ 9653056) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 7789429882 := by rw [factor_5_23]; decide
      have factor_5_25 : (79 : ZMod 16062686641) ^ 38612227 = 197382426 := by
        calc
          (79 : ZMod 16062686641) ^ 38612227 = (79 : ZMod 16062686641) ^ (19306113 + 19306113 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 19306113 * (79 : ZMod 16062686641) ^ 19306113) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 197382426 := by rw [factor_5_24]; decide
      have factor_5_26 : (79 : ZMod 16062686641) ^ 77224455 = 9232149768 := by
        calc
          (79 : ZMod 16062686641) ^ 77224455 = (79 : ZMod 16062686641) ^ (38612227 + 38612227 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 38612227 * (79 : ZMod 16062686641) ^ 38612227) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 9232149768 := by rw [factor_5_25]; decide
      have factor_5_27 : (79 : ZMod 16062686641) ^ 154448910 = 522663937 := by
        calc
          (79 : ZMod 16062686641) ^ 154448910 = (79 : ZMod 16062686641) ^ (77224455 + 77224455) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 77224455 * (79 : ZMod 16062686641) ^ 77224455 := by rw [pow_add]
          _ = 522663937 := by rw [factor_5_26]; decide
      have factor_5_28 : (79 : ZMod 16062686641) ^ 308897820 = 9405512122 := by
        calc
          (79 : ZMod 16062686641) ^ 308897820 = (79 : ZMod 16062686641) ^ (154448910 + 154448910) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 154448910 * (79 : ZMod 16062686641) ^ 154448910 := by rw [pow_add]
          _ = 9405512122 := by rw [factor_5_27]; decide
      have factor_5_29 : (79 : ZMod 16062686641) ^ 617795640 = 8737998092 := by
        calc
          (79 : ZMod 16062686641) ^ 617795640 = (79 : ZMod 16062686641) ^ (308897820 + 308897820) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 308897820 * (79 : ZMod 16062686641) ^ 308897820 := by rw [pow_add]
          _ = 8737998092 := by rw [factor_5_28]; decide
      have factor_5_30 : (79 : ZMod 16062686641) ^ 1235591280 = 15599484174 := by
        calc
          (79 : ZMod 16062686641) ^ 1235591280 = (79 : ZMod 16062686641) ^ (617795640 + 617795640) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 617795640 * (79 : ZMod 16062686641) ^ 617795640 := by rw [pow_add]
          _ = 15599484174 := by rw [factor_5_29]; decide
      change (79 : ZMod 16062686641) ^ 1235591280 ≠ 1
      rw [factor_5_30]
      decide
    ·
      have factor_6_0 : (79 : ZMod 16062686641) ^ 1 = 79 := by norm_num
      have factor_6_1 : (79 : ZMod 16062686641) ^ 3 = 493039 := by
        calc
          (79 : ZMod 16062686641) ^ 3 = (79 : ZMod 16062686641) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 1 * (79 : ZMod 16062686641) ^ 1) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 493039 := by rw [factor_6_0]; decide
      have factor_6_2 : (79 : ZMod 16062686641) ^ 7 = 8998450164 := by
        calc
          (79 : ZMod 16062686641) ^ 7 = (79 : ZMod 16062686641) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 3 * (79 : ZMod 16062686641) ^ 3) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 8998450164 := by rw [factor_6_1]; decide
      have factor_6_3 : (79 : ZMod 16062686641) ^ 14 = 14713143187 := by
        calc
          (79 : ZMod 16062686641) ^ 14 = (79 : ZMod 16062686641) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 7 * (79 : ZMod 16062686641) ^ 7 := by rw [pow_add]
          _ = 14713143187 := by rw [factor_6_2]; decide
      have factor_6_4 : (79 : ZMod 16062686641) ^ 28 = 2196704808 := by
        calc
          (79 : ZMod 16062686641) ^ 28 = (79 : ZMod 16062686641) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 14 * (79 : ZMod 16062686641) ^ 14 := by rw [pow_add]
          _ = 2196704808 := by rw [factor_6_3]; decide
      have factor_6_5 : (79 : ZMod 16062686641) ^ 56 = 10144565774 := by
        calc
          (79 : ZMod 16062686641) ^ 56 = (79 : ZMod 16062686641) ^ (28 + 28) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 28 * (79 : ZMod 16062686641) ^ 28 := by rw [pow_add]
          _ = 10144565774 := by rw [factor_6_4]; decide
      have factor_6_6 : (79 : ZMod 16062686641) ^ 112 = 10295918991 := by
        calc
          (79 : ZMod 16062686641) ^ 112 = (79 : ZMod 16062686641) ^ (56 + 56) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 56 * (79 : ZMod 16062686641) ^ 56 := by rw [pow_add]
          _ = 10295918991 := by rw [factor_6_5]; decide
      have factor_6_7 : (79 : ZMod 16062686641) ^ 225 = 8796629878 := by
        calc
          (79 : ZMod 16062686641) ^ 225 = (79 : ZMod 16062686641) ^ (112 + 112 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 112 * (79 : ZMod 16062686641) ^ 112) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 8796629878 := by rw [factor_6_6]; decide
      have factor_6_8 : (79 : ZMod 16062686641) ^ 450 = 14122691149 := by
        calc
          (79 : ZMod 16062686641) ^ 450 = (79 : ZMod 16062686641) ^ (225 + 225) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 225 * (79 : ZMod 16062686641) ^ 225 := by rw [pow_add]
          _ = 14122691149 := by rw [factor_6_7]; decide
      have factor_6_9 : (79 : ZMod 16062686641) ^ 901 = 8421592322 := by
        calc
          (79 : ZMod 16062686641) ^ 901 = (79 : ZMod 16062686641) ^ (450 + 450 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 450 * (79 : ZMod 16062686641) ^ 450) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 8421592322 := by rw [factor_6_8]; decide
      have factor_6_10 : (79 : ZMod 16062686641) ^ 1802 = 11754527297 := by
        calc
          (79 : ZMod 16062686641) ^ 1802 = (79 : ZMod 16062686641) ^ (901 + 901) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 901 * (79 : ZMod 16062686641) ^ 901 := by rw [pow_add]
          _ = 11754527297 := by rw [factor_6_9]; decide
      have factor_6_11 : (79 : ZMod 16062686641) ^ 3604 = 10351261431 := by
        calc
          (79 : ZMod 16062686641) ^ 3604 = (79 : ZMod 16062686641) ^ (1802 + 1802) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 1802 * (79 : ZMod 16062686641) ^ 1802 := by rw [pow_add]
          _ = 10351261431 := by rw [factor_6_10]; decide
      have factor_6_12 : (79 : ZMod 16062686641) ^ 7208 = 14010828409 := by
        calc
          (79 : ZMod 16062686641) ^ 7208 = (79 : ZMod 16062686641) ^ (3604 + 3604) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 3604 * (79 : ZMod 16062686641) ^ 3604 := by rw [pow_add]
          _ = 14010828409 := by rw [factor_6_11]; decide
      have factor_6_13 : (79 : ZMod 16062686641) ^ 14417 = 6751778164 := by
        calc
          (79 : ZMod 16062686641) ^ 14417 = (79 : ZMod 16062686641) ^ (7208 + 7208 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 7208 * (79 : ZMod 16062686641) ^ 7208) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 6751778164 := by rw [factor_6_12]; decide
      have factor_6_14 : (79 : ZMod 16062686641) ^ 28834 = 4757182193 := by
        calc
          (79 : ZMod 16062686641) ^ 28834 = (79 : ZMod 16062686641) ^ (14417 + 14417) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 14417 * (79 : ZMod 16062686641) ^ 14417 := by rw [pow_add]
          _ = 4757182193 := by rw [factor_6_13]; decide
      have factor_6_15 : (79 : ZMod 16062686641) ^ 57669 = 14710229796 := by
        calc
          (79 : ZMod 16062686641) ^ 57669 = (79 : ZMod 16062686641) ^ (28834 + 28834 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 28834 * (79 : ZMod 16062686641) ^ 28834) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 14710229796 := by rw [factor_6_14]; decide
      have factor_6_16 : (79 : ZMod 16062686641) ^ 115339 = 11334452162 := by
        calc
          (79 : ZMod 16062686641) ^ 115339 = (79 : ZMod 16062686641) ^ (57669 + 57669 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 57669 * (79 : ZMod 16062686641) ^ 57669) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 11334452162 := by rw [factor_6_15]; decide
      have factor_6_17 : (79 : ZMod 16062686641) ^ 230679 = 1442030006 := by
        calc
          (79 : ZMod 16062686641) ^ 230679 = (79 : ZMod 16062686641) ^ (115339 + 115339 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 115339 * (79 : ZMod 16062686641) ^ 115339) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 1442030006 := by rw [factor_6_16]; decide
      have factor_6_18 : (79 : ZMod 16062686641) ^ 461359 = 4137789502 := by
        calc
          (79 : ZMod 16062686641) ^ 461359 = (79 : ZMod 16062686641) ^ (230679 + 230679 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 230679 * (79 : ZMod 16062686641) ^ 230679) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 4137789502 := by rw [factor_6_17]; decide
      have factor_6_19 : (79 : ZMod 16062686641) ^ 922718 = 7365389318 := by
        calc
          (79 : ZMod 16062686641) ^ 922718 = (79 : ZMod 16062686641) ^ (461359 + 461359) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 461359 * (79 : ZMod 16062686641) ^ 461359 := by rw [pow_add]
          _ = 7365389318 := by rw [factor_6_18]; decide
      have factor_6_20 : (79 : ZMod 16062686641) ^ 1845437 = 4305484781 := by
        calc
          (79 : ZMod 16062686641) ^ 1845437 = (79 : ZMod 16062686641) ^ (922718 + 922718 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 922718 * (79 : ZMod 16062686641) ^ 922718) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 4305484781 := by rw [factor_6_19]; decide
      have factor_6_21 : (79 : ZMod 16062686641) ^ 3690874 = 8104670255 := by
        calc
          (79 : ZMod 16062686641) ^ 3690874 = (79 : ZMod 16062686641) ^ (1845437 + 1845437) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 1845437 * (79 : ZMod 16062686641) ^ 1845437 := by rw [pow_add]
          _ = 8104670255 := by rw [factor_6_20]; decide
      have factor_6_22 : (79 : ZMod 16062686641) ^ 7381749 = 15411244014 := by
        calc
          (79 : ZMod 16062686641) ^ 7381749 = (79 : ZMod 16062686641) ^ (3690874 + 3690874 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 3690874 * (79 : ZMod 16062686641) ^ 3690874) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 15411244014 := by rw [factor_6_21]; decide
      have factor_6_23 : (79 : ZMod 16062686641) ^ 14763498 = 14139823208 := by
        calc
          (79 : ZMod 16062686641) ^ 14763498 = (79 : ZMod 16062686641) ^ (7381749 + 7381749) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 7381749 * (79 : ZMod 16062686641) ^ 7381749 := by rw [pow_add]
          _ = 14139823208 := by rw [factor_6_22]; decide
      have factor_6_24 : (79 : ZMod 16062686641) ^ 29526997 = 11636925070 := by
        calc
          (79 : ZMod 16062686641) ^ 29526997 = (79 : ZMod 16062686641) ^ (14763498 + 14763498 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 14763498 * (79 : ZMod 16062686641) ^ 14763498) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 11636925070 := by rw [factor_6_23]; decide
      have factor_6_25 : (79 : ZMod 16062686641) ^ 59053995 = 8500278034 := by
        calc
          (79 : ZMod 16062686641) ^ 59053995 = (79 : ZMod 16062686641) ^ (29526997 + 29526997 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 29526997 * (79 : ZMod 16062686641) ^ 29526997) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 8500278034 := by rw [factor_6_24]; decide
      have factor_6_26 : (79 : ZMod 16062686641) ^ 118107990 = 7251074604 := by
        calc
          (79 : ZMod 16062686641) ^ 118107990 = (79 : ZMod 16062686641) ^ (59053995 + 59053995) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 59053995 * (79 : ZMod 16062686641) ^ 59053995 := by rw [pow_add]
          _ = 7251074604 := by rw [factor_6_25]; decide
      have factor_6_27 : (79 : ZMod 16062686641) ^ 236215980 = 8734308448 := by
        calc
          (79 : ZMod 16062686641) ^ 236215980 = (79 : ZMod 16062686641) ^ (118107990 + 118107990) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 118107990 * (79 : ZMod 16062686641) ^ 118107990 := by rw [pow_add]
          _ = 8734308448 := by rw [factor_6_26]; decide
      have factor_6_28 : (79 : ZMod 16062686641) ^ 472431960 = 5492407531 := by
        calc
          (79 : ZMod 16062686641) ^ 472431960 = (79 : ZMod 16062686641) ^ (236215980 + 236215980) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 236215980 * (79 : ZMod 16062686641) ^ 236215980 := by rw [pow_add]
          _ = 5492407531 := by rw [factor_6_27]; decide
      have factor_6_29 : (79 : ZMod 16062686641) ^ 944863920 = 2255411544 := by
        calc
          (79 : ZMod 16062686641) ^ 944863920 = (79 : ZMod 16062686641) ^ (472431960 + 472431960) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 472431960 * (79 : ZMod 16062686641) ^ 472431960 := by rw [pow_add]
          _ = 2255411544 := by rw [factor_6_28]; decide
      change (79 : ZMod 16062686641) ^ 944863920 ≠ 1
      rw [factor_6_29]
      decide
    ·
      have factor_7_0 : (79 : ZMod 16062686641) ^ 1 = 79 := by norm_num
      have factor_7_1 : (79 : ZMod 16062686641) ^ 3 = 493039 := by
        calc
          (79 : ZMod 16062686641) ^ 3 = (79 : ZMod 16062686641) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 1 * (79 : ZMod 16062686641) ^ 1) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 493039 := by rw [factor_7_0]; decide
      have factor_7_2 : (79 : ZMod 16062686641) ^ 6 = 2147155906 := by
        calc
          (79 : ZMod 16062686641) ^ 6 = (79 : ZMod 16062686641) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 3 * (79 : ZMod 16062686641) ^ 3 := by rw [pow_add]
          _ = 2147155906 := by rw [factor_7_1]; decide
      have factor_7_3 : (79 : ZMod 16062686641) ^ 12 = 9051613423 := by
        calc
          (79 : ZMod 16062686641) ^ 12 = (79 : ZMod 16062686641) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 6 * (79 : ZMod 16062686641) ^ 6 := by rw [pow_add]
          _ = 9051613423 := by rw [factor_7_2]; decide
      have factor_7_4 : (79 : ZMod 16062686641) ^ 25 = 6221278312 := by
        calc
          (79 : ZMod 16062686641) ^ 25 = (79 : ZMod 16062686641) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 12 * (79 : ZMod 16062686641) ^ 12) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 6221278312 := by rw [factor_7_3]; decide
      have factor_7_5 : (79 : ZMod 16062686641) ^ 50 = 15164783279 := by
        calc
          (79 : ZMod 16062686641) ^ 50 = (79 : ZMod 16062686641) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 25 * (79 : ZMod 16062686641) ^ 25 := by rw [pow_add]
          _ = 15164783279 := by rw [factor_7_4]; decide
      have factor_7_6 : (79 : ZMod 16062686641) ^ 100 = 465477012 := by
        calc
          (79 : ZMod 16062686641) ^ 100 = (79 : ZMod 16062686641) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 50 * (79 : ZMod 16062686641) ^ 50 := by rw [pow_add]
          _ = 465477012 := by rw [factor_7_5]; decide
      have factor_7_7 : (79 : ZMod 16062686641) ^ 201 = 12946466694 := by
        calc
          (79 : ZMod 16062686641) ^ 201 = (79 : ZMod 16062686641) ^ (100 + 100 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 100 * (79 : ZMod 16062686641) ^ 100) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 12946466694 := by rw [factor_7_6]; decide
      have factor_7_8 : (79 : ZMod 16062686641) ^ 403 = 2885118838 := by
        calc
          (79 : ZMod 16062686641) ^ 403 = (79 : ZMod 16062686641) ^ (201 + 201 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 201 * (79 : ZMod 16062686641) ^ 201) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 2885118838 := by rw [factor_7_7]; decide
      have factor_7_9 : (79 : ZMod 16062686641) ^ 806 = 8134632144 := by
        calc
          (79 : ZMod 16062686641) ^ 806 = (79 : ZMod 16062686641) ^ (403 + 403) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 403 * (79 : ZMod 16062686641) ^ 403 := by rw [pow_add]
          _ = 8134632144 := by rw [factor_7_8]; decide
      have factor_7_10 : (79 : ZMod 16062686641) ^ 1612 = 13643063189 := by
        calc
          (79 : ZMod 16062686641) ^ 1612 = (79 : ZMod 16062686641) ^ (806 + 806) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 806 * (79 : ZMod 16062686641) ^ 806 := by rw [pow_add]
          _ = 13643063189 := by rw [factor_7_9]; decide
      have factor_7_11 : (79 : ZMod 16062686641) ^ 3224 = 4917682255 := by
        calc
          (79 : ZMod 16062686641) ^ 3224 = (79 : ZMod 16062686641) ^ (1612 + 1612) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 1612 * (79 : ZMod 16062686641) ^ 1612 := by rw [pow_add]
          _ = 4917682255 := by rw [factor_7_10]; decide
      have factor_7_12 : (79 : ZMod 16062686641) ^ 6449 = 2860371027 := by
        calc
          (79 : ZMod 16062686641) ^ 6449 = (79 : ZMod 16062686641) ^ (3224 + 3224 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 3224 * (79 : ZMod 16062686641) ^ 3224) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 2860371027 := by rw [factor_7_11]; decide
      have factor_7_13 : (79 : ZMod 16062686641) ^ 12899 = 6595226593 := by
        calc
          (79 : ZMod 16062686641) ^ 12899 = (79 : ZMod 16062686641) ^ (6449 + 6449 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 6449 * (79 : ZMod 16062686641) ^ 6449) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 6595226593 := by rw [factor_7_12]; decide
      have factor_7_14 : (79 : ZMod 16062686641) ^ 25799 = 13856620645 := by
        calc
          (79 : ZMod 16062686641) ^ 25799 = (79 : ZMod 16062686641) ^ (12899 + 12899 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 12899 * (79 : ZMod 16062686641) ^ 12899) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 13856620645 := by rw [factor_7_13]; decide
      have factor_7_15 : (79 : ZMod 16062686641) ^ 51599 = 7373187250 := by
        calc
          (79 : ZMod 16062686641) ^ 51599 = (79 : ZMod 16062686641) ^ (25799 + 25799 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 25799 * (79 : ZMod 16062686641) ^ 25799) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 7373187250 := by rw [factor_7_14]; decide
      have factor_7_16 : (79 : ZMod 16062686641) ^ 103198 = 15454540039 := by
        calc
          (79 : ZMod 16062686641) ^ 103198 = (79 : ZMod 16062686641) ^ (51599 + 51599) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 51599 * (79 : ZMod 16062686641) ^ 51599 := by rw [pow_add]
          _ = 15454540039 := by rw [factor_7_15]; decide
      have factor_7_17 : (79 : ZMod 16062686641) ^ 206397 = 9639755781 := by
        calc
          (79 : ZMod 16062686641) ^ 206397 = (79 : ZMod 16062686641) ^ (103198 + 103198 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 103198 * (79 : ZMod 16062686641) ^ 103198) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 9639755781 := by rw [factor_7_16]; decide
      have factor_7_18 : (79 : ZMod 16062686641) ^ 412795 = 4416176267 := by
        calc
          (79 : ZMod 16062686641) ^ 412795 = (79 : ZMod 16062686641) ^ (206397 + 206397 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 206397 * (79 : ZMod 16062686641) ^ 206397) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 4416176267 := by rw [factor_7_17]; decide
      have factor_7_19 : (79 : ZMod 16062686641) ^ 825590 = 14673287990 := by
        calc
          (79 : ZMod 16062686641) ^ 825590 = (79 : ZMod 16062686641) ^ (412795 + 412795) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 412795 * (79 : ZMod 16062686641) ^ 412795 := by rw [pow_add]
          _ = 14673287990 := by rw [factor_7_18]; decide
      have factor_7_20 : (79 : ZMod 16062686641) ^ 1651180 = 8649350312 := by
        calc
          (79 : ZMod 16062686641) ^ 1651180 = (79 : ZMod 16062686641) ^ (825590 + 825590) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 825590 * (79 : ZMod 16062686641) ^ 825590 := by rw [pow_add]
          _ = 8649350312 := by rw [factor_7_19]; decide
      have factor_7_21 : (79 : ZMod 16062686641) ^ 3302361 = 6500180211 := by
        calc
          (79 : ZMod 16062686641) ^ 3302361 = (79 : ZMod 16062686641) ^ (1651180 + 1651180 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 1651180 * (79 : ZMod 16062686641) ^ 1651180) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 6500180211 := by rw [factor_7_20]; decide
      have factor_7_22 : (79 : ZMod 16062686641) ^ 6604723 = 3716195112 := by
        calc
          (79 : ZMod 16062686641) ^ 6604723 = (79 : ZMod 16062686641) ^ (3302361 + 3302361 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 3302361 * (79 : ZMod 16062686641) ^ 3302361) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 3716195112 := by rw [factor_7_21]; decide
      have factor_7_23 : (79 : ZMod 16062686641) ^ 13209446 = 14398240112 := by
        calc
          (79 : ZMod 16062686641) ^ 13209446 = (79 : ZMod 16062686641) ^ (6604723 + 6604723) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 6604723 * (79 : ZMod 16062686641) ^ 6604723 := by rw [pow_add]
          _ = 14398240112 := by rw [factor_7_22]; decide
      have factor_7_24 : (79 : ZMod 16062686641) ^ 26418892 = 5150525486 := by
        calc
          (79 : ZMod 16062686641) ^ 26418892 = (79 : ZMod 16062686641) ^ (13209446 + 13209446) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 13209446 * (79 : ZMod 16062686641) ^ 13209446 := by rw [pow_add]
          _ = 5150525486 := by rw [factor_7_23]; decide
      have factor_7_25 : (79 : ZMod 16062686641) ^ 52837785 = 8399060059 := by
        calc
          (79 : ZMod 16062686641) ^ 52837785 = (79 : ZMod 16062686641) ^ (26418892 + 26418892 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 26418892 * (79 : ZMod 16062686641) ^ 26418892) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 8399060059 := by rw [factor_7_24]; decide
      have factor_7_26 : (79 : ZMod 16062686641) ^ 105675570 = 12052274209 := by
        calc
          (79 : ZMod 16062686641) ^ 105675570 = (79 : ZMod 16062686641) ^ (52837785 + 52837785) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 52837785 * (79 : ZMod 16062686641) ^ 52837785 := by rw [pow_add]
          _ = 12052274209 := by rw [factor_7_25]; decide
      have factor_7_27 : (79 : ZMod 16062686641) ^ 211351140 = 14594158522 := by
        calc
          (79 : ZMod 16062686641) ^ 211351140 = (79 : ZMod 16062686641) ^ (105675570 + 105675570) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 105675570 * (79 : ZMod 16062686641) ^ 105675570 := by rw [pow_add]
          _ = 14594158522 := by rw [factor_7_26]; decide
      have factor_7_28 : (79 : ZMod 16062686641) ^ 422702280 = 5640189133 := by
        calc
          (79 : ZMod 16062686641) ^ 422702280 = (79 : ZMod 16062686641) ^ (211351140 + 211351140) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 211351140 * (79 : ZMod 16062686641) ^ 211351140 := by rw [pow_add]
          _ = 5640189133 := by rw [factor_7_27]; decide
      have factor_7_29 : (79 : ZMod 16062686641) ^ 845404560 = 611217997 := by
        calc
          (79 : ZMod 16062686641) ^ 845404560 = (79 : ZMod 16062686641) ^ (422702280 + 422702280) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 422702280 * (79 : ZMod 16062686641) ^ 422702280 := by rw [pow_add]
          _ = 611217997 := by rw [factor_7_28]; decide
      change (79 : ZMod 16062686641) ^ 845404560 ≠ 1
      rw [factor_7_29]
      decide
    ·
      have factor_8_0 : (79 : ZMod 16062686641) ^ 1 = 79 := by norm_num
      have factor_8_1 : (79 : ZMod 16062686641) ^ 2 = 6241 := by
        calc
          (79 : ZMod 16062686641) ^ 2 = (79 : ZMod 16062686641) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 1 * (79 : ZMod 16062686641) ^ 1 := by rw [pow_add]
          _ = 6241 := by rw [factor_8_0]; decide
      have factor_8_2 : (79 : ZMod 16062686641) ^ 5 = 3077056399 := by
        calc
          (79 : ZMod 16062686641) ^ 5 = (79 : ZMod 16062686641) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 2 * (79 : ZMod 16062686641) ^ 2) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 3077056399 := by rw [factor_8_1]; decide
      have factor_8_3 : (79 : ZMod 16062686641) ^ 10 = 8569417632 := by
        calc
          (79 : ZMod 16062686641) ^ 10 = (79 : ZMod 16062686641) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 5 * (79 : ZMod 16062686641) ^ 5 := by rw [pow_add]
          _ = 8569417632 := by rw [factor_8_2]; decide
      have factor_8_4 : (79 : ZMod 16062686641) ^ 20 = 9295932824 := by
        calc
          (79 : ZMod 16062686641) ^ 20 = (79 : ZMod 16062686641) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 10 * (79 : ZMod 16062686641) ^ 10 := by rw [pow_add]
          _ = 9295932824 := by rw [factor_8_3]; decide
      have factor_8_5 : (79 : ZMod 16062686641) ^ 41 = 5479382893 := by
        calc
          (79 : ZMod 16062686641) ^ 41 = (79 : ZMod 16062686641) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 20 * (79 : ZMod 16062686641) ^ 20) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 5479382893 := by rw [factor_8_4]; decide
      have factor_8_6 : (79 : ZMod 16062686641) ^ 83 = 1521287275 := by
        calc
          (79 : ZMod 16062686641) ^ 83 = (79 : ZMod 16062686641) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 41 * (79 : ZMod 16062686641) ^ 41) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 1521287275 := by rw [factor_8_5]; decide
      have factor_8_7 : (79 : ZMod 16062686641) ^ 166 = 13868497194 := by
        calc
          (79 : ZMod 16062686641) ^ 166 = (79 : ZMod 16062686641) ^ (83 + 83) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 83 * (79 : ZMod 16062686641) ^ 83 := by rw [pow_add]
          _ = 13868497194 := by rw [factor_8_6]; decide
      have factor_8_8 : (79 : ZMod 16062686641) ^ 333 = 2839662897 := by
        calc
          (79 : ZMod 16062686641) ^ 333 = (79 : ZMod 16062686641) ^ (166 + 166 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 166 * (79 : ZMod 16062686641) ^ 166) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 2839662897 := by rw [factor_8_7]; decide
      have factor_8_9 : (79 : ZMod 16062686641) ^ 666 = 5236332160 := by
        calc
          (79 : ZMod 16062686641) ^ 666 = (79 : ZMod 16062686641) ^ (333 + 333) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 333 * (79 : ZMod 16062686641) ^ 333 := by rw [pow_add]
          _ = 5236332160 := by rw [factor_8_8]; decide
      have factor_8_10 : (79 : ZMod 16062686641) ^ 1332 = 8519207997 := by
        calc
          (79 : ZMod 16062686641) ^ 1332 = (79 : ZMod 16062686641) ^ (666 + 666) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 666 * (79 : ZMod 16062686641) ^ 666 := by rw [pow_add]
          _ = 8519207997 := by rw [factor_8_9]; decide
      have factor_8_11 : (79 : ZMod 16062686641) ^ 2664 = 11284612061 := by
        calc
          (79 : ZMod 16062686641) ^ 2664 = (79 : ZMod 16062686641) ^ (1332 + 1332) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 1332 * (79 : ZMod 16062686641) ^ 1332 := by rw [pow_add]
          _ = 11284612061 := by rw [factor_8_10]; decide
      have factor_8_12 : (79 : ZMod 16062686641) ^ 5328 = 2274983124 := by
        calc
          (79 : ZMod 16062686641) ^ 5328 = (79 : ZMod 16062686641) ^ (2664 + 2664) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 2664 * (79 : ZMod 16062686641) ^ 2664 := by rw [pow_add]
          _ = 2274983124 := by rw [factor_8_11]; decide
      have factor_8_13 : (79 : ZMod 16062686641) ^ 10656 = 7130026642 := by
        calc
          (79 : ZMod 16062686641) ^ 10656 = (79 : ZMod 16062686641) ^ (5328 + 5328) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 5328 * (79 : ZMod 16062686641) ^ 5328 := by rw [pow_add]
          _ = 7130026642 := by rw [factor_8_12]; decide
      have factor_8_14 : (79 : ZMod 16062686641) ^ 21312 = 8729661217 := by
        calc
          (79 : ZMod 16062686641) ^ 21312 = (79 : ZMod 16062686641) ^ (10656 + 10656) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 10656 * (79 : ZMod 16062686641) ^ 10656 := by rw [pow_add]
          _ = 8729661217 := by rw [factor_8_13]; decide
      have factor_8_15 : (79 : ZMod 16062686641) ^ 42625 = 9506161488 := by
        calc
          (79 : ZMod 16062686641) ^ 42625 = (79 : ZMod 16062686641) ^ (21312 + 21312 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 21312 * (79 : ZMod 16062686641) ^ 21312) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 9506161488 := by rw [factor_8_14]; decide
      have factor_8_16 : (79 : ZMod 16062686641) ^ 85251 = 6377226408 := by
        calc
          (79 : ZMod 16062686641) ^ 85251 = (79 : ZMod 16062686641) ^ (42625 + 42625 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 42625 * (79 : ZMod 16062686641) ^ 42625) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 6377226408 := by rw [factor_8_15]; decide
      have factor_8_17 : (79 : ZMod 16062686641) ^ 170502 = 5452603228 := by
        calc
          (79 : ZMod 16062686641) ^ 170502 = (79 : ZMod 16062686641) ^ (85251 + 85251) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 85251 * (79 : ZMod 16062686641) ^ 85251 := by rw [pow_add]
          _ = 5452603228 := by rw [factor_8_16]; decide
      have factor_8_18 : (79 : ZMod 16062686641) ^ 341004 = 9504340762 := by
        calc
          (79 : ZMod 16062686641) ^ 341004 = (79 : ZMod 16062686641) ^ (170502 + 170502) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 170502 * (79 : ZMod 16062686641) ^ 170502 := by rw [pow_add]
          _ = 9504340762 := by rw [factor_8_17]; decide
      have factor_8_19 : (79 : ZMod 16062686641) ^ 682009 = 9477659336 := by
        calc
          (79 : ZMod 16062686641) ^ 682009 = (79 : ZMod 16062686641) ^ (341004 + 341004 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 341004 * (79 : ZMod 16062686641) ^ 341004) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 9477659336 := by rw [factor_8_18]; decide
      have factor_8_20 : (79 : ZMod 16062686641) ^ 1364018 = 765026071 := by
        calc
          (79 : ZMod 16062686641) ^ 1364018 = (79 : ZMod 16062686641) ^ (682009 + 682009) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 682009 * (79 : ZMod 16062686641) ^ 682009 := by rw [pow_add]
          _ = 765026071 := by rw [factor_8_19]; decide
      have factor_8_21 : (79 : ZMod 16062686641) ^ 2728037 = 9982779721 := by
        calc
          (79 : ZMod 16062686641) ^ 2728037 = (79 : ZMod 16062686641) ^ (1364018 + 1364018 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 1364018 * (79 : ZMod 16062686641) ^ 1364018) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 9982779721 := by rw [factor_8_20]; decide
      have factor_8_22 : (79 : ZMod 16062686641) ^ 5456075 = 10020118574 := by
        calc
          (79 : ZMod 16062686641) ^ 5456075 = (79 : ZMod 16062686641) ^ (2728037 + 2728037 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 2728037 * (79 : ZMod 16062686641) ^ 2728037) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 10020118574 := by rw [factor_8_21]; decide
      have factor_8_23 : (79 : ZMod 16062686641) ^ 10912151 = 1388850923 := by
        calc
          (79 : ZMod 16062686641) ^ 10912151 = (79 : ZMod 16062686641) ^ (5456075 + 5456075 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 5456075 * (79 : ZMod 16062686641) ^ 5456075) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 1388850923 := by rw [factor_8_22]; decide
      have factor_8_24 : (79 : ZMod 16062686641) ^ 21824302 = 14310990857 := by
        calc
          (79 : ZMod 16062686641) ^ 21824302 = (79 : ZMod 16062686641) ^ (10912151 + 10912151) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 10912151 * (79 : ZMod 16062686641) ^ 10912151 := by rw [pow_add]
          _ = 14310990857 := by rw [factor_8_23]; decide
      have factor_8_25 : (79 : ZMod 16062686641) ^ 43648605 = 14932926589 := by
        calc
          (79 : ZMod 16062686641) ^ 43648605 = (79 : ZMod 16062686641) ^ (21824302 + 21824302 + 1) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = ((79 : ZMod 16062686641) ^ 21824302 * (79 : ZMod 16062686641) ^ 21824302) * (79 : ZMod 16062686641) := by rw [pow_succ, pow_add]
          _ = 14932926589 := by rw [factor_8_24]; decide
      have factor_8_26 : (79 : ZMod 16062686641) ^ 87297210 = 5469762705 := by
        calc
          (79 : ZMod 16062686641) ^ 87297210 = (79 : ZMod 16062686641) ^ (43648605 + 43648605) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 43648605 * (79 : ZMod 16062686641) ^ 43648605 := by rw [pow_add]
          _ = 5469762705 := by rw [factor_8_25]; decide
      have factor_8_27 : (79 : ZMod 16062686641) ^ 174594420 = 2384067397 := by
        calc
          (79 : ZMod 16062686641) ^ 174594420 = (79 : ZMod 16062686641) ^ (87297210 + 87297210) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 87297210 * (79 : ZMod 16062686641) ^ 87297210 := by rw [pow_add]
          _ = 2384067397 := by rw [factor_8_26]; decide
      have factor_8_28 : (79 : ZMod 16062686641) ^ 349188840 = 6383212038 := by
        calc
          (79 : ZMod 16062686641) ^ 349188840 = (79 : ZMod 16062686641) ^ (174594420 + 174594420) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 174594420 * (79 : ZMod 16062686641) ^ 174594420 := by rw [pow_add]
          _ = 6383212038 := by rw [factor_8_27]; decide
      have factor_8_29 : (79 : ZMod 16062686641) ^ 698377680 = 5011367774 := by
        calc
          (79 : ZMod 16062686641) ^ 698377680 = (79 : ZMod 16062686641) ^ (349188840 + 349188840) :=
            congrArg (fun n : ℕ => (79 : ZMod 16062686641) ^ n) (by norm_num)
          _ = (79 : ZMod 16062686641) ^ 349188840 * (79 : ZMod 16062686641) ^ 349188840 := by rw [pow_add]
          _ = 5011367774 := by rw [factor_8_28]; decide
      change (79 : ZMod 16062686641) ^ 698377680 ≠ 1
      rw [factor_8_29]
      decide

#print axioms prime_lucas_16062686641

end TotientTailPeriodKiller
end Erdos249257
