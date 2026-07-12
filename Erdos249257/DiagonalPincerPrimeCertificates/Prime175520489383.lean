import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime154779973

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_175520489383 : Nat.Prime 175520489383 := by
  apply lucas_primality 175520489383 (5 : ZMod 175520489383)
  ·
      have fermat_0 : (5 : ZMod 175520489383) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 175520489383) ^ 2 = 25 := by
        calc
          (5 : ZMod 175520489383) ^ 2 = (5 : ZMod 175520489383) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 1 * (5 : ZMod 175520489383) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 175520489383) ^ 5 = 3125 := by
        calc
          (5 : ZMod 175520489383) ^ 5 = (5 : ZMod 175520489383) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 2 * (5 : ZMod 175520489383) ^ 2) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 175520489383) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 175520489383) ^ 10 = (5 : ZMod 175520489383) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 5 * (5 : ZMod 175520489383) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 175520489383) ^ 20 = 59805905656 := by
        calc
          (5 : ZMod 175520489383) ^ 20 = (5 : ZMod 175520489383) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 10 * (5 : ZMod 175520489383) ^ 10 := by rw [pow_add]
          _ = 59805905656 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 175520489383) ^ 40 = 104626430017 := by
        calc
          (5 : ZMod 175520489383) ^ 40 = (5 : ZMod 175520489383) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 20 * (5 : ZMod 175520489383) ^ 20 := by rw [pow_add]
          _ = 104626430017 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 175520489383) ^ 81 = 167240660815 := by
        calc
          (5 : ZMod 175520489383) ^ 81 = (5 : ZMod 175520489383) ^ (40 + 40 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 40 * (5 : ZMod 175520489383) ^ 40) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 167240660815 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 175520489383) ^ 163 = 68812338016 := by
        calc
          (5 : ZMod 175520489383) ^ 163 = (5 : ZMod 175520489383) ^ (81 + 81 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 81 * (5 : ZMod 175520489383) ^ 81) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 68812338016 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 175520489383) ^ 326 = 12106016045 := by
        calc
          (5 : ZMod 175520489383) ^ 326 = (5 : ZMod 175520489383) ^ (163 + 163) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 163 * (5 : ZMod 175520489383) ^ 163 := by rw [pow_add]
          _ = 12106016045 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 175520489383) ^ 653 = 108425223093 := by
        calc
          (5 : ZMod 175520489383) ^ 653 = (5 : ZMod 175520489383) ^ (326 + 326 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 326 * (5 : ZMod 175520489383) ^ 326) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 108425223093 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 175520489383) ^ 1307 = 169208545666 := by
        calc
          (5 : ZMod 175520489383) ^ 1307 = (5 : ZMod 175520489383) ^ (653 + 653 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 653 * (5 : ZMod 175520489383) ^ 653) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 169208545666 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 175520489383) ^ 2615 = 137151939822 := by
        calc
          (5 : ZMod 175520489383) ^ 2615 = (5 : ZMod 175520489383) ^ (1307 + 1307 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 1307 * (5 : ZMod 175520489383) ^ 1307) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 137151939822 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 175520489383) ^ 5230 = 93482843832 := by
        calc
          (5 : ZMod 175520489383) ^ 5230 = (5 : ZMod 175520489383) ^ (2615 + 2615) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 2615 * (5 : ZMod 175520489383) ^ 2615 := by rw [pow_add]
          _ = 93482843832 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 175520489383) ^ 10461 = 161236359865 := by
        calc
          (5 : ZMod 175520489383) ^ 10461 = (5 : ZMod 175520489383) ^ (5230 + 5230 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 5230 * (5 : ZMod 175520489383) ^ 5230) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 161236359865 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 175520489383) ^ 20923 = 39079533109 := by
        calc
          (5 : ZMod 175520489383) ^ 20923 = (5 : ZMod 175520489383) ^ (10461 + 10461 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 10461 * (5 : ZMod 175520489383) ^ 10461) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 39079533109 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 175520489383) ^ 41847 = 91864969945 := by
        calc
          (5 : ZMod 175520489383) ^ 41847 = (5 : ZMod 175520489383) ^ (20923 + 20923 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 20923 * (5 : ZMod 175520489383) ^ 20923) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 91864969945 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 175520489383) ^ 83694 = 46131821817 := by
        calc
          (5 : ZMod 175520489383) ^ 83694 = (5 : ZMod 175520489383) ^ (41847 + 41847) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 41847 * (5 : ZMod 175520489383) ^ 41847 := by rw [pow_add]
          _ = 46131821817 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 175520489383) ^ 167389 = 94085964605 := by
        calc
          (5 : ZMod 175520489383) ^ 167389 = (5 : ZMod 175520489383) ^ (83694 + 83694 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 83694 * (5 : ZMod 175520489383) ^ 83694) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 94085964605 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 175520489383) ^ 334778 = 94949792497 := by
        calc
          (5 : ZMod 175520489383) ^ 334778 = (5 : ZMod 175520489383) ^ (167389 + 167389) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 167389 * (5 : ZMod 175520489383) ^ 167389 := by rw [pow_add]
          _ = 94949792497 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 175520489383) ^ 669557 = 82282607514 := by
        calc
          (5 : ZMod 175520489383) ^ 669557 = (5 : ZMod 175520489383) ^ (334778 + 334778 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 334778 * (5 : ZMod 175520489383) ^ 334778) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 82282607514 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 175520489383) ^ 1339115 = 65349864270 := by
        calc
          (5 : ZMod 175520489383) ^ 1339115 = (5 : ZMod 175520489383) ^ (669557 + 669557 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 669557 * (5 : ZMod 175520489383) ^ 669557) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 65349864270 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 175520489383) ^ 2678230 = 150583787695 := by
        calc
          (5 : ZMod 175520489383) ^ 2678230 = (5 : ZMod 175520489383) ^ (1339115 + 1339115) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 1339115 * (5 : ZMod 175520489383) ^ 1339115 := by rw [pow_add]
          _ = 150583787695 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 175520489383) ^ 5356460 = 138226711215 := by
        calc
          (5 : ZMod 175520489383) ^ 5356460 = (5 : ZMod 175520489383) ^ (2678230 + 2678230) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 2678230 * (5 : ZMod 175520489383) ^ 2678230 := by rw [pow_add]
          _ = 138226711215 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 175520489383) ^ 10712920 = 54749612017 := by
        calc
          (5 : ZMod 175520489383) ^ 10712920 = (5 : ZMod 175520489383) ^ (5356460 + 5356460) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 5356460 * (5 : ZMod 175520489383) ^ 5356460 := by rw [pow_add]
          _ = 54749612017 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 175520489383) ^ 21425840 = 130658463559 := by
        calc
          (5 : ZMod 175520489383) ^ 21425840 = (5 : ZMod 175520489383) ^ (10712920 + 10712920) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 10712920 * (5 : ZMod 175520489383) ^ 10712920 := by rw [pow_add]
          _ = 130658463559 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 175520489383) ^ 42851681 = 173978160526 := by
        calc
          (5 : ZMod 175520489383) ^ 42851681 = (5 : ZMod 175520489383) ^ (21425840 + 21425840 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 21425840 * (5 : ZMod 175520489383) ^ 21425840) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 173978160526 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 175520489383) ^ 85703363 = 57345242595 := by
        calc
          (5 : ZMod 175520489383) ^ 85703363 = (5 : ZMod 175520489383) ^ (42851681 + 42851681 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 42851681 * (5 : ZMod 175520489383) ^ 42851681) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 57345242595 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 175520489383) ^ 171406727 = 4508580820 := by
        calc
          (5 : ZMod 175520489383) ^ 171406727 = (5 : ZMod 175520489383) ^ (85703363 + 85703363 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 85703363 * (5 : ZMod 175520489383) ^ 85703363) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 4508580820 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 175520489383) ^ 342813455 = 125725812260 := by
        calc
          (5 : ZMod 175520489383) ^ 342813455 = (5 : ZMod 175520489383) ^ (171406727 + 171406727 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 171406727 * (5 : ZMod 175520489383) ^ 171406727) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 125725812260 := by rw [fermat_27]; decide
      have fermat_29 : (5 : ZMod 175520489383) ^ 685626911 = 5161815868 := by
        calc
          (5 : ZMod 175520489383) ^ 685626911 = (5 : ZMod 175520489383) ^ (342813455 + 342813455 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 342813455 * (5 : ZMod 175520489383) ^ 342813455) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 5161815868 := by rw [fermat_28]; decide
      have fermat_30 : (5 : ZMod 175520489383) ^ 1371253823 = 75267105663 := by
        calc
          (5 : ZMod 175520489383) ^ 1371253823 = (5 : ZMod 175520489383) ^ (685626911 + 685626911 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 685626911 * (5 : ZMod 175520489383) ^ 685626911) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 75267105663 := by rw [fermat_29]; decide
      have fermat_31 : (5 : ZMod 175520489383) ^ 2742507646 = 131643945573 := by
        calc
          (5 : ZMod 175520489383) ^ 2742507646 = (5 : ZMod 175520489383) ^ (1371253823 + 1371253823) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 1371253823 * (5 : ZMod 175520489383) ^ 1371253823 := by rw [pow_add]
          _ = 131643945573 := by rw [fermat_30]; decide
      have fermat_32 : (5 : ZMod 175520489383) ^ 5485015293 = 107222342969 := by
        calc
          (5 : ZMod 175520489383) ^ 5485015293 = (5 : ZMod 175520489383) ^ (2742507646 + 2742507646 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 2742507646 * (5 : ZMod 175520489383) ^ 2742507646) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 107222342969 := by rw [fermat_31]; decide
      have fermat_33 : (5 : ZMod 175520489383) ^ 10970030586 = 135726306303 := by
        calc
          (5 : ZMod 175520489383) ^ 10970030586 = (5 : ZMod 175520489383) ^ (5485015293 + 5485015293) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 5485015293 * (5 : ZMod 175520489383) ^ 5485015293 := by rw [pow_add]
          _ = 135726306303 := by rw [fermat_32]; decide
      have fermat_34 : (5 : ZMod 175520489383) ^ 21940061172 = 63635612794 := by
        calc
          (5 : ZMod 175520489383) ^ 21940061172 = (5 : ZMod 175520489383) ^ (10970030586 + 10970030586) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 10970030586 * (5 : ZMod 175520489383) ^ 10970030586 := by rw [pow_add]
          _ = 63635612794 := by rw [fermat_33]; decide
      have fermat_35 : (5 : ZMod 175520489383) ^ 43880122345 = 70393686938 := by
        calc
          (5 : ZMod 175520489383) ^ 43880122345 = (5 : ZMod 175520489383) ^ (21940061172 + 21940061172 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 21940061172 * (5 : ZMod 175520489383) ^ 21940061172) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 70393686938 := by rw [fermat_34]; decide
      have fermat_36 : (5 : ZMod 175520489383) ^ 87760244691 = 175520489382 := by
        calc
          (5 : ZMod 175520489383) ^ 87760244691 = (5 : ZMod 175520489383) ^ (43880122345 + 43880122345 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 43880122345 * (5 : ZMod 175520489383) ^ 43880122345) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 175520489382 := by rw [fermat_35]; decide
      have fermat_37 : (5 : ZMod 175520489383) ^ 175520489382 = 1 := by
        calc
          (5 : ZMod 175520489383) ^ 175520489382 = (5 : ZMod 175520489383) ^ (87760244691 + 87760244691) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 87760244691 * (5 : ZMod 175520489383) ^ 87760244691 := by rw [pow_add]
          _ = 1 := by rw [fermat_36]; decide
      simpa using fermat_37
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 4), (7, 1), (154779973, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 4), (7, 1), (154779973, 1)] : List FactorBlock).map factorBlockValue).prod = 175520489383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_154779973) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 175520489383) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 175520489383) ^ 2 = 25 := by
        calc
          (5 : ZMod 175520489383) ^ 2 = (5 : ZMod 175520489383) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 1 * (5 : ZMod 175520489383) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 175520489383) ^ 5 = 3125 := by
        calc
          (5 : ZMod 175520489383) ^ 5 = (5 : ZMod 175520489383) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 2 * (5 : ZMod 175520489383) ^ 2) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 175520489383) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 175520489383) ^ 10 = (5 : ZMod 175520489383) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 5 * (5 : ZMod 175520489383) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 175520489383) ^ 20 = 59805905656 := by
        calc
          (5 : ZMod 175520489383) ^ 20 = (5 : ZMod 175520489383) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 10 * (5 : ZMod 175520489383) ^ 10 := by rw [pow_add]
          _ = 59805905656 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 175520489383) ^ 40 = 104626430017 := by
        calc
          (5 : ZMod 175520489383) ^ 40 = (5 : ZMod 175520489383) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 20 * (5 : ZMod 175520489383) ^ 20 := by rw [pow_add]
          _ = 104626430017 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 175520489383) ^ 81 = 167240660815 := by
        calc
          (5 : ZMod 175520489383) ^ 81 = (5 : ZMod 175520489383) ^ (40 + 40 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 40 * (5 : ZMod 175520489383) ^ 40) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 167240660815 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 175520489383) ^ 163 = 68812338016 := by
        calc
          (5 : ZMod 175520489383) ^ 163 = (5 : ZMod 175520489383) ^ (81 + 81 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 81 * (5 : ZMod 175520489383) ^ 81) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 68812338016 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 175520489383) ^ 326 = 12106016045 := by
        calc
          (5 : ZMod 175520489383) ^ 326 = (5 : ZMod 175520489383) ^ (163 + 163) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 163 * (5 : ZMod 175520489383) ^ 163 := by rw [pow_add]
          _ = 12106016045 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 175520489383) ^ 653 = 108425223093 := by
        calc
          (5 : ZMod 175520489383) ^ 653 = (5 : ZMod 175520489383) ^ (326 + 326 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 326 * (5 : ZMod 175520489383) ^ 326) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 108425223093 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 175520489383) ^ 1307 = 169208545666 := by
        calc
          (5 : ZMod 175520489383) ^ 1307 = (5 : ZMod 175520489383) ^ (653 + 653 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 653 * (5 : ZMod 175520489383) ^ 653) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 169208545666 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 175520489383) ^ 2615 = 137151939822 := by
        calc
          (5 : ZMod 175520489383) ^ 2615 = (5 : ZMod 175520489383) ^ (1307 + 1307 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 1307 * (5 : ZMod 175520489383) ^ 1307) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 137151939822 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 175520489383) ^ 5230 = 93482843832 := by
        calc
          (5 : ZMod 175520489383) ^ 5230 = (5 : ZMod 175520489383) ^ (2615 + 2615) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 2615 * (5 : ZMod 175520489383) ^ 2615 := by rw [pow_add]
          _ = 93482843832 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 175520489383) ^ 10461 = 161236359865 := by
        calc
          (5 : ZMod 175520489383) ^ 10461 = (5 : ZMod 175520489383) ^ (5230 + 5230 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 5230 * (5 : ZMod 175520489383) ^ 5230) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 161236359865 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 175520489383) ^ 20923 = 39079533109 := by
        calc
          (5 : ZMod 175520489383) ^ 20923 = (5 : ZMod 175520489383) ^ (10461 + 10461 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 10461 * (5 : ZMod 175520489383) ^ 10461) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 39079533109 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 175520489383) ^ 41847 = 91864969945 := by
        calc
          (5 : ZMod 175520489383) ^ 41847 = (5 : ZMod 175520489383) ^ (20923 + 20923 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 20923 * (5 : ZMod 175520489383) ^ 20923) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 91864969945 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 175520489383) ^ 83694 = 46131821817 := by
        calc
          (5 : ZMod 175520489383) ^ 83694 = (5 : ZMod 175520489383) ^ (41847 + 41847) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 41847 * (5 : ZMod 175520489383) ^ 41847 := by rw [pow_add]
          _ = 46131821817 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 175520489383) ^ 167389 = 94085964605 := by
        calc
          (5 : ZMod 175520489383) ^ 167389 = (5 : ZMod 175520489383) ^ (83694 + 83694 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 83694 * (5 : ZMod 175520489383) ^ 83694) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 94085964605 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 175520489383) ^ 334778 = 94949792497 := by
        calc
          (5 : ZMod 175520489383) ^ 334778 = (5 : ZMod 175520489383) ^ (167389 + 167389) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 167389 * (5 : ZMod 175520489383) ^ 167389 := by rw [pow_add]
          _ = 94949792497 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 175520489383) ^ 669557 = 82282607514 := by
        calc
          (5 : ZMod 175520489383) ^ 669557 = (5 : ZMod 175520489383) ^ (334778 + 334778 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 334778 * (5 : ZMod 175520489383) ^ 334778) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 82282607514 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 175520489383) ^ 1339115 = 65349864270 := by
        calc
          (5 : ZMod 175520489383) ^ 1339115 = (5 : ZMod 175520489383) ^ (669557 + 669557 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 669557 * (5 : ZMod 175520489383) ^ 669557) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 65349864270 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 175520489383) ^ 2678230 = 150583787695 := by
        calc
          (5 : ZMod 175520489383) ^ 2678230 = (5 : ZMod 175520489383) ^ (1339115 + 1339115) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 1339115 * (5 : ZMod 175520489383) ^ 1339115 := by rw [pow_add]
          _ = 150583787695 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 175520489383) ^ 5356460 = 138226711215 := by
        calc
          (5 : ZMod 175520489383) ^ 5356460 = (5 : ZMod 175520489383) ^ (2678230 + 2678230) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 2678230 * (5 : ZMod 175520489383) ^ 2678230 := by rw [pow_add]
          _ = 138226711215 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 175520489383) ^ 10712920 = 54749612017 := by
        calc
          (5 : ZMod 175520489383) ^ 10712920 = (5 : ZMod 175520489383) ^ (5356460 + 5356460) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 5356460 * (5 : ZMod 175520489383) ^ 5356460 := by rw [pow_add]
          _ = 54749612017 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 175520489383) ^ 21425840 = 130658463559 := by
        calc
          (5 : ZMod 175520489383) ^ 21425840 = (5 : ZMod 175520489383) ^ (10712920 + 10712920) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 10712920 * (5 : ZMod 175520489383) ^ 10712920 := by rw [pow_add]
          _ = 130658463559 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 175520489383) ^ 42851681 = 173978160526 := by
        calc
          (5 : ZMod 175520489383) ^ 42851681 = (5 : ZMod 175520489383) ^ (21425840 + 21425840 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 21425840 * (5 : ZMod 175520489383) ^ 21425840) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 173978160526 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 175520489383) ^ 85703363 = 57345242595 := by
        calc
          (5 : ZMod 175520489383) ^ 85703363 = (5 : ZMod 175520489383) ^ (42851681 + 42851681 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 42851681 * (5 : ZMod 175520489383) ^ 42851681) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 57345242595 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 175520489383) ^ 171406727 = 4508580820 := by
        calc
          (5 : ZMod 175520489383) ^ 171406727 = (5 : ZMod 175520489383) ^ (85703363 + 85703363 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 85703363 * (5 : ZMod 175520489383) ^ 85703363) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 4508580820 := by rw [factor_0_26]; decide
      have factor_0_28 : (5 : ZMod 175520489383) ^ 342813455 = 125725812260 := by
        calc
          (5 : ZMod 175520489383) ^ 342813455 = (5 : ZMod 175520489383) ^ (171406727 + 171406727 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 171406727 * (5 : ZMod 175520489383) ^ 171406727) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 125725812260 := by rw [factor_0_27]; decide
      have factor_0_29 : (5 : ZMod 175520489383) ^ 685626911 = 5161815868 := by
        calc
          (5 : ZMod 175520489383) ^ 685626911 = (5 : ZMod 175520489383) ^ (342813455 + 342813455 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 342813455 * (5 : ZMod 175520489383) ^ 342813455) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 5161815868 := by rw [factor_0_28]; decide
      have factor_0_30 : (5 : ZMod 175520489383) ^ 1371253823 = 75267105663 := by
        calc
          (5 : ZMod 175520489383) ^ 1371253823 = (5 : ZMod 175520489383) ^ (685626911 + 685626911 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 685626911 * (5 : ZMod 175520489383) ^ 685626911) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 75267105663 := by rw [factor_0_29]; decide
      have factor_0_31 : (5 : ZMod 175520489383) ^ 2742507646 = 131643945573 := by
        calc
          (5 : ZMod 175520489383) ^ 2742507646 = (5 : ZMod 175520489383) ^ (1371253823 + 1371253823) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 1371253823 * (5 : ZMod 175520489383) ^ 1371253823 := by rw [pow_add]
          _ = 131643945573 := by rw [factor_0_30]; decide
      have factor_0_32 : (5 : ZMod 175520489383) ^ 5485015293 = 107222342969 := by
        calc
          (5 : ZMod 175520489383) ^ 5485015293 = (5 : ZMod 175520489383) ^ (2742507646 + 2742507646 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 2742507646 * (5 : ZMod 175520489383) ^ 2742507646) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 107222342969 := by rw [factor_0_31]; decide
      have factor_0_33 : (5 : ZMod 175520489383) ^ 10970030586 = 135726306303 := by
        calc
          (5 : ZMod 175520489383) ^ 10970030586 = (5 : ZMod 175520489383) ^ (5485015293 + 5485015293) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 5485015293 * (5 : ZMod 175520489383) ^ 5485015293 := by rw [pow_add]
          _ = 135726306303 := by rw [factor_0_32]; decide
      have factor_0_34 : (5 : ZMod 175520489383) ^ 21940061172 = 63635612794 := by
        calc
          (5 : ZMod 175520489383) ^ 21940061172 = (5 : ZMod 175520489383) ^ (10970030586 + 10970030586) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 10970030586 * (5 : ZMod 175520489383) ^ 10970030586 := by rw [pow_add]
          _ = 63635612794 := by rw [factor_0_33]; decide
      have factor_0_35 : (5 : ZMod 175520489383) ^ 43880122345 = 70393686938 := by
        calc
          (5 : ZMod 175520489383) ^ 43880122345 = (5 : ZMod 175520489383) ^ (21940061172 + 21940061172 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 21940061172 * (5 : ZMod 175520489383) ^ 21940061172) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 70393686938 := by rw [factor_0_34]; decide
      have factor_0_36 : (5 : ZMod 175520489383) ^ 87760244691 = 175520489382 := by
        calc
          (5 : ZMod 175520489383) ^ 87760244691 = (5 : ZMod 175520489383) ^ (43880122345 + 43880122345 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 43880122345 * (5 : ZMod 175520489383) ^ 43880122345) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 175520489382 := by rw [factor_0_35]; decide
      change (5 : ZMod 175520489383) ^ 87760244691 ≠ 1
      rw [factor_0_36]
      decide
    ·
      have factor_1_0 : (5 : ZMod 175520489383) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 175520489383) ^ 3 = 125 := by
        calc
          (5 : ZMod 175520489383) ^ 3 = (5 : ZMod 175520489383) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 1 * (5 : ZMod 175520489383) ^ 1) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 175520489383) ^ 6 = 15625 := by
        calc
          (5 : ZMod 175520489383) ^ 6 = (5 : ZMod 175520489383) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 3 * (5 : ZMod 175520489383) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 175520489383) ^ 13 = 1220703125 := by
        calc
          (5 : ZMod 175520489383) ^ 13 = (5 : ZMod 175520489383) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 6 * (5 : ZMod 175520489383) ^ 6) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 1220703125 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 175520489383) ^ 27 = 156472488923 := by
        calc
          (5 : ZMod 175520489383) ^ 27 = (5 : ZMod 175520489383) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 13 * (5 : ZMod 175520489383) ^ 13) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 156472488923 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 175520489383) ^ 54 = 15764355087 := by
        calc
          (5 : ZMod 175520489383) ^ 54 = (5 : ZMod 175520489383) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 27 * (5 : ZMod 175520489383) ^ 27 := by rw [pow_add]
          _ = 15764355087 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 175520489383) ^ 108 = 67574163974 := by
        calc
          (5 : ZMod 175520489383) ^ 108 = (5 : ZMod 175520489383) ^ (54 + 54) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 54 * (5 : ZMod 175520489383) ^ 54 := by rw [pow_add]
          _ = 67574163974 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 175520489383) ^ 217 = 111069479196 := by
        calc
          (5 : ZMod 175520489383) ^ 217 = (5 : ZMod 175520489383) ^ (108 + 108 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 108 * (5 : ZMod 175520489383) ^ 108) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 111069479196 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 175520489383) ^ 435 = 33635446392 := by
        calc
          (5 : ZMod 175520489383) ^ 435 = (5 : ZMod 175520489383) ^ (217 + 217 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 217 * (5 : ZMod 175520489383) ^ 217) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 33635446392 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 175520489383) ^ 871 = 122074361215 := by
        calc
          (5 : ZMod 175520489383) ^ 871 = (5 : ZMod 175520489383) ^ (435 + 435 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 435 * (5 : ZMod 175520489383) ^ 435) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 122074361215 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 175520489383) ^ 1743 = 94966820801 := by
        calc
          (5 : ZMod 175520489383) ^ 1743 = (5 : ZMod 175520489383) ^ (871 + 871 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 871 * (5 : ZMod 175520489383) ^ 871) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 94966820801 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 175520489383) ^ 3487 = 109017988989 := by
        calc
          (5 : ZMod 175520489383) ^ 3487 = (5 : ZMod 175520489383) ^ (1743 + 1743 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 1743 * (5 : ZMod 175520489383) ^ 1743) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 109017988989 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 175520489383) ^ 6974 = 158468881472 := by
        calc
          (5 : ZMod 175520489383) ^ 6974 = (5 : ZMod 175520489383) ^ (3487 + 3487) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 3487 * (5 : ZMod 175520489383) ^ 3487 := by rw [pow_add]
          _ = 158468881472 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 175520489383) ^ 13949 = 84439591867 := by
        calc
          (5 : ZMod 175520489383) ^ 13949 = (5 : ZMod 175520489383) ^ (6974 + 6974 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 6974 * (5 : ZMod 175520489383) ^ 6974) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 84439591867 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 175520489383) ^ 27898 = 111399931251 := by
        calc
          (5 : ZMod 175520489383) ^ 27898 = (5 : ZMod 175520489383) ^ (13949 + 13949) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 13949 * (5 : ZMod 175520489383) ^ 13949 := by rw [pow_add]
          _ = 111399931251 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 175520489383) ^ 55796 = 150909134853 := by
        calc
          (5 : ZMod 175520489383) ^ 55796 = (5 : ZMod 175520489383) ^ (27898 + 27898) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 27898 * (5 : ZMod 175520489383) ^ 27898 := by rw [pow_add]
          _ = 150909134853 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 175520489383) ^ 111592 = 42613603855 := by
        calc
          (5 : ZMod 175520489383) ^ 111592 = (5 : ZMod 175520489383) ^ (55796 + 55796) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 55796 * (5 : ZMod 175520489383) ^ 55796 := by rw [pow_add]
          _ = 42613603855 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 175520489383) ^ 223185 = 92448924373 := by
        calc
          (5 : ZMod 175520489383) ^ 223185 = (5 : ZMod 175520489383) ^ (111592 + 111592 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 111592 * (5 : ZMod 175520489383) ^ 111592) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 92448924373 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 175520489383) ^ 446371 = 44655790012 := by
        calc
          (5 : ZMod 175520489383) ^ 446371 = (5 : ZMod 175520489383) ^ (223185 + 223185 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 223185 * (5 : ZMod 175520489383) ^ 223185) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 44655790012 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 175520489383) ^ 892743 = 126367654392 := by
        calc
          (5 : ZMod 175520489383) ^ 892743 = (5 : ZMod 175520489383) ^ (446371 + 446371 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 446371 * (5 : ZMod 175520489383) ^ 446371) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 126367654392 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 175520489383) ^ 1785486 = 65122304219 := by
        calc
          (5 : ZMod 175520489383) ^ 1785486 = (5 : ZMod 175520489383) ^ (892743 + 892743) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 892743 * (5 : ZMod 175520489383) ^ 892743 := by rw [pow_add]
          _ = 65122304219 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 175520489383) ^ 3570973 = 141140948108 := by
        calc
          (5 : ZMod 175520489383) ^ 3570973 = (5 : ZMod 175520489383) ^ (1785486 + 1785486 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 1785486 * (5 : ZMod 175520489383) ^ 1785486) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 141140948108 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 175520489383) ^ 7141946 = 77970052754 := by
        calc
          (5 : ZMod 175520489383) ^ 7141946 = (5 : ZMod 175520489383) ^ (3570973 + 3570973) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 3570973 * (5 : ZMod 175520489383) ^ 3570973 := by rw [pow_add]
          _ = 77970052754 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 175520489383) ^ 14283893 = 18834336974 := by
        calc
          (5 : ZMod 175520489383) ^ 14283893 = (5 : ZMod 175520489383) ^ (7141946 + 7141946 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 7141946 * (5 : ZMod 175520489383) ^ 7141946) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 18834336974 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 175520489383) ^ 28567787 = 156775483888 := by
        calc
          (5 : ZMod 175520489383) ^ 28567787 = (5 : ZMod 175520489383) ^ (14283893 + 14283893 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 14283893 * (5 : ZMod 175520489383) ^ 14283893) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 156775483888 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 175520489383) ^ 57135575 = 41241331173 := by
        calc
          (5 : ZMod 175520489383) ^ 57135575 = (5 : ZMod 175520489383) ^ (28567787 + 28567787 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 28567787 * (5 : ZMod 175520489383) ^ 28567787) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 41241331173 := by rw [factor_1_24]; decide
      have factor_1_26 : (5 : ZMod 175520489383) ^ 114271151 = 117773297110 := by
        calc
          (5 : ZMod 175520489383) ^ 114271151 = (5 : ZMod 175520489383) ^ (57135575 + 57135575 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 57135575 * (5 : ZMod 175520489383) ^ 57135575) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 117773297110 := by rw [factor_1_25]; decide
      have factor_1_27 : (5 : ZMod 175520489383) ^ 228542303 = 73947025344 := by
        calc
          (5 : ZMod 175520489383) ^ 228542303 = (5 : ZMod 175520489383) ^ (114271151 + 114271151 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 114271151 * (5 : ZMod 175520489383) ^ 114271151) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 73947025344 := by rw [factor_1_26]; decide
      have factor_1_28 : (5 : ZMod 175520489383) ^ 457084607 = 172704612103 := by
        calc
          (5 : ZMod 175520489383) ^ 457084607 = (5 : ZMod 175520489383) ^ (228542303 + 228542303 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 228542303 * (5 : ZMod 175520489383) ^ 228542303) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 172704612103 := by rw [factor_1_27]; decide
      have factor_1_29 : (5 : ZMod 175520489383) ^ 914169215 = 169623446537 := by
        calc
          (5 : ZMod 175520489383) ^ 914169215 = (5 : ZMod 175520489383) ^ (457084607 + 457084607 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 457084607 * (5 : ZMod 175520489383) ^ 457084607) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 169623446537 := by rw [factor_1_28]; decide
      have factor_1_30 : (5 : ZMod 175520489383) ^ 1828338431 = 77768516211 := by
        calc
          (5 : ZMod 175520489383) ^ 1828338431 = (5 : ZMod 175520489383) ^ (914169215 + 914169215 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 914169215 * (5 : ZMod 175520489383) ^ 914169215) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 77768516211 := by rw [factor_1_29]; decide
      have factor_1_31 : (5 : ZMod 175520489383) ^ 3656676862 = 161213882036 := by
        calc
          (5 : ZMod 175520489383) ^ 3656676862 = (5 : ZMod 175520489383) ^ (1828338431 + 1828338431) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 1828338431 * (5 : ZMod 175520489383) ^ 1828338431 := by rw [pow_add]
          _ = 161213882036 := by rw [factor_1_30]; decide
      have factor_1_32 : (5 : ZMod 175520489383) ^ 7313353724 = 31613076940 := by
        calc
          (5 : ZMod 175520489383) ^ 7313353724 = (5 : ZMod 175520489383) ^ (3656676862 + 3656676862) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 3656676862 * (5 : ZMod 175520489383) ^ 3656676862 := by rw [pow_add]
          _ = 31613076940 := by rw [factor_1_31]; decide
      have factor_1_33 : (5 : ZMod 175520489383) ^ 14626707448 = 31250575728 := by
        calc
          (5 : ZMod 175520489383) ^ 14626707448 = (5 : ZMod 175520489383) ^ (7313353724 + 7313353724) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 7313353724 * (5 : ZMod 175520489383) ^ 7313353724 := by rw [pow_add]
          _ = 31250575728 := by rw [factor_1_32]; decide
      have factor_1_34 : (5 : ZMod 175520489383) ^ 29253414897 = 95514825906 := by
        calc
          (5 : ZMod 175520489383) ^ 29253414897 = (5 : ZMod 175520489383) ^ (14626707448 + 14626707448 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 14626707448 * (5 : ZMod 175520489383) ^ 14626707448) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 95514825906 := by rw [factor_1_33]; decide
      have factor_1_35 : (5 : ZMod 175520489383) ^ 58506829794 = 95514825905 := by
        calc
          (5 : ZMod 175520489383) ^ 58506829794 = (5 : ZMod 175520489383) ^ (29253414897 + 29253414897) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 29253414897 * (5 : ZMod 175520489383) ^ 29253414897 := by rw [pow_add]
          _ = 95514825905 := by rw [factor_1_34]; decide
      change (5 : ZMod 175520489383) ^ 58506829794 ≠ 1
      rw [factor_1_35]
      decide
    ·
      have factor_2_0 : (5 : ZMod 175520489383) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 175520489383) ^ 2 = 25 := by
        calc
          (5 : ZMod 175520489383) ^ 2 = (5 : ZMod 175520489383) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 1 * (5 : ZMod 175520489383) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 175520489383) ^ 5 = 3125 := by
        calc
          (5 : ZMod 175520489383) ^ 5 = (5 : ZMod 175520489383) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 2 * (5 : ZMod 175520489383) ^ 2) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 175520489383) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 175520489383) ^ 11 = (5 : ZMod 175520489383) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 5 * (5 : ZMod 175520489383) ^ 5) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 175520489383) ^ 23 = 103877652914 := by
        calc
          (5 : ZMod 175520489383) ^ 23 = (5 : ZMod 175520489383) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 11 * (5 : ZMod 175520489383) ^ 11) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 103877652914 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 175520489383) ^ 46 = 165651391746 := by
        calc
          (5 : ZMod 175520489383) ^ 46 = (5 : ZMod 175520489383) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 23 * (5 : ZMod 175520489383) ^ 23 := by rw [pow_add]
          _ = 165651391746 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 175520489383) ^ 93 = 100104760401 := by
        calc
          (5 : ZMod 175520489383) ^ 93 = (5 : ZMod 175520489383) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 46 * (5 : ZMod 175520489383) ^ 46) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 100104760401 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 175520489383) ^ 186 = 57232150693 := by
        calc
          (5 : ZMod 175520489383) ^ 186 = (5 : ZMod 175520489383) ^ (93 + 93) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 93 * (5 : ZMod 175520489383) ^ 93 := by rw [pow_add]
          _ = 57232150693 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 175520489383) ^ 373 = 64833182542 := by
        calc
          (5 : ZMod 175520489383) ^ 373 = (5 : ZMod 175520489383) ^ (186 + 186 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 186 * (5 : ZMod 175520489383) ^ 186) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 64833182542 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 175520489383) ^ 747 = 120339043004 := by
        calc
          (5 : ZMod 175520489383) ^ 747 = (5 : ZMod 175520489383) ^ (373 + 373 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 373 * (5 : ZMod 175520489383) ^ 373) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 120339043004 := by rw [factor_2_8]; decide
      have factor_2_10 : (5 : ZMod 175520489383) ^ 1494 = 28018767694 := by
        calc
          (5 : ZMod 175520489383) ^ 1494 = (5 : ZMod 175520489383) ^ (747 + 747) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 747 * (5 : ZMod 175520489383) ^ 747 := by rw [pow_add]
          _ = 28018767694 := by rw [factor_2_9]; decide
      have factor_2_11 : (5 : ZMod 175520489383) ^ 2989 = 28717031920 := by
        calc
          (5 : ZMod 175520489383) ^ 2989 = (5 : ZMod 175520489383) ^ (1494 + 1494 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 1494 * (5 : ZMod 175520489383) ^ 1494) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 28717031920 := by rw [factor_2_10]; decide
      have factor_2_12 : (5 : ZMod 175520489383) ^ 5978 = 147647175762 := by
        calc
          (5 : ZMod 175520489383) ^ 5978 = (5 : ZMod 175520489383) ^ (2989 + 2989) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 2989 * (5 : ZMod 175520489383) ^ 2989 := by rw [pow_add]
          _ = 147647175762 := by rw [factor_2_11]; decide
      have factor_2_13 : (5 : ZMod 175520489383) ^ 11956 = 127115889407 := by
        calc
          (5 : ZMod 175520489383) ^ 11956 = (5 : ZMod 175520489383) ^ (5978 + 5978) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 5978 * (5 : ZMod 175520489383) ^ 5978 := by rw [pow_add]
          _ = 127115889407 := by rw [factor_2_12]; decide
      have factor_2_14 : (5 : ZMod 175520489383) ^ 23912 = 117262201085 := by
        calc
          (5 : ZMod 175520489383) ^ 23912 = (5 : ZMod 175520489383) ^ (11956 + 11956) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 11956 * (5 : ZMod 175520489383) ^ 11956 := by rw [pow_add]
          _ = 117262201085 := by rw [factor_2_13]; decide
      have factor_2_15 : (5 : ZMod 175520489383) ^ 47825 = 113730626317 := by
        calc
          (5 : ZMod 175520489383) ^ 47825 = (5 : ZMod 175520489383) ^ (23912 + 23912 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 23912 * (5 : ZMod 175520489383) ^ 23912) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 113730626317 := by rw [factor_2_14]; decide
      have factor_2_16 : (5 : ZMod 175520489383) ^ 95651 = 144167909553 := by
        calc
          (5 : ZMod 175520489383) ^ 95651 = (5 : ZMod 175520489383) ^ (47825 + 47825 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 47825 * (5 : ZMod 175520489383) ^ 47825) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 144167909553 := by rw [factor_2_15]; decide
      have factor_2_17 : (5 : ZMod 175520489383) ^ 191302 = 67644584579 := by
        calc
          (5 : ZMod 175520489383) ^ 191302 = (5 : ZMod 175520489383) ^ (95651 + 95651) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 95651 * (5 : ZMod 175520489383) ^ 95651 := by rw [pow_add]
          _ = 67644584579 := by rw [factor_2_16]; decide
      have factor_2_18 : (5 : ZMod 175520489383) ^ 382604 = 92147145563 := by
        calc
          (5 : ZMod 175520489383) ^ 382604 = (5 : ZMod 175520489383) ^ (191302 + 191302) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 191302 * (5 : ZMod 175520489383) ^ 191302 := by rw [pow_add]
          _ = 92147145563 := by rw [factor_2_17]; decide
      have factor_2_19 : (5 : ZMod 175520489383) ^ 765208 = 175093828906 := by
        calc
          (5 : ZMod 175520489383) ^ 765208 = (5 : ZMod 175520489383) ^ (382604 + 382604) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 382604 * (5 : ZMod 175520489383) ^ 382604 := by rw [pow_add]
          _ = 175093828906 := by rw [factor_2_18]; decide
      have factor_2_20 : (5 : ZMod 175520489383) ^ 1530417 = 88978361460 := by
        calc
          (5 : ZMod 175520489383) ^ 1530417 = (5 : ZMod 175520489383) ^ (765208 + 765208 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 765208 * (5 : ZMod 175520489383) ^ 765208) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 88978361460 := by rw [factor_2_19]; decide
      have factor_2_21 : (5 : ZMod 175520489383) ^ 3060834 = 62213596092 := by
        calc
          (5 : ZMod 175520489383) ^ 3060834 = (5 : ZMod 175520489383) ^ (1530417 + 1530417) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 1530417 * (5 : ZMod 175520489383) ^ 1530417 := by rw [pow_add]
          _ = 62213596092 := by rw [factor_2_20]; decide
      have factor_2_22 : (5 : ZMod 175520489383) ^ 6121668 = 2635459948 := by
        calc
          (5 : ZMod 175520489383) ^ 6121668 = (5 : ZMod 175520489383) ^ (3060834 + 3060834) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 3060834 * (5 : ZMod 175520489383) ^ 3060834 := by rw [pow_add]
          _ = 2635459948 := by rw [factor_2_21]; decide
      have factor_2_23 : (5 : ZMod 175520489383) ^ 12243337 = 15065015634 := by
        calc
          (5 : ZMod 175520489383) ^ 12243337 = (5 : ZMod 175520489383) ^ (6121668 + 6121668 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 6121668 * (5 : ZMod 175520489383) ^ 6121668) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 15065015634 := by rw [factor_2_22]; decide
      have factor_2_24 : (5 : ZMod 175520489383) ^ 24486675 = 62697468398 := by
        calc
          (5 : ZMod 175520489383) ^ 24486675 = (5 : ZMod 175520489383) ^ (12243337 + 12243337 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 12243337 * (5 : ZMod 175520489383) ^ 12243337) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 62697468398 := by rw [factor_2_23]; decide
      have factor_2_25 : (5 : ZMod 175520489383) ^ 48973350 = 23588636867 := by
        calc
          (5 : ZMod 175520489383) ^ 48973350 = (5 : ZMod 175520489383) ^ (24486675 + 24486675) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 24486675 * (5 : ZMod 175520489383) ^ 24486675 := by rw [pow_add]
          _ = 23588636867 := by rw [factor_2_24]; decide
      have factor_2_26 : (5 : ZMod 175520489383) ^ 97946701 = 25325990316 := by
        calc
          (5 : ZMod 175520489383) ^ 97946701 = (5 : ZMod 175520489383) ^ (48973350 + 48973350 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 48973350 * (5 : ZMod 175520489383) ^ 48973350) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 25325990316 := by rw [factor_2_25]; decide
      have factor_2_27 : (5 : ZMod 175520489383) ^ 195893403 = 95563315005 := by
        calc
          (5 : ZMod 175520489383) ^ 195893403 = (5 : ZMod 175520489383) ^ (97946701 + 97946701 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 97946701 * (5 : ZMod 175520489383) ^ 97946701) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 95563315005 := by rw [factor_2_26]; decide
      have factor_2_28 : (5 : ZMod 175520489383) ^ 391786806 = 68524748157 := by
        calc
          (5 : ZMod 175520489383) ^ 391786806 = (5 : ZMod 175520489383) ^ (195893403 + 195893403) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 195893403 * (5 : ZMod 175520489383) ^ 195893403 := by rw [pow_add]
          _ = 68524748157 := by rw [factor_2_27]; decide
      have factor_2_29 : (5 : ZMod 175520489383) ^ 783573613 = 120675192834 := by
        calc
          (5 : ZMod 175520489383) ^ 783573613 = (5 : ZMod 175520489383) ^ (391786806 + 391786806 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 391786806 * (5 : ZMod 175520489383) ^ 391786806) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 120675192834 := by rw [factor_2_28]; decide
      have factor_2_30 : (5 : ZMod 175520489383) ^ 1567147226 = 32487621663 := by
        calc
          (5 : ZMod 175520489383) ^ 1567147226 = (5 : ZMod 175520489383) ^ (783573613 + 783573613) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 783573613 * (5 : ZMod 175520489383) ^ 783573613 := by rw [pow_add]
          _ = 32487621663 := by rw [factor_2_29]; decide
      have factor_2_31 : (5 : ZMod 175520489383) ^ 3134294453 = 79072851421 := by
        calc
          (5 : ZMod 175520489383) ^ 3134294453 = (5 : ZMod 175520489383) ^ (1567147226 + 1567147226 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 1567147226 * (5 : ZMod 175520489383) ^ 1567147226) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 79072851421 := by rw [factor_2_30]; decide
      have factor_2_32 : (5 : ZMod 175520489383) ^ 6268588906 = 42227322519 := by
        calc
          (5 : ZMod 175520489383) ^ 6268588906 = (5 : ZMod 175520489383) ^ (3134294453 + 3134294453) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 3134294453 * (5 : ZMod 175520489383) ^ 3134294453 := by rw [pow_add]
          _ = 42227322519 := by rw [factor_2_31]; decide
      have factor_2_33 : (5 : ZMod 175520489383) ^ 12537177813 = 102897020234 := by
        calc
          (5 : ZMod 175520489383) ^ 12537177813 = (5 : ZMod 175520489383) ^ (6268588906 + 6268588906 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 6268588906 * (5 : ZMod 175520489383) ^ 6268588906) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 102897020234 := by rw [factor_2_32]; decide
      have factor_2_34 : (5 : ZMod 175520489383) ^ 25074355626 = 111033498122 := by
        calc
          (5 : ZMod 175520489383) ^ 25074355626 = (5 : ZMod 175520489383) ^ (12537177813 + 12537177813) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 12537177813 * (5 : ZMod 175520489383) ^ 12537177813 := by rw [pow_add]
          _ = 111033498122 := by rw [factor_2_33]; decide
      change (5 : ZMod 175520489383) ^ 25074355626 ≠ 1
      rw [factor_2_34]
      decide
    ·
      have factor_3_0 : (5 : ZMod 175520489383) ^ 1 = 5 := by norm_num
      have factor_3_1 : (5 : ZMod 175520489383) ^ 2 = 25 := by
        calc
          (5 : ZMod 175520489383) ^ 2 = (5 : ZMod 175520489383) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 1 * (5 : ZMod 175520489383) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_3_0]; decide
      have factor_3_2 : (5 : ZMod 175520489383) ^ 4 = 625 := by
        calc
          (5 : ZMod 175520489383) ^ 4 = (5 : ZMod 175520489383) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 2 * (5 : ZMod 175520489383) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_3_1]; decide
      have factor_3_3 : (5 : ZMod 175520489383) ^ 8 = 390625 := by
        calc
          (5 : ZMod 175520489383) ^ 8 = (5 : ZMod 175520489383) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 4 * (5 : ZMod 175520489383) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_3_2]; decide
      have factor_3_4 : (5 : ZMod 175520489383) ^ 17 = 60857495593 := by
        calc
          (5 : ZMod 175520489383) ^ 17 = (5 : ZMod 175520489383) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 8 * (5 : ZMod 175520489383) ^ 8) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 60857495593 := by rw [factor_3_3]; decide
      have factor_3_5 : (5 : ZMod 175520489383) ^ 35 = 39406236636 := by
        calc
          (5 : ZMod 175520489383) ^ 35 = (5 : ZMod 175520489383) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 17 * (5 : ZMod 175520489383) ^ 17) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 39406236636 := by rw [factor_3_4]; decide
      have factor_3_6 : (5 : ZMod 175520489383) ^ 70 = 143999174204 := by
        calc
          (5 : ZMod 175520489383) ^ 70 = (5 : ZMod 175520489383) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 35 * (5 : ZMod 175520489383) ^ 35 := by rw [pow_add]
          _ = 143999174204 := by rw [factor_3_5]; decide
      have factor_3_7 : (5 : ZMod 175520489383) ^ 141 = 156316213455 := by
        calc
          (5 : ZMod 175520489383) ^ 141 = (5 : ZMod 175520489383) ^ (70 + 70 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 70 * (5 : ZMod 175520489383) ^ 70) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 156316213455 := by rw [factor_3_6]; decide
      have factor_3_8 : (5 : ZMod 175520489383) ^ 283 = 159214156686 := by
        calc
          (5 : ZMod 175520489383) ^ 283 = (5 : ZMod 175520489383) ^ (141 + 141 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 141 * (5 : ZMod 175520489383) ^ 141) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 159214156686 := by rw [factor_3_7]; decide
      have factor_3_9 : (5 : ZMod 175520489383) ^ 567 = 30839178361 := by
        calc
          (5 : ZMod 175520489383) ^ 567 = (5 : ZMod 175520489383) ^ (283 + 283 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = ((5 : ZMod 175520489383) ^ 283 * (5 : ZMod 175520489383) ^ 283) * (5 : ZMod 175520489383) := by rw [pow_succ, pow_add]
          _ = 30839178361 := by rw [factor_3_8]; decide
      have factor_3_10 : (5 : ZMod 175520489383) ^ 1134 = 10450768709 := by
        calc
          (5 : ZMod 175520489383) ^ 1134 = (5 : ZMod 175520489383) ^ (567 + 567) :=
            congrArg (fun n : ℕ => (5 : ZMod 175520489383) ^ n) (by norm_num)
          _ = (5 : ZMod 175520489383) ^ 567 * (5 : ZMod 175520489383) ^ 567 := by rw [pow_add]
          _ = 10450768709 := by rw [factor_3_9]; decide
      change (5 : ZMod 175520489383) ^ 1134 ≠ 1
      rw [factor_3_10]
      decide

#print axioms prime_lucas_175520489383

end TotientTailPeriodKiller
end Erdos249257
