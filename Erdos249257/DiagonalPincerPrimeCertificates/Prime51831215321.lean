import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1295780383

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_51831215321 : Nat.Prime 51831215321 := by
  apply lucas_primality 51831215321 (3 : ZMod 51831215321)
  ·
      have fermat_0 : (3 : ZMod 51831215321) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 51831215321) ^ 3 = 27 := by
        calc
          (3 : ZMod 51831215321) ^ 3 = (3 : ZMod 51831215321) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 1 * (3 : ZMod 51831215321) ^ 1) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 51831215321) ^ 6 = 729 := by
        calc
          (3 : ZMod 51831215321) ^ 6 = (3 : ZMod 51831215321) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 3 * (3 : ZMod 51831215321) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 51831215321) ^ 12 = 531441 := by
        calc
          (3 : ZMod 51831215321) ^ 12 = (3 : ZMod 51831215321) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 6 * (3 : ZMod 51831215321) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 51831215321) ^ 24 = 23273459876 := by
        calc
          (3 : ZMod 51831215321) ^ 24 = (3 : ZMod 51831215321) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 12 * (3 : ZMod 51831215321) ^ 12 := by rw [pow_add]
          _ = 23273459876 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 51831215321) ^ 48 = 30360132658 := by
        calc
          (3 : ZMod 51831215321) ^ 48 = (3 : ZMod 51831215321) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 24 * (3 : ZMod 51831215321) ^ 24 := by rw [pow_add]
          _ = 30360132658 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 51831215321) ^ 96 = 5962469585 := by
        calc
          (3 : ZMod 51831215321) ^ 96 = (3 : ZMod 51831215321) ^ (48 + 48) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 48 * (3 : ZMod 51831215321) ^ 48 := by rw [pow_add]
          _ = 5962469585 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 51831215321) ^ 193 = 16717025925 := by
        calc
          (3 : ZMod 51831215321) ^ 193 = (3 : ZMod 51831215321) ^ (96 + 96 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 96 * (3 : ZMod 51831215321) ^ 96) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 16717025925 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 51831215321) ^ 386 = 11082578521 := by
        calc
          (3 : ZMod 51831215321) ^ 386 = (3 : ZMod 51831215321) ^ (193 + 193) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 193 * (3 : ZMod 51831215321) ^ 193 := by rw [pow_add]
          _ = 11082578521 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 51831215321) ^ 772 = 20321439022 := by
        calc
          (3 : ZMod 51831215321) ^ 772 = (3 : ZMod 51831215321) ^ (386 + 386) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 386 * (3 : ZMod 51831215321) ^ 386 := by rw [pow_add]
          _ = 20321439022 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 51831215321) ^ 1544 = 29428616872 := by
        calc
          (3 : ZMod 51831215321) ^ 1544 = (3 : ZMod 51831215321) ^ (772 + 772) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 772 * (3 : ZMod 51831215321) ^ 772 := by rw [pow_add]
          _ = 29428616872 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 51831215321) ^ 3089 = 7888366375 := by
        calc
          (3 : ZMod 51831215321) ^ 3089 = (3 : ZMod 51831215321) ^ (1544 + 1544 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 1544 * (3 : ZMod 51831215321) ^ 1544) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 7888366375 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 51831215321) ^ 6178 = 47918930589 := by
        calc
          (3 : ZMod 51831215321) ^ 6178 = (3 : ZMod 51831215321) ^ (3089 + 3089) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 3089 * (3 : ZMod 51831215321) ^ 3089 := by rw [pow_add]
          _ = 47918930589 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 51831215321) ^ 12357 = 45738930850 := by
        calc
          (3 : ZMod 51831215321) ^ 12357 = (3 : ZMod 51831215321) ^ (6178 + 6178 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 6178 * (3 : ZMod 51831215321) ^ 6178) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 45738930850 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 51831215321) ^ 24715 = 41393326342 := by
        calc
          (3 : ZMod 51831215321) ^ 24715 = (3 : ZMod 51831215321) ^ (12357 + 12357 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 12357 * (3 : ZMod 51831215321) ^ 12357) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 41393326342 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 51831215321) ^ 49430 = 20258721947 := by
        calc
          (3 : ZMod 51831215321) ^ 49430 = (3 : ZMod 51831215321) ^ (24715 + 24715) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 24715 * (3 : ZMod 51831215321) ^ 24715 := by rw [pow_add]
          _ = 20258721947 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 51831215321) ^ 98860 = 25630279333 := by
        calc
          (3 : ZMod 51831215321) ^ 98860 = (3 : ZMod 51831215321) ^ (49430 + 49430) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 49430 * (3 : ZMod 51831215321) ^ 49430 := by rw [pow_add]
          _ = 25630279333 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 51831215321) ^ 197720 = 18649572948 := by
        calc
          (3 : ZMod 51831215321) ^ 197720 = (3 : ZMod 51831215321) ^ (98860 + 98860) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 98860 * (3 : ZMod 51831215321) ^ 98860 := by rw [pow_add]
          _ = 18649572948 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 51831215321) ^ 395440 = 1859934805 := by
        calc
          (3 : ZMod 51831215321) ^ 395440 = (3 : ZMod 51831215321) ^ (197720 + 197720) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 197720 * (3 : ZMod 51831215321) ^ 197720 := by rw [pow_add]
          _ = 1859934805 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 51831215321) ^ 790881 = 37740882887 := by
        calc
          (3 : ZMod 51831215321) ^ 790881 = (3 : ZMod 51831215321) ^ (395440 + 395440 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 395440 * (3 : ZMod 51831215321) ^ 395440) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 37740882887 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 51831215321) ^ 1581763 = 4675497795 := by
        calc
          (3 : ZMod 51831215321) ^ 1581763 = (3 : ZMod 51831215321) ^ (790881 + 790881 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 790881 * (3 : ZMod 51831215321) ^ 790881) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 4675497795 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 51831215321) ^ 3163526 = 6235189902 := by
        calc
          (3 : ZMod 51831215321) ^ 3163526 = (3 : ZMod 51831215321) ^ (1581763 + 1581763) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 1581763 * (3 : ZMod 51831215321) ^ 1581763 := by rw [pow_add]
          _ = 6235189902 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 51831215321) ^ 6327052 = 36294317287 := by
        calc
          (3 : ZMod 51831215321) ^ 6327052 = (3 : ZMod 51831215321) ^ (3163526 + 3163526) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 3163526 * (3 : ZMod 51831215321) ^ 3163526 := by rw [pow_add]
          _ = 36294317287 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 51831215321) ^ 12654105 = 51215471069 := by
        calc
          (3 : ZMod 51831215321) ^ 12654105 = (3 : ZMod 51831215321) ^ (6327052 + 6327052 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 6327052 * (3 : ZMod 51831215321) ^ 6327052) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 51215471069 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 51831215321) ^ 25308210 = 49451226789 := by
        calc
          (3 : ZMod 51831215321) ^ 25308210 = (3 : ZMod 51831215321) ^ (12654105 + 12654105) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 12654105 * (3 : ZMod 51831215321) ^ 12654105 := by rw [pow_add]
          _ = 49451226789 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 51831215321) ^ 50616421 = 7404968068 := by
        calc
          (3 : ZMod 51831215321) ^ 50616421 = (3 : ZMod 51831215321) ^ (25308210 + 25308210 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 25308210 * (3 : ZMod 51831215321) ^ 25308210) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 7404968068 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 51831215321) ^ 101232842 = 39852313522 := by
        calc
          (3 : ZMod 51831215321) ^ 101232842 = (3 : ZMod 51831215321) ^ (50616421 + 50616421) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 50616421 * (3 : ZMod 51831215321) ^ 50616421 := by rw [pow_add]
          _ = 39852313522 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 51831215321) ^ 202465684 = 49930761502 := by
        calc
          (3 : ZMod 51831215321) ^ 202465684 = (3 : ZMod 51831215321) ^ (101232842 + 101232842) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 101232842 * (3 : ZMod 51831215321) ^ 101232842 := by rw [pow_add]
          _ = 49930761502 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 51831215321) ^ 404931369 = 38986615292 := by
        calc
          (3 : ZMod 51831215321) ^ 404931369 = (3 : ZMod 51831215321) ^ (202465684 + 202465684 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 202465684 * (3 : ZMod 51831215321) ^ 202465684) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 38986615292 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 51831215321) ^ 809862739 = 6481797092 := by
        calc
          (3 : ZMod 51831215321) ^ 809862739 = (3 : ZMod 51831215321) ^ (404931369 + 404931369 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 404931369 * (3 : ZMod 51831215321) ^ 404931369) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 6481797092 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 51831215321) ^ 1619725478 = 16976902369 := by
        calc
          (3 : ZMod 51831215321) ^ 1619725478 = (3 : ZMod 51831215321) ^ (809862739 + 809862739) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 809862739 * (3 : ZMod 51831215321) ^ 809862739 := by rw [pow_add]
          _ = 16976902369 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 51831215321) ^ 3239450957 = 8919132618 := by
        calc
          (3 : ZMod 51831215321) ^ 3239450957 = (3 : ZMod 51831215321) ^ (1619725478 + 1619725478 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 1619725478 * (3 : ZMod 51831215321) ^ 1619725478) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 8919132618 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 51831215321) ^ 6478901915 = 50997160490 := by
        calc
          (3 : ZMod 51831215321) ^ 6478901915 = (3 : ZMod 51831215321) ^ (3239450957 + 3239450957 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 3239450957 * (3 : ZMod 51831215321) ^ 3239450957) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 50997160490 := by rw [fermat_31]; decide
      have fermat_33 : (3 : ZMod 51831215321) ^ 12957803830 = 39636384482 := by
        calc
          (3 : ZMod 51831215321) ^ 12957803830 = (3 : ZMod 51831215321) ^ (6478901915 + 6478901915) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 6478901915 * (3 : ZMod 51831215321) ^ 6478901915 := by rw [pow_add]
          _ = 39636384482 := by rw [fermat_32]; decide
      have fermat_34 : (3 : ZMod 51831215321) ^ 25915607660 = 51831215320 := by
        calc
          (3 : ZMod 51831215321) ^ 25915607660 = (3 : ZMod 51831215321) ^ (12957803830 + 12957803830) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 12957803830 * (3 : ZMod 51831215321) ^ 12957803830 := by rw [pow_add]
          _ = 51831215320 := by rw [fermat_33]; decide
      have fermat_35 : (3 : ZMod 51831215321) ^ 51831215320 = 1 := by
        calc
          (3 : ZMod 51831215321) ^ 51831215320 = (3 : ZMod 51831215321) ^ (25915607660 + 25915607660) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 25915607660 * (3 : ZMod 51831215321) ^ 25915607660 := by rw [pow_add]
          _ = 1 := by rw [fermat_34]; decide
      simpa using fermat_35
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (1295780383, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (1295780383, 1)] : List FactorBlock).map factorBlockValue).prod = 51831215321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_1295780383) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 51831215321) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 51831215321) ^ 3 = 27 := by
        calc
          (3 : ZMod 51831215321) ^ 3 = (3 : ZMod 51831215321) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 1 * (3 : ZMod 51831215321) ^ 1) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 51831215321) ^ 6 = 729 := by
        calc
          (3 : ZMod 51831215321) ^ 6 = (3 : ZMod 51831215321) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 3 * (3 : ZMod 51831215321) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 51831215321) ^ 12 = 531441 := by
        calc
          (3 : ZMod 51831215321) ^ 12 = (3 : ZMod 51831215321) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 6 * (3 : ZMod 51831215321) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 51831215321) ^ 24 = 23273459876 := by
        calc
          (3 : ZMod 51831215321) ^ 24 = (3 : ZMod 51831215321) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 12 * (3 : ZMod 51831215321) ^ 12 := by rw [pow_add]
          _ = 23273459876 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 51831215321) ^ 48 = 30360132658 := by
        calc
          (3 : ZMod 51831215321) ^ 48 = (3 : ZMod 51831215321) ^ (24 + 24) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 24 * (3 : ZMod 51831215321) ^ 24 := by rw [pow_add]
          _ = 30360132658 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 51831215321) ^ 96 = 5962469585 := by
        calc
          (3 : ZMod 51831215321) ^ 96 = (3 : ZMod 51831215321) ^ (48 + 48) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 48 * (3 : ZMod 51831215321) ^ 48 := by rw [pow_add]
          _ = 5962469585 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 51831215321) ^ 193 = 16717025925 := by
        calc
          (3 : ZMod 51831215321) ^ 193 = (3 : ZMod 51831215321) ^ (96 + 96 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 96 * (3 : ZMod 51831215321) ^ 96) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 16717025925 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 51831215321) ^ 386 = 11082578521 := by
        calc
          (3 : ZMod 51831215321) ^ 386 = (3 : ZMod 51831215321) ^ (193 + 193) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 193 * (3 : ZMod 51831215321) ^ 193 := by rw [pow_add]
          _ = 11082578521 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 51831215321) ^ 772 = 20321439022 := by
        calc
          (3 : ZMod 51831215321) ^ 772 = (3 : ZMod 51831215321) ^ (386 + 386) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 386 * (3 : ZMod 51831215321) ^ 386 := by rw [pow_add]
          _ = 20321439022 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 51831215321) ^ 1544 = 29428616872 := by
        calc
          (3 : ZMod 51831215321) ^ 1544 = (3 : ZMod 51831215321) ^ (772 + 772) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 772 * (3 : ZMod 51831215321) ^ 772 := by rw [pow_add]
          _ = 29428616872 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 51831215321) ^ 3089 = 7888366375 := by
        calc
          (3 : ZMod 51831215321) ^ 3089 = (3 : ZMod 51831215321) ^ (1544 + 1544 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 1544 * (3 : ZMod 51831215321) ^ 1544) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 7888366375 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 51831215321) ^ 6178 = 47918930589 := by
        calc
          (3 : ZMod 51831215321) ^ 6178 = (3 : ZMod 51831215321) ^ (3089 + 3089) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 3089 * (3 : ZMod 51831215321) ^ 3089 := by rw [pow_add]
          _ = 47918930589 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 51831215321) ^ 12357 = 45738930850 := by
        calc
          (3 : ZMod 51831215321) ^ 12357 = (3 : ZMod 51831215321) ^ (6178 + 6178 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 6178 * (3 : ZMod 51831215321) ^ 6178) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 45738930850 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 51831215321) ^ 24715 = 41393326342 := by
        calc
          (3 : ZMod 51831215321) ^ 24715 = (3 : ZMod 51831215321) ^ (12357 + 12357 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 12357 * (3 : ZMod 51831215321) ^ 12357) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 41393326342 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 51831215321) ^ 49430 = 20258721947 := by
        calc
          (3 : ZMod 51831215321) ^ 49430 = (3 : ZMod 51831215321) ^ (24715 + 24715) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 24715 * (3 : ZMod 51831215321) ^ 24715 := by rw [pow_add]
          _ = 20258721947 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 51831215321) ^ 98860 = 25630279333 := by
        calc
          (3 : ZMod 51831215321) ^ 98860 = (3 : ZMod 51831215321) ^ (49430 + 49430) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 49430 * (3 : ZMod 51831215321) ^ 49430 := by rw [pow_add]
          _ = 25630279333 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 51831215321) ^ 197720 = 18649572948 := by
        calc
          (3 : ZMod 51831215321) ^ 197720 = (3 : ZMod 51831215321) ^ (98860 + 98860) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 98860 * (3 : ZMod 51831215321) ^ 98860 := by rw [pow_add]
          _ = 18649572948 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 51831215321) ^ 395440 = 1859934805 := by
        calc
          (3 : ZMod 51831215321) ^ 395440 = (3 : ZMod 51831215321) ^ (197720 + 197720) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 197720 * (3 : ZMod 51831215321) ^ 197720 := by rw [pow_add]
          _ = 1859934805 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 51831215321) ^ 790881 = 37740882887 := by
        calc
          (3 : ZMod 51831215321) ^ 790881 = (3 : ZMod 51831215321) ^ (395440 + 395440 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 395440 * (3 : ZMod 51831215321) ^ 395440) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 37740882887 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 51831215321) ^ 1581763 = 4675497795 := by
        calc
          (3 : ZMod 51831215321) ^ 1581763 = (3 : ZMod 51831215321) ^ (790881 + 790881 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 790881 * (3 : ZMod 51831215321) ^ 790881) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 4675497795 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 51831215321) ^ 3163526 = 6235189902 := by
        calc
          (3 : ZMod 51831215321) ^ 3163526 = (3 : ZMod 51831215321) ^ (1581763 + 1581763) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 1581763 * (3 : ZMod 51831215321) ^ 1581763 := by rw [pow_add]
          _ = 6235189902 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 51831215321) ^ 6327052 = 36294317287 := by
        calc
          (3 : ZMod 51831215321) ^ 6327052 = (3 : ZMod 51831215321) ^ (3163526 + 3163526) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 3163526 * (3 : ZMod 51831215321) ^ 3163526 := by rw [pow_add]
          _ = 36294317287 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 51831215321) ^ 12654105 = 51215471069 := by
        calc
          (3 : ZMod 51831215321) ^ 12654105 = (3 : ZMod 51831215321) ^ (6327052 + 6327052 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 6327052 * (3 : ZMod 51831215321) ^ 6327052) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 51215471069 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 51831215321) ^ 25308210 = 49451226789 := by
        calc
          (3 : ZMod 51831215321) ^ 25308210 = (3 : ZMod 51831215321) ^ (12654105 + 12654105) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 12654105 * (3 : ZMod 51831215321) ^ 12654105 := by rw [pow_add]
          _ = 49451226789 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 51831215321) ^ 50616421 = 7404968068 := by
        calc
          (3 : ZMod 51831215321) ^ 50616421 = (3 : ZMod 51831215321) ^ (25308210 + 25308210 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 25308210 * (3 : ZMod 51831215321) ^ 25308210) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 7404968068 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 51831215321) ^ 101232842 = 39852313522 := by
        calc
          (3 : ZMod 51831215321) ^ 101232842 = (3 : ZMod 51831215321) ^ (50616421 + 50616421) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 50616421 * (3 : ZMod 51831215321) ^ 50616421 := by rw [pow_add]
          _ = 39852313522 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 51831215321) ^ 202465684 = 49930761502 := by
        calc
          (3 : ZMod 51831215321) ^ 202465684 = (3 : ZMod 51831215321) ^ (101232842 + 101232842) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 101232842 * (3 : ZMod 51831215321) ^ 101232842 := by rw [pow_add]
          _ = 49930761502 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 51831215321) ^ 404931369 = 38986615292 := by
        calc
          (3 : ZMod 51831215321) ^ 404931369 = (3 : ZMod 51831215321) ^ (202465684 + 202465684 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 202465684 * (3 : ZMod 51831215321) ^ 202465684) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 38986615292 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 51831215321) ^ 809862739 = 6481797092 := by
        calc
          (3 : ZMod 51831215321) ^ 809862739 = (3 : ZMod 51831215321) ^ (404931369 + 404931369 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 404931369 * (3 : ZMod 51831215321) ^ 404931369) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 6481797092 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 51831215321) ^ 1619725478 = 16976902369 := by
        calc
          (3 : ZMod 51831215321) ^ 1619725478 = (3 : ZMod 51831215321) ^ (809862739 + 809862739) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 809862739 * (3 : ZMod 51831215321) ^ 809862739 := by rw [pow_add]
          _ = 16976902369 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 51831215321) ^ 3239450957 = 8919132618 := by
        calc
          (3 : ZMod 51831215321) ^ 3239450957 = (3 : ZMod 51831215321) ^ (1619725478 + 1619725478 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 1619725478 * (3 : ZMod 51831215321) ^ 1619725478) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 8919132618 := by rw [factor_0_30]; decide
      have factor_0_32 : (3 : ZMod 51831215321) ^ 6478901915 = 50997160490 := by
        calc
          (3 : ZMod 51831215321) ^ 6478901915 = (3 : ZMod 51831215321) ^ (3239450957 + 3239450957 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 3239450957 * (3 : ZMod 51831215321) ^ 3239450957) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 50997160490 := by rw [factor_0_31]; decide
      have factor_0_33 : (3 : ZMod 51831215321) ^ 12957803830 = 39636384482 := by
        calc
          (3 : ZMod 51831215321) ^ 12957803830 = (3 : ZMod 51831215321) ^ (6478901915 + 6478901915) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 6478901915 * (3 : ZMod 51831215321) ^ 6478901915 := by rw [pow_add]
          _ = 39636384482 := by rw [factor_0_32]; decide
      have factor_0_34 : (3 : ZMod 51831215321) ^ 25915607660 = 51831215320 := by
        calc
          (3 : ZMod 51831215321) ^ 25915607660 = (3 : ZMod 51831215321) ^ (12957803830 + 12957803830) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 12957803830 * (3 : ZMod 51831215321) ^ 12957803830 := by rw [pow_add]
          _ = 51831215320 := by rw [factor_0_33]; decide
      change (3 : ZMod 51831215321) ^ 25915607660 ≠ 1
      rw [factor_0_34]
      decide
    ·
      have factor_1_0 : (3 : ZMod 51831215321) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 51831215321) ^ 2 = 9 := by
        calc
          (3 : ZMod 51831215321) ^ 2 = (3 : ZMod 51831215321) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 1 * (3 : ZMod 51831215321) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 51831215321) ^ 4 = 81 := by
        calc
          (3 : ZMod 51831215321) ^ 4 = (3 : ZMod 51831215321) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 2 * (3 : ZMod 51831215321) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 51831215321) ^ 9 = 19683 := by
        calc
          (3 : ZMod 51831215321) ^ 9 = (3 : ZMod 51831215321) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 4 * (3 : ZMod 51831215321) ^ 4) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 51831215321) ^ 19 = 1162261467 := by
        calc
          (3 : ZMod 51831215321) ^ 19 = (3 : ZMod 51831215321) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 9 * (3 : ZMod 51831215321) ^ 9) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 1162261467 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 51831215321) ^ 38 = 46394845737 := by
        calc
          (3 : ZMod 51831215321) ^ 38 = (3 : ZMod 51831215321) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 19 * (3 : ZMod 51831215321) ^ 19 := by rw [pow_add]
          _ = 46394845737 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 51831215321) ^ 77 = 24434865237 := by
        calc
          (3 : ZMod 51831215321) ^ 77 = (3 : ZMod 51831215321) ^ (38 + 38 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 38 * (3 : ZMod 51831215321) ^ 38) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 24434865237 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 51831215321) ^ 154 = 40008656946 := by
        calc
          (3 : ZMod 51831215321) ^ 154 = (3 : ZMod 51831215321) ^ (77 + 77) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 77 * (3 : ZMod 51831215321) ^ 77 := by rw [pow_add]
          _ = 40008656946 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 51831215321) ^ 308 = 4431539573 := by
        calc
          (3 : ZMod 51831215321) ^ 308 = (3 : ZMod 51831215321) ^ (154 + 154) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 154 * (3 : ZMod 51831215321) ^ 154 := by rw [pow_add]
          _ = 4431539573 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 51831215321) ^ 617 = 30984399612 := by
        calc
          (3 : ZMod 51831215321) ^ 617 = (3 : ZMod 51831215321) ^ (308 + 308 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 308 * (3 : ZMod 51831215321) ^ 308) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 30984399612 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 51831215321) ^ 1235 = 50702199970 := by
        calc
          (3 : ZMod 51831215321) ^ 1235 = (3 : ZMod 51831215321) ^ (617 + 617 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 617 * (3 : ZMod 51831215321) ^ 617) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 50702199970 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 51831215321) ^ 2471 = 1225250548 := by
        calc
          (3 : ZMod 51831215321) ^ 2471 = (3 : ZMod 51831215321) ^ (1235 + 1235 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 1235 * (3 : ZMod 51831215321) ^ 1235) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 1225250548 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 51831215321) ^ 4943 = 50230951937 := by
        calc
          (3 : ZMod 51831215321) ^ 4943 = (3 : ZMod 51831215321) ^ (2471 + 2471 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 2471 * (3 : ZMod 51831215321) ^ 2471) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 50230951937 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 51831215321) ^ 9886 = 5543552748 := by
        calc
          (3 : ZMod 51831215321) ^ 9886 = (3 : ZMod 51831215321) ^ (4943 + 4943) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 4943 * (3 : ZMod 51831215321) ^ 4943 := by rw [pow_add]
          _ = 5543552748 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 51831215321) ^ 19772 = 42398111531 := by
        calc
          (3 : ZMod 51831215321) ^ 19772 = (3 : ZMod 51831215321) ^ (9886 + 9886) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 9886 * (3 : ZMod 51831215321) ^ 9886 := by rw [pow_add]
          _ = 42398111531 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 51831215321) ^ 39544 = 45319293537 := by
        calc
          (3 : ZMod 51831215321) ^ 39544 = (3 : ZMod 51831215321) ^ (19772 + 19772) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 19772 * (3 : ZMod 51831215321) ^ 19772 := by rw [pow_add]
          _ = 45319293537 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 51831215321) ^ 79088 = 21879676474 := by
        calc
          (3 : ZMod 51831215321) ^ 79088 = (3 : ZMod 51831215321) ^ (39544 + 39544) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 39544 * (3 : ZMod 51831215321) ^ 39544 := by rw [pow_add]
          _ = 21879676474 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 51831215321) ^ 158176 = 18166356482 := by
        calc
          (3 : ZMod 51831215321) ^ 158176 = (3 : ZMod 51831215321) ^ (79088 + 79088) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 79088 * (3 : ZMod 51831215321) ^ 79088 := by rw [pow_add]
          _ = 18166356482 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 51831215321) ^ 316352 = 21874404026 := by
        calc
          (3 : ZMod 51831215321) ^ 316352 = (3 : ZMod 51831215321) ^ (158176 + 158176) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 158176 * (3 : ZMod 51831215321) ^ 158176 := by rw [pow_add]
          _ = 21874404026 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 51831215321) ^ 632705 = 8190041328 := by
        calc
          (3 : ZMod 51831215321) ^ 632705 = (3 : ZMod 51831215321) ^ (316352 + 316352 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 316352 * (3 : ZMod 51831215321) ^ 316352) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 8190041328 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 51831215321) ^ 1265410 = 4218359774 := by
        calc
          (3 : ZMod 51831215321) ^ 1265410 = (3 : ZMod 51831215321) ^ (632705 + 632705) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 632705 * (3 : ZMod 51831215321) ^ 632705 := by rw [pow_add]
          _ = 4218359774 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 51831215321) ^ 2530821 = 34799771805 := by
        calc
          (3 : ZMod 51831215321) ^ 2530821 = (3 : ZMod 51831215321) ^ (1265410 + 1265410 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 1265410 * (3 : ZMod 51831215321) ^ 1265410) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 34799771805 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 51831215321) ^ 5061642 = 36213780271 := by
        calc
          (3 : ZMod 51831215321) ^ 5061642 = (3 : ZMod 51831215321) ^ (2530821 + 2530821) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 2530821 * (3 : ZMod 51831215321) ^ 2530821 := by rw [pow_add]
          _ = 36213780271 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 51831215321) ^ 10123284 = 37212306092 := by
        calc
          (3 : ZMod 51831215321) ^ 10123284 = (3 : ZMod 51831215321) ^ (5061642 + 5061642) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 5061642 * (3 : ZMod 51831215321) ^ 5061642 := by rw [pow_add]
          _ = 37212306092 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 51831215321) ^ 20246568 = 9390355202 := by
        calc
          (3 : ZMod 51831215321) ^ 20246568 = (3 : ZMod 51831215321) ^ (10123284 + 10123284) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 10123284 * (3 : ZMod 51831215321) ^ 10123284 := by rw [pow_add]
          _ = 9390355202 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 51831215321) ^ 40493136 = 964919376 := by
        calc
          (3 : ZMod 51831215321) ^ 40493136 = (3 : ZMod 51831215321) ^ (20246568 + 20246568) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 20246568 * (3 : ZMod 51831215321) ^ 20246568 := by rw [pow_add]
          _ = 964919376 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 51831215321) ^ 80986273 = 15039304505 := by
        calc
          (3 : ZMod 51831215321) ^ 80986273 = (3 : ZMod 51831215321) ^ (40493136 + 40493136 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 40493136 * (3 : ZMod 51831215321) ^ 40493136) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 15039304505 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 51831215321) ^ 161972547 = 33730387641 := by
        calc
          (3 : ZMod 51831215321) ^ 161972547 = (3 : ZMod 51831215321) ^ (80986273 + 80986273 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 80986273 * (3 : ZMod 51831215321) ^ 80986273) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 33730387641 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 51831215321) ^ 323945095 = 35260659082 := by
        calc
          (3 : ZMod 51831215321) ^ 323945095 = (3 : ZMod 51831215321) ^ (161972547 + 161972547 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 161972547 * (3 : ZMod 51831215321) ^ 161972547) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 35260659082 := by rw [factor_1_27]; decide
      have factor_1_29 : (3 : ZMod 51831215321) ^ 647890191 = 21957514506 := by
        calc
          (3 : ZMod 51831215321) ^ 647890191 = (3 : ZMod 51831215321) ^ (323945095 + 323945095 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 323945095 * (3 : ZMod 51831215321) ^ 323945095) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 21957514506 := by rw [factor_1_28]; decide
      have factor_1_30 : (3 : ZMod 51831215321) ^ 1295780383 = 26402238541 := by
        calc
          (3 : ZMod 51831215321) ^ 1295780383 = (3 : ZMod 51831215321) ^ (647890191 + 647890191 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 647890191 * (3 : ZMod 51831215321) ^ 647890191) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 26402238541 := by rw [factor_1_29]; decide
      have factor_1_31 : (3 : ZMod 51831215321) ^ 2591560766 = 34466897390 := by
        calc
          (3 : ZMod 51831215321) ^ 2591560766 = (3 : ZMod 51831215321) ^ (1295780383 + 1295780383) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 1295780383 * (3 : ZMod 51831215321) ^ 1295780383 := by rw [pow_add]
          _ = 34466897390 := by rw [factor_1_30]; decide
      have factor_1_32 : (3 : ZMod 51831215321) ^ 5183121532 = 34554701713 := by
        calc
          (3 : ZMod 51831215321) ^ 5183121532 = (3 : ZMod 51831215321) ^ (2591560766 + 2591560766) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 2591560766 * (3 : ZMod 51831215321) ^ 2591560766 := by rw [pow_add]
          _ = 34554701713 := by rw [factor_1_31]; decide
      have factor_1_33 : (3 : ZMod 51831215321) ^ 10366243064 = 6320643444 := by
        calc
          (3 : ZMod 51831215321) ^ 10366243064 = (3 : ZMod 51831215321) ^ (5183121532 + 5183121532) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 5183121532 * (3 : ZMod 51831215321) ^ 5183121532 := by rw [pow_add]
          _ = 6320643444 := by rw [factor_1_32]; decide
      change (3 : ZMod 51831215321) ^ 10366243064 ≠ 1
      rw [factor_1_33]
      decide
    ·
      have factor_2_0 : (3 : ZMod 51831215321) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 51831215321) ^ 2 = 9 := by
        calc
          (3 : ZMod 51831215321) ^ 2 = (3 : ZMod 51831215321) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 1 * (3 : ZMod 51831215321) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 51831215321) ^ 5 = 243 := by
        calc
          (3 : ZMod 51831215321) ^ 5 = (3 : ZMod 51831215321) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = ((3 : ZMod 51831215321) ^ 2 * (3 : ZMod 51831215321) ^ 2) * (3 : ZMod 51831215321) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 51831215321) ^ 10 = 59049 := by
        calc
          (3 : ZMod 51831215321) ^ 10 = (3 : ZMod 51831215321) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 5 * (3 : ZMod 51831215321) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 51831215321) ^ 20 = 3486784401 := by
        calc
          (3 : ZMod 51831215321) ^ 20 = (3 : ZMod 51831215321) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 10 * (3 : ZMod 51831215321) ^ 10 := by rw [pow_add]
          _ = 3486784401 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 51831215321) ^ 40 = 2903889065 := by
        calc
          (3 : ZMod 51831215321) ^ 40 = (3 : ZMod 51831215321) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (3 : ZMod 51831215321) ^ n) (by norm_num)
          _ = (3 : ZMod 51831215321) ^ 20 * (3 : ZMod 51831215321) ^ 20 := by rw [pow_add]
          _ = 2903889065 := by rw [factor_2_4]; decide
      change (3 : ZMod 51831215321) ^ 40 ≠ 1
      rw [factor_2_5]
      decide

#print axioms prime_lucas_51831215321

end TotientTailPeriodKiller
end Erdos249257
