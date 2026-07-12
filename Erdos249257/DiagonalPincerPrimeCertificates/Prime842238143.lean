import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime421119071

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_842238143 : Nat.Prime 842238143 := by
  apply lucas_primality 842238143 (5 : ZMod 842238143)
  ·
      have fermat_0 : (5 : ZMod 842238143) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 842238143) ^ 3 = 125 := by
        calc
          (5 : ZMod 842238143) ^ 3 = (5 : ZMod 842238143) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = ((5 : ZMod 842238143) ^ 1 * (5 : ZMod 842238143) ^ 1) * (5 : ZMod 842238143) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 842238143) ^ 6 = 15625 := by
        calc
          (5 : ZMod 842238143) ^ 6 = (5 : ZMod 842238143) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 3 * (5 : ZMod 842238143) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 842238143) ^ 12 = 244140625 := by
        calc
          (5 : ZMod 842238143) ^ 12 = (5 : ZMod 842238143) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 6 * (5 : ZMod 842238143) ^ 6 := by rw [pow_add]
          _ = 244140625 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 842238143) ^ 25 = 146034876 := by
        calc
          (5 : ZMod 842238143) ^ 25 = (5 : ZMod 842238143) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = ((5 : ZMod 842238143) ^ 12 * (5 : ZMod 842238143) ^ 12) * (5 : ZMod 842238143) := by rw [pow_succ, pow_add]
          _ = 146034876 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 842238143) ^ 50 = 167391969 := by
        calc
          (5 : ZMod 842238143) ^ 50 = (5 : ZMod 842238143) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 25 * (5 : ZMod 842238143) ^ 25 := by rw [pow_add]
          _ = 167391969 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 842238143) ^ 100 = 35059306 := by
        calc
          (5 : ZMod 842238143) ^ 100 = (5 : ZMod 842238143) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 50 * (5 : ZMod 842238143) ^ 50 := by rw [pow_add]
          _ = 35059306 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 842238143) ^ 200 = 171450723 := by
        calc
          (5 : ZMod 842238143) ^ 200 = (5 : ZMod 842238143) ^ (100 + 100) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 100 * (5 : ZMod 842238143) ^ 100 := by rw [pow_add]
          _ = 171450723 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 842238143) ^ 401 = 628833737 := by
        calc
          (5 : ZMod 842238143) ^ 401 = (5 : ZMod 842238143) ^ (200 + 200 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = ((5 : ZMod 842238143) ^ 200 * (5 : ZMod 842238143) ^ 200) * (5 : ZMod 842238143) := by rw [pow_succ, pow_add]
          _ = 628833737 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 842238143) ^ 803 = 523077517 := by
        calc
          (5 : ZMod 842238143) ^ 803 = (5 : ZMod 842238143) ^ (401 + 401 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = ((5 : ZMod 842238143) ^ 401 * (5 : ZMod 842238143) ^ 401) * (5 : ZMod 842238143) := by rw [pow_succ, pow_add]
          _ = 523077517 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 842238143) ^ 1606 = 86680472 := by
        calc
          (5 : ZMod 842238143) ^ 1606 = (5 : ZMod 842238143) ^ (803 + 803) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 803 * (5 : ZMod 842238143) ^ 803 := by rw [pow_add]
          _ = 86680472 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 842238143) ^ 3212 = 505493230 := by
        calc
          (5 : ZMod 842238143) ^ 3212 = (5 : ZMod 842238143) ^ (1606 + 1606) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 1606 * (5 : ZMod 842238143) ^ 1606 := by rw [pow_add]
          _ = 505493230 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 842238143) ^ 6425 = 662324092 := by
        calc
          (5 : ZMod 842238143) ^ 6425 = (5 : ZMod 842238143) ^ (3212 + 3212 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = ((5 : ZMod 842238143) ^ 3212 * (5 : ZMod 842238143) ^ 3212) * (5 : ZMod 842238143) := by rw [pow_succ, pow_add]
          _ = 662324092 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 842238143) ^ 12851 = 727939290 := by
        calc
          (5 : ZMod 842238143) ^ 12851 = (5 : ZMod 842238143) ^ (6425 + 6425 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = ((5 : ZMod 842238143) ^ 6425 * (5 : ZMod 842238143) ^ 6425) * (5 : ZMod 842238143) := by rw [pow_succ, pow_add]
          _ = 727939290 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 842238143) ^ 25703 = 432850243 := by
        calc
          (5 : ZMod 842238143) ^ 25703 = (5 : ZMod 842238143) ^ (12851 + 12851 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = ((5 : ZMod 842238143) ^ 12851 * (5 : ZMod 842238143) ^ 12851) * (5 : ZMod 842238143) := by rw [pow_succ, pow_add]
          _ = 432850243 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 842238143) ^ 51406 = 567232034 := by
        calc
          (5 : ZMod 842238143) ^ 51406 = (5 : ZMod 842238143) ^ (25703 + 25703) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 25703 * (5 : ZMod 842238143) ^ 25703 := by rw [pow_add]
          _ = 567232034 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 842238143) ^ 102812 = 317801237 := by
        calc
          (5 : ZMod 842238143) ^ 102812 = (5 : ZMod 842238143) ^ (51406 + 51406) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 51406 * (5 : ZMod 842238143) ^ 51406 := by rw [pow_add]
          _ = 317801237 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 842238143) ^ 205624 = 62134632 := by
        calc
          (5 : ZMod 842238143) ^ 205624 = (5 : ZMod 842238143) ^ (102812 + 102812) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 102812 * (5 : ZMod 842238143) ^ 102812 := by rw [pow_add]
          _ = 62134632 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 842238143) ^ 411249 = 737014211 := by
        calc
          (5 : ZMod 842238143) ^ 411249 = (5 : ZMod 842238143) ^ (205624 + 205624 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = ((5 : ZMod 842238143) ^ 205624 * (5 : ZMod 842238143) ^ 205624) * (5 : ZMod 842238143) := by rw [pow_succ, pow_add]
          _ = 737014211 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 842238143) ^ 822498 = 604090479 := by
        calc
          (5 : ZMod 842238143) ^ 822498 = (5 : ZMod 842238143) ^ (411249 + 411249) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 411249 * (5 : ZMod 842238143) ^ 411249 := by rw [pow_add]
          _ = 604090479 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 842238143) ^ 1644996 = 372531665 := by
        calc
          (5 : ZMod 842238143) ^ 1644996 = (5 : ZMod 842238143) ^ (822498 + 822498) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 822498 * (5 : ZMod 842238143) ^ 822498 := by rw [pow_add]
          _ = 372531665 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 842238143) ^ 3289992 = 38320502 := by
        calc
          (5 : ZMod 842238143) ^ 3289992 = (5 : ZMod 842238143) ^ (1644996 + 1644996) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 1644996 * (5 : ZMod 842238143) ^ 1644996 := by rw [pow_add]
          _ = 38320502 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 842238143) ^ 6579985 = 709861790 := by
        calc
          (5 : ZMod 842238143) ^ 6579985 = (5 : ZMod 842238143) ^ (3289992 + 3289992 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = ((5 : ZMod 842238143) ^ 3289992 * (5 : ZMod 842238143) ^ 3289992) * (5 : ZMod 842238143) := by rw [pow_succ, pow_add]
          _ = 709861790 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 842238143) ^ 13159970 = 679043056 := by
        calc
          (5 : ZMod 842238143) ^ 13159970 = (5 : ZMod 842238143) ^ (6579985 + 6579985) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 6579985 * (5 : ZMod 842238143) ^ 6579985 := by rw [pow_add]
          _ = 679043056 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 842238143) ^ 26319941 = 328942655 := by
        calc
          (5 : ZMod 842238143) ^ 26319941 = (5 : ZMod 842238143) ^ (13159970 + 13159970 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = ((5 : ZMod 842238143) ^ 13159970 * (5 : ZMod 842238143) ^ 13159970) * (5 : ZMod 842238143) := by rw [pow_succ, pow_add]
          _ = 328942655 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 842238143) ^ 52639883 = 761072617 := by
        calc
          (5 : ZMod 842238143) ^ 52639883 = (5 : ZMod 842238143) ^ (26319941 + 26319941 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = ((5 : ZMod 842238143) ^ 26319941 * (5 : ZMod 842238143) ^ 26319941) * (5 : ZMod 842238143) := by rw [pow_succ, pow_add]
          _ = 761072617 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 842238143) ^ 105279767 = 237403788 := by
        calc
          (5 : ZMod 842238143) ^ 105279767 = (5 : ZMod 842238143) ^ (52639883 + 52639883 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = ((5 : ZMod 842238143) ^ 52639883 * (5 : ZMod 842238143) ^ 52639883) * (5 : ZMod 842238143) := by rw [pow_succ, pow_add]
          _ = 237403788 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 842238143) ^ 210559535 = 148897860 := by
        calc
          (5 : ZMod 842238143) ^ 210559535 = (5 : ZMod 842238143) ^ (105279767 + 105279767 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = ((5 : ZMod 842238143) ^ 105279767 * (5 : ZMod 842238143) ^ 105279767) * (5 : ZMod 842238143) := by rw [pow_succ, pow_add]
          _ = 148897860 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 842238143) ^ 421119071 = 842238142 := by
        calc
          (5 : ZMod 842238143) ^ 421119071 = (5 : ZMod 842238143) ^ (210559535 + 210559535 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = ((5 : ZMod 842238143) ^ 210559535 * (5 : ZMod 842238143) ^ 210559535) * (5 : ZMod 842238143) := by rw [pow_succ, pow_add]
          _ = 842238142 := by rw [fermat_27]; decide
      have fermat_29 : (5 : ZMod 842238143) ^ 842238142 = 1 := by
        calc
          (5 : ZMod 842238143) ^ 842238142 = (5 : ZMod 842238143) ^ (421119071 + 421119071) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 421119071 * (5 : ZMod 842238143) ^ 421119071 := by rw [pow_add]
          _ = 1 := by rw [fermat_28]; decide
      simpa using fermat_29
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (421119071, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (421119071, 1)] : List FactorBlock).map factorBlockValue).prod = 842238143 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_421119071) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 842238143) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 842238143) ^ 3 = 125 := by
        calc
          (5 : ZMod 842238143) ^ 3 = (5 : ZMod 842238143) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = ((5 : ZMod 842238143) ^ 1 * (5 : ZMod 842238143) ^ 1) * (5 : ZMod 842238143) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 842238143) ^ 6 = 15625 := by
        calc
          (5 : ZMod 842238143) ^ 6 = (5 : ZMod 842238143) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 3 * (5 : ZMod 842238143) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 842238143) ^ 12 = 244140625 := by
        calc
          (5 : ZMod 842238143) ^ 12 = (5 : ZMod 842238143) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 6 * (5 : ZMod 842238143) ^ 6 := by rw [pow_add]
          _ = 244140625 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 842238143) ^ 25 = 146034876 := by
        calc
          (5 : ZMod 842238143) ^ 25 = (5 : ZMod 842238143) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = ((5 : ZMod 842238143) ^ 12 * (5 : ZMod 842238143) ^ 12) * (5 : ZMod 842238143) := by rw [pow_succ, pow_add]
          _ = 146034876 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 842238143) ^ 50 = 167391969 := by
        calc
          (5 : ZMod 842238143) ^ 50 = (5 : ZMod 842238143) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 25 * (5 : ZMod 842238143) ^ 25 := by rw [pow_add]
          _ = 167391969 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 842238143) ^ 100 = 35059306 := by
        calc
          (5 : ZMod 842238143) ^ 100 = (5 : ZMod 842238143) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 50 * (5 : ZMod 842238143) ^ 50 := by rw [pow_add]
          _ = 35059306 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 842238143) ^ 200 = 171450723 := by
        calc
          (5 : ZMod 842238143) ^ 200 = (5 : ZMod 842238143) ^ (100 + 100) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 100 * (5 : ZMod 842238143) ^ 100 := by rw [pow_add]
          _ = 171450723 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 842238143) ^ 401 = 628833737 := by
        calc
          (5 : ZMod 842238143) ^ 401 = (5 : ZMod 842238143) ^ (200 + 200 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = ((5 : ZMod 842238143) ^ 200 * (5 : ZMod 842238143) ^ 200) * (5 : ZMod 842238143) := by rw [pow_succ, pow_add]
          _ = 628833737 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 842238143) ^ 803 = 523077517 := by
        calc
          (5 : ZMod 842238143) ^ 803 = (5 : ZMod 842238143) ^ (401 + 401 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = ((5 : ZMod 842238143) ^ 401 * (5 : ZMod 842238143) ^ 401) * (5 : ZMod 842238143) := by rw [pow_succ, pow_add]
          _ = 523077517 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 842238143) ^ 1606 = 86680472 := by
        calc
          (5 : ZMod 842238143) ^ 1606 = (5 : ZMod 842238143) ^ (803 + 803) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 803 * (5 : ZMod 842238143) ^ 803 := by rw [pow_add]
          _ = 86680472 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 842238143) ^ 3212 = 505493230 := by
        calc
          (5 : ZMod 842238143) ^ 3212 = (5 : ZMod 842238143) ^ (1606 + 1606) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 1606 * (5 : ZMod 842238143) ^ 1606 := by rw [pow_add]
          _ = 505493230 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 842238143) ^ 6425 = 662324092 := by
        calc
          (5 : ZMod 842238143) ^ 6425 = (5 : ZMod 842238143) ^ (3212 + 3212 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = ((5 : ZMod 842238143) ^ 3212 * (5 : ZMod 842238143) ^ 3212) * (5 : ZMod 842238143) := by rw [pow_succ, pow_add]
          _ = 662324092 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 842238143) ^ 12851 = 727939290 := by
        calc
          (5 : ZMod 842238143) ^ 12851 = (5 : ZMod 842238143) ^ (6425 + 6425 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = ((5 : ZMod 842238143) ^ 6425 * (5 : ZMod 842238143) ^ 6425) * (5 : ZMod 842238143) := by rw [pow_succ, pow_add]
          _ = 727939290 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 842238143) ^ 25703 = 432850243 := by
        calc
          (5 : ZMod 842238143) ^ 25703 = (5 : ZMod 842238143) ^ (12851 + 12851 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = ((5 : ZMod 842238143) ^ 12851 * (5 : ZMod 842238143) ^ 12851) * (5 : ZMod 842238143) := by rw [pow_succ, pow_add]
          _ = 432850243 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 842238143) ^ 51406 = 567232034 := by
        calc
          (5 : ZMod 842238143) ^ 51406 = (5 : ZMod 842238143) ^ (25703 + 25703) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 25703 * (5 : ZMod 842238143) ^ 25703 := by rw [pow_add]
          _ = 567232034 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 842238143) ^ 102812 = 317801237 := by
        calc
          (5 : ZMod 842238143) ^ 102812 = (5 : ZMod 842238143) ^ (51406 + 51406) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 51406 * (5 : ZMod 842238143) ^ 51406 := by rw [pow_add]
          _ = 317801237 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 842238143) ^ 205624 = 62134632 := by
        calc
          (5 : ZMod 842238143) ^ 205624 = (5 : ZMod 842238143) ^ (102812 + 102812) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 102812 * (5 : ZMod 842238143) ^ 102812 := by rw [pow_add]
          _ = 62134632 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 842238143) ^ 411249 = 737014211 := by
        calc
          (5 : ZMod 842238143) ^ 411249 = (5 : ZMod 842238143) ^ (205624 + 205624 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = ((5 : ZMod 842238143) ^ 205624 * (5 : ZMod 842238143) ^ 205624) * (5 : ZMod 842238143) := by rw [pow_succ, pow_add]
          _ = 737014211 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 842238143) ^ 822498 = 604090479 := by
        calc
          (5 : ZMod 842238143) ^ 822498 = (5 : ZMod 842238143) ^ (411249 + 411249) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 411249 * (5 : ZMod 842238143) ^ 411249 := by rw [pow_add]
          _ = 604090479 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 842238143) ^ 1644996 = 372531665 := by
        calc
          (5 : ZMod 842238143) ^ 1644996 = (5 : ZMod 842238143) ^ (822498 + 822498) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 822498 * (5 : ZMod 842238143) ^ 822498 := by rw [pow_add]
          _ = 372531665 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 842238143) ^ 3289992 = 38320502 := by
        calc
          (5 : ZMod 842238143) ^ 3289992 = (5 : ZMod 842238143) ^ (1644996 + 1644996) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 1644996 * (5 : ZMod 842238143) ^ 1644996 := by rw [pow_add]
          _ = 38320502 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 842238143) ^ 6579985 = 709861790 := by
        calc
          (5 : ZMod 842238143) ^ 6579985 = (5 : ZMod 842238143) ^ (3289992 + 3289992 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = ((5 : ZMod 842238143) ^ 3289992 * (5 : ZMod 842238143) ^ 3289992) * (5 : ZMod 842238143) := by rw [pow_succ, pow_add]
          _ = 709861790 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 842238143) ^ 13159970 = 679043056 := by
        calc
          (5 : ZMod 842238143) ^ 13159970 = (5 : ZMod 842238143) ^ (6579985 + 6579985) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 6579985 * (5 : ZMod 842238143) ^ 6579985 := by rw [pow_add]
          _ = 679043056 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 842238143) ^ 26319941 = 328942655 := by
        calc
          (5 : ZMod 842238143) ^ 26319941 = (5 : ZMod 842238143) ^ (13159970 + 13159970 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = ((5 : ZMod 842238143) ^ 13159970 * (5 : ZMod 842238143) ^ 13159970) * (5 : ZMod 842238143) := by rw [pow_succ, pow_add]
          _ = 328942655 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 842238143) ^ 52639883 = 761072617 := by
        calc
          (5 : ZMod 842238143) ^ 52639883 = (5 : ZMod 842238143) ^ (26319941 + 26319941 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = ((5 : ZMod 842238143) ^ 26319941 * (5 : ZMod 842238143) ^ 26319941) * (5 : ZMod 842238143) := by rw [pow_succ, pow_add]
          _ = 761072617 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 842238143) ^ 105279767 = 237403788 := by
        calc
          (5 : ZMod 842238143) ^ 105279767 = (5 : ZMod 842238143) ^ (52639883 + 52639883 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = ((5 : ZMod 842238143) ^ 52639883 * (5 : ZMod 842238143) ^ 52639883) * (5 : ZMod 842238143) := by rw [pow_succ, pow_add]
          _ = 237403788 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 842238143) ^ 210559535 = 148897860 := by
        calc
          (5 : ZMod 842238143) ^ 210559535 = (5 : ZMod 842238143) ^ (105279767 + 105279767 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = ((5 : ZMod 842238143) ^ 105279767 * (5 : ZMod 842238143) ^ 105279767) * (5 : ZMod 842238143) := by rw [pow_succ, pow_add]
          _ = 148897860 := by rw [factor_0_26]; decide
      have factor_0_28 : (5 : ZMod 842238143) ^ 421119071 = 842238142 := by
        calc
          (5 : ZMod 842238143) ^ 421119071 = (5 : ZMod 842238143) ^ (210559535 + 210559535 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = ((5 : ZMod 842238143) ^ 210559535 * (5 : ZMod 842238143) ^ 210559535) * (5 : ZMod 842238143) := by rw [pow_succ, pow_add]
          _ = 842238142 := by rw [factor_0_27]; decide
      change (5 : ZMod 842238143) ^ 421119071 ≠ 1
      rw [factor_0_28]
      decide
    ·
      have factor_1_0 : (5 : ZMod 842238143) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 842238143) ^ 2 = 25 := by
        calc
          (5 : ZMod 842238143) ^ 2 = (5 : ZMod 842238143) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 842238143) ^ n) (by norm_num)
          _ = (5 : ZMod 842238143) ^ 1 * (5 : ZMod 842238143) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_1_0]; decide
      change (5 : ZMod 842238143) ^ 2 ≠ 1
      rw [factor_1_1]
      decide

#print axioms prime_lucas_842238143

end TotientTailPeriodKiller
end Erdos249257
