import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=32 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_426598383733 : Nat.Prime 426598383733 := by
  apply lucas_primality 426598383733 (34 : ZMod 426598383733)
  ·
      have fermat_0 : (34 : ZMod 426598383733) ^ 1 = 34 := by norm_num
      have fermat_1 : (34 : ZMod 426598383733) ^ 3 = 39304 := by
        calc
          (34 : ZMod 426598383733) ^ 3 = (34 : ZMod 426598383733) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 1 * (34 : ZMod 426598383733) ^ 1) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 39304 := by rw [fermat_0]; decide
      have fermat_2 : (34 : ZMod 426598383733) ^ 6 = 1544804416 := by
        calc
          (34 : ZMod 426598383733) ^ 6 = (34 : ZMod 426598383733) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 3 * (34 : ZMod 426598383733) ^ 3 := by rw [pow_add]
          _ = 1544804416 := by rw [fermat_1]; decide
      have fermat_3 : (34 : ZMod 426598383733) ^ 12 = 316400605212 := by
        calc
          (34 : ZMod 426598383733) ^ 12 = (34 : ZMod 426598383733) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 6 * (34 : ZMod 426598383733) ^ 6 := by rw [pow_add]
          _ = 316400605212 := by rw [fermat_2]; decide
      have fermat_4 : (34 : ZMod 426598383733) ^ 24 = 174419831799 := by
        calc
          (34 : ZMod 426598383733) ^ 24 = (34 : ZMod 426598383733) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 12 * (34 : ZMod 426598383733) ^ 12 := by rw [pow_add]
          _ = 174419831799 := by rw [fermat_3]; decide
      have fermat_5 : (34 : ZMod 426598383733) ^ 49 = 282990307355 := by
        calc
          (34 : ZMod 426598383733) ^ 49 = (34 : ZMod 426598383733) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 24 * (34 : ZMod 426598383733) ^ 24) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 282990307355 := by rw [fermat_4]; decide
      have fermat_6 : (34 : ZMod 426598383733) ^ 99 = 265259684447 := by
        calc
          (34 : ZMod 426598383733) ^ 99 = (34 : ZMod 426598383733) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 49 * (34 : ZMod 426598383733) ^ 49) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 265259684447 := by rw [fermat_5]; decide
      have fermat_7 : (34 : ZMod 426598383733) ^ 198 = 257883263776 := by
        calc
          (34 : ZMod 426598383733) ^ 198 = (34 : ZMod 426598383733) ^ (99 + 99) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 99 * (34 : ZMod 426598383733) ^ 99 := by rw [pow_add]
          _ = 257883263776 := by rw [fermat_6]; decide
      have fermat_8 : (34 : ZMod 426598383733) ^ 397 = 39505409613 := by
        calc
          (34 : ZMod 426598383733) ^ 397 = (34 : ZMod 426598383733) ^ (198 + 198 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 198 * (34 : ZMod 426598383733) ^ 198) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 39505409613 := by rw [fermat_7]; decide
      have fermat_9 : (34 : ZMod 426598383733) ^ 794 = 393867237741 := by
        calc
          (34 : ZMod 426598383733) ^ 794 = (34 : ZMod 426598383733) ^ (397 + 397) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 397 * (34 : ZMod 426598383733) ^ 397 := by rw [pow_add]
          _ = 393867237741 := by rw [fermat_8]; decide
      have fermat_10 : (34 : ZMod 426598383733) ^ 1589 = 135492247354 := by
        calc
          (34 : ZMod 426598383733) ^ 1589 = (34 : ZMod 426598383733) ^ (794 + 794 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 794 * (34 : ZMod 426598383733) ^ 794) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 135492247354 := by rw [fermat_9]; decide
      have fermat_11 : (34 : ZMod 426598383733) ^ 3178 = 145704090311 := by
        calc
          (34 : ZMod 426598383733) ^ 3178 = (34 : ZMod 426598383733) ^ (1589 + 1589) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 1589 * (34 : ZMod 426598383733) ^ 1589 := by rw [pow_add]
          _ = 145704090311 := by rw [fermat_10]; decide
      have fermat_12 : (34 : ZMod 426598383733) ^ 6356 = 276141570632 := by
        calc
          (34 : ZMod 426598383733) ^ 6356 = (34 : ZMod 426598383733) ^ (3178 + 3178) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 3178 * (34 : ZMod 426598383733) ^ 3178 := by rw [pow_add]
          _ = 276141570632 := by rw [fermat_11]; decide
      have fermat_13 : (34 : ZMod 426598383733) ^ 12713 = 29180288166 := by
        calc
          (34 : ZMod 426598383733) ^ 12713 = (34 : ZMod 426598383733) ^ (6356 + 6356 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 6356 * (34 : ZMod 426598383733) ^ 6356) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 29180288166 := by rw [fermat_12]; decide
      have fermat_14 : (34 : ZMod 426598383733) ^ 25427 = 97101318980 := by
        calc
          (34 : ZMod 426598383733) ^ 25427 = (34 : ZMod 426598383733) ^ (12713 + 12713 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 12713 * (34 : ZMod 426598383733) ^ 12713) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 97101318980 := by rw [fermat_13]; decide
      have fermat_15 : (34 : ZMod 426598383733) ^ 50854 = 415415805147 := by
        calc
          (34 : ZMod 426598383733) ^ 50854 = (34 : ZMod 426598383733) ^ (25427 + 25427) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 25427 * (34 : ZMod 426598383733) ^ 25427 := by rw [pow_add]
          _ = 415415805147 := by rw [fermat_14]; decide
      have fermat_16 : (34 : ZMod 426598383733) ^ 101708 = 239858654129 := by
        calc
          (34 : ZMod 426598383733) ^ 101708 = (34 : ZMod 426598383733) ^ (50854 + 50854) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 50854 * (34 : ZMod 426598383733) ^ 50854 := by rw [pow_add]
          _ = 239858654129 := by rw [fermat_15]; decide
      have fermat_17 : (34 : ZMod 426598383733) ^ 203417 = 417014527638 := by
        calc
          (34 : ZMod 426598383733) ^ 203417 = (34 : ZMod 426598383733) ^ (101708 + 101708 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 101708 * (34 : ZMod 426598383733) ^ 101708) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 417014527638 := by rw [fermat_16]; decide
      have fermat_18 : (34 : ZMod 426598383733) ^ 406835 = 342021487167 := by
        calc
          (34 : ZMod 426598383733) ^ 406835 = (34 : ZMod 426598383733) ^ (203417 + 203417 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 203417 * (34 : ZMod 426598383733) ^ 203417) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 342021487167 := by rw [fermat_17]; decide
      have fermat_19 : (34 : ZMod 426598383733) ^ 813671 = 200249460316 := by
        calc
          (34 : ZMod 426598383733) ^ 813671 = (34 : ZMod 426598383733) ^ (406835 + 406835 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 406835 * (34 : ZMod 426598383733) ^ 406835) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 200249460316 := by rw [fermat_18]; decide
      have fermat_20 : (34 : ZMod 426598383733) ^ 1627343 = 225043204733 := by
        calc
          (34 : ZMod 426598383733) ^ 1627343 = (34 : ZMod 426598383733) ^ (813671 + 813671 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 813671 * (34 : ZMod 426598383733) ^ 813671) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 225043204733 := by rw [fermat_19]; decide
      have fermat_21 : (34 : ZMod 426598383733) ^ 3254687 = 317856677985 := by
        calc
          (34 : ZMod 426598383733) ^ 3254687 = (34 : ZMod 426598383733) ^ (1627343 + 1627343 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 1627343 * (34 : ZMod 426598383733) ^ 1627343) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 317856677985 := by rw [fermat_20]; decide
      have fermat_22 : (34 : ZMod 426598383733) ^ 6509374 = 37051215353 := by
        calc
          (34 : ZMod 426598383733) ^ 6509374 = (34 : ZMod 426598383733) ^ (3254687 + 3254687) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 3254687 * (34 : ZMod 426598383733) ^ 3254687 := by rw [pow_add]
          _ = 37051215353 := by rw [fermat_21]; decide
      have fermat_23 : (34 : ZMod 426598383733) ^ 13018749 = 75689515484 := by
        calc
          (34 : ZMod 426598383733) ^ 13018749 = (34 : ZMod 426598383733) ^ (6509374 + 6509374 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 6509374 * (34 : ZMod 426598383733) ^ 6509374) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 75689515484 := by rw [fermat_22]; decide
      have fermat_24 : (34 : ZMod 426598383733) ^ 26037499 = 128352897649 := by
        calc
          (34 : ZMod 426598383733) ^ 26037499 = (34 : ZMod 426598383733) ^ (13018749 + 13018749 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 13018749 * (34 : ZMod 426598383733) ^ 13018749) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 128352897649 := by rw [fermat_23]; decide
      have fermat_25 : (34 : ZMod 426598383733) ^ 52074998 = 211678554287 := by
        calc
          (34 : ZMod 426598383733) ^ 52074998 = (34 : ZMod 426598383733) ^ (26037499 + 26037499) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 26037499 * (34 : ZMod 426598383733) ^ 26037499 := by rw [pow_add]
          _ = 211678554287 := by rw [fermat_24]; decide
      have fermat_26 : (34 : ZMod 426598383733) ^ 104149996 = 59414119142 := by
        calc
          (34 : ZMod 426598383733) ^ 104149996 = (34 : ZMod 426598383733) ^ (52074998 + 52074998) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 52074998 * (34 : ZMod 426598383733) ^ 52074998 := by rw [pow_add]
          _ = 59414119142 := by rw [fermat_25]; decide
      have fermat_27 : (34 : ZMod 426598383733) ^ 208299992 = 120243826633 := by
        calc
          (34 : ZMod 426598383733) ^ 208299992 = (34 : ZMod 426598383733) ^ (104149996 + 104149996) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 104149996 * (34 : ZMod 426598383733) ^ 104149996 := by rw [pow_add]
          _ = 120243826633 := by rw [fermat_26]; decide
      have fermat_28 : (34 : ZMod 426598383733) ^ 416599984 = 35085626538 := by
        calc
          (34 : ZMod 426598383733) ^ 416599984 = (34 : ZMod 426598383733) ^ (208299992 + 208299992) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 208299992 * (34 : ZMod 426598383733) ^ 208299992 := by rw [pow_add]
          _ = 35085626538 := by rw [fermat_27]; decide
      have fermat_29 : (34 : ZMod 426598383733) ^ 833199968 = 167559383593 := by
        calc
          (34 : ZMod 426598383733) ^ 833199968 = (34 : ZMod 426598383733) ^ (416599984 + 416599984) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 416599984 * (34 : ZMod 426598383733) ^ 416599984 := by rw [pow_add]
          _ = 167559383593 := by rw [fermat_28]; decide
      have fermat_30 : (34 : ZMod 426598383733) ^ 1666399936 = 129655433366 := by
        calc
          (34 : ZMod 426598383733) ^ 1666399936 = (34 : ZMod 426598383733) ^ (833199968 + 833199968) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 833199968 * (34 : ZMod 426598383733) ^ 833199968 := by rw [pow_add]
          _ = 129655433366 := by rw [fermat_29]; decide
      have fermat_31 : (34 : ZMod 426598383733) ^ 3332799872 = 234387380300 := by
        calc
          (34 : ZMod 426598383733) ^ 3332799872 = (34 : ZMod 426598383733) ^ (1666399936 + 1666399936) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 1666399936 * (34 : ZMod 426598383733) ^ 1666399936 := by rw [pow_add]
          _ = 234387380300 := by rw [fermat_30]; decide
      have fermat_32 : (34 : ZMod 426598383733) ^ 6665599745 = 185409126837 := by
        calc
          (34 : ZMod 426598383733) ^ 6665599745 = (34 : ZMod 426598383733) ^ (3332799872 + 3332799872 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 3332799872 * (34 : ZMod 426598383733) ^ 3332799872) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 185409126837 := by rw [fermat_31]; decide
      have fermat_33 : (34 : ZMod 426598383733) ^ 13331199491 = 120778840750 := by
        calc
          (34 : ZMod 426598383733) ^ 13331199491 = (34 : ZMod 426598383733) ^ (6665599745 + 6665599745 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 6665599745 * (34 : ZMod 426598383733) ^ 6665599745) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 120778840750 := by rw [fermat_32]; decide
      have fermat_34 : (34 : ZMod 426598383733) ^ 26662398983 = 387392832833 := by
        calc
          (34 : ZMod 426598383733) ^ 26662398983 = (34 : ZMod 426598383733) ^ (13331199491 + 13331199491 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 13331199491 * (34 : ZMod 426598383733) ^ 13331199491) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 387392832833 := by rw [fermat_33]; decide
      have fermat_35 : (34 : ZMod 426598383733) ^ 53324797966 = 397555736094 := by
        calc
          (34 : ZMod 426598383733) ^ 53324797966 = (34 : ZMod 426598383733) ^ (26662398983 + 26662398983) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 26662398983 * (34 : ZMod 426598383733) ^ 26662398983 := by rw [pow_add]
          _ = 397555736094 := by rw [fermat_34]; decide
      have fermat_36 : (34 : ZMod 426598383733) ^ 106649595933 = 135738375677 := by
        calc
          (34 : ZMod 426598383733) ^ 106649595933 = (34 : ZMod 426598383733) ^ (53324797966 + 53324797966 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 53324797966 * (34 : ZMod 426598383733) ^ 53324797966) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 135738375677 := by rw [fermat_35]; decide
      have fermat_37 : (34 : ZMod 426598383733) ^ 213299191866 = 426598383732 := by
        calc
          (34 : ZMod 426598383733) ^ 213299191866 = (34 : ZMod 426598383733) ^ (106649595933 + 106649595933) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 106649595933 * (34 : ZMod 426598383733) ^ 106649595933 := by rw [pow_add]
          _ = 426598383732 := by rw [fermat_36]; decide
      have fermat_38 : (34 : ZMod 426598383733) ^ 426598383732 = 1 := by
        calc
          (34 : ZMod 426598383733) ^ 426598383732 = (34 : ZMod 426598383733) ^ (213299191866 + 213299191866) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 213299191866 * (34 : ZMod 426598383733) ^ 213299191866 := by rw [pow_add]
          _ = 1 := by rw [fermat_37]; decide
      simpa using fermat_38
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (47, 1), (547, 1), (1382779, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (47, 1), (547, 1), (1382779, 1)] : List FactorBlock).map factorBlockValue).prod = 426598383733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (34 : ZMod 426598383733) ^ 1 = 34 := by norm_num
      have factor_0_1 : (34 : ZMod 426598383733) ^ 3 = 39304 := by
        calc
          (34 : ZMod 426598383733) ^ 3 = (34 : ZMod 426598383733) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 1 * (34 : ZMod 426598383733) ^ 1) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 39304 := by rw [factor_0_0]; decide
      have factor_0_2 : (34 : ZMod 426598383733) ^ 6 = 1544804416 := by
        calc
          (34 : ZMod 426598383733) ^ 6 = (34 : ZMod 426598383733) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 3 * (34 : ZMod 426598383733) ^ 3 := by rw [pow_add]
          _ = 1544804416 := by rw [factor_0_1]; decide
      have factor_0_3 : (34 : ZMod 426598383733) ^ 12 = 316400605212 := by
        calc
          (34 : ZMod 426598383733) ^ 12 = (34 : ZMod 426598383733) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 6 * (34 : ZMod 426598383733) ^ 6 := by rw [pow_add]
          _ = 316400605212 := by rw [factor_0_2]; decide
      have factor_0_4 : (34 : ZMod 426598383733) ^ 24 = 174419831799 := by
        calc
          (34 : ZMod 426598383733) ^ 24 = (34 : ZMod 426598383733) ^ (12 + 12) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 12 * (34 : ZMod 426598383733) ^ 12 := by rw [pow_add]
          _ = 174419831799 := by rw [factor_0_3]; decide
      have factor_0_5 : (34 : ZMod 426598383733) ^ 49 = 282990307355 := by
        calc
          (34 : ZMod 426598383733) ^ 49 = (34 : ZMod 426598383733) ^ (24 + 24 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 24 * (34 : ZMod 426598383733) ^ 24) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 282990307355 := by rw [factor_0_4]; decide
      have factor_0_6 : (34 : ZMod 426598383733) ^ 99 = 265259684447 := by
        calc
          (34 : ZMod 426598383733) ^ 99 = (34 : ZMod 426598383733) ^ (49 + 49 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 49 * (34 : ZMod 426598383733) ^ 49) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 265259684447 := by rw [factor_0_5]; decide
      have factor_0_7 : (34 : ZMod 426598383733) ^ 198 = 257883263776 := by
        calc
          (34 : ZMod 426598383733) ^ 198 = (34 : ZMod 426598383733) ^ (99 + 99) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 99 * (34 : ZMod 426598383733) ^ 99 := by rw [pow_add]
          _ = 257883263776 := by rw [factor_0_6]; decide
      have factor_0_8 : (34 : ZMod 426598383733) ^ 397 = 39505409613 := by
        calc
          (34 : ZMod 426598383733) ^ 397 = (34 : ZMod 426598383733) ^ (198 + 198 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 198 * (34 : ZMod 426598383733) ^ 198) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 39505409613 := by rw [factor_0_7]; decide
      have factor_0_9 : (34 : ZMod 426598383733) ^ 794 = 393867237741 := by
        calc
          (34 : ZMod 426598383733) ^ 794 = (34 : ZMod 426598383733) ^ (397 + 397) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 397 * (34 : ZMod 426598383733) ^ 397 := by rw [pow_add]
          _ = 393867237741 := by rw [factor_0_8]; decide
      have factor_0_10 : (34 : ZMod 426598383733) ^ 1589 = 135492247354 := by
        calc
          (34 : ZMod 426598383733) ^ 1589 = (34 : ZMod 426598383733) ^ (794 + 794 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 794 * (34 : ZMod 426598383733) ^ 794) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 135492247354 := by rw [factor_0_9]; decide
      have factor_0_11 : (34 : ZMod 426598383733) ^ 3178 = 145704090311 := by
        calc
          (34 : ZMod 426598383733) ^ 3178 = (34 : ZMod 426598383733) ^ (1589 + 1589) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 1589 * (34 : ZMod 426598383733) ^ 1589 := by rw [pow_add]
          _ = 145704090311 := by rw [factor_0_10]; decide
      have factor_0_12 : (34 : ZMod 426598383733) ^ 6356 = 276141570632 := by
        calc
          (34 : ZMod 426598383733) ^ 6356 = (34 : ZMod 426598383733) ^ (3178 + 3178) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 3178 * (34 : ZMod 426598383733) ^ 3178 := by rw [pow_add]
          _ = 276141570632 := by rw [factor_0_11]; decide
      have factor_0_13 : (34 : ZMod 426598383733) ^ 12713 = 29180288166 := by
        calc
          (34 : ZMod 426598383733) ^ 12713 = (34 : ZMod 426598383733) ^ (6356 + 6356 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 6356 * (34 : ZMod 426598383733) ^ 6356) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 29180288166 := by rw [factor_0_12]; decide
      have factor_0_14 : (34 : ZMod 426598383733) ^ 25427 = 97101318980 := by
        calc
          (34 : ZMod 426598383733) ^ 25427 = (34 : ZMod 426598383733) ^ (12713 + 12713 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 12713 * (34 : ZMod 426598383733) ^ 12713) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 97101318980 := by rw [factor_0_13]; decide
      have factor_0_15 : (34 : ZMod 426598383733) ^ 50854 = 415415805147 := by
        calc
          (34 : ZMod 426598383733) ^ 50854 = (34 : ZMod 426598383733) ^ (25427 + 25427) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 25427 * (34 : ZMod 426598383733) ^ 25427 := by rw [pow_add]
          _ = 415415805147 := by rw [factor_0_14]; decide
      have factor_0_16 : (34 : ZMod 426598383733) ^ 101708 = 239858654129 := by
        calc
          (34 : ZMod 426598383733) ^ 101708 = (34 : ZMod 426598383733) ^ (50854 + 50854) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 50854 * (34 : ZMod 426598383733) ^ 50854 := by rw [pow_add]
          _ = 239858654129 := by rw [factor_0_15]; decide
      have factor_0_17 : (34 : ZMod 426598383733) ^ 203417 = 417014527638 := by
        calc
          (34 : ZMod 426598383733) ^ 203417 = (34 : ZMod 426598383733) ^ (101708 + 101708 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 101708 * (34 : ZMod 426598383733) ^ 101708) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 417014527638 := by rw [factor_0_16]; decide
      have factor_0_18 : (34 : ZMod 426598383733) ^ 406835 = 342021487167 := by
        calc
          (34 : ZMod 426598383733) ^ 406835 = (34 : ZMod 426598383733) ^ (203417 + 203417 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 203417 * (34 : ZMod 426598383733) ^ 203417) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 342021487167 := by rw [factor_0_17]; decide
      have factor_0_19 : (34 : ZMod 426598383733) ^ 813671 = 200249460316 := by
        calc
          (34 : ZMod 426598383733) ^ 813671 = (34 : ZMod 426598383733) ^ (406835 + 406835 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 406835 * (34 : ZMod 426598383733) ^ 406835) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 200249460316 := by rw [factor_0_18]; decide
      have factor_0_20 : (34 : ZMod 426598383733) ^ 1627343 = 225043204733 := by
        calc
          (34 : ZMod 426598383733) ^ 1627343 = (34 : ZMod 426598383733) ^ (813671 + 813671 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 813671 * (34 : ZMod 426598383733) ^ 813671) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 225043204733 := by rw [factor_0_19]; decide
      have factor_0_21 : (34 : ZMod 426598383733) ^ 3254687 = 317856677985 := by
        calc
          (34 : ZMod 426598383733) ^ 3254687 = (34 : ZMod 426598383733) ^ (1627343 + 1627343 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 1627343 * (34 : ZMod 426598383733) ^ 1627343) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 317856677985 := by rw [factor_0_20]; decide
      have factor_0_22 : (34 : ZMod 426598383733) ^ 6509374 = 37051215353 := by
        calc
          (34 : ZMod 426598383733) ^ 6509374 = (34 : ZMod 426598383733) ^ (3254687 + 3254687) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 3254687 * (34 : ZMod 426598383733) ^ 3254687 := by rw [pow_add]
          _ = 37051215353 := by rw [factor_0_21]; decide
      have factor_0_23 : (34 : ZMod 426598383733) ^ 13018749 = 75689515484 := by
        calc
          (34 : ZMod 426598383733) ^ 13018749 = (34 : ZMod 426598383733) ^ (6509374 + 6509374 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 6509374 * (34 : ZMod 426598383733) ^ 6509374) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 75689515484 := by rw [factor_0_22]; decide
      have factor_0_24 : (34 : ZMod 426598383733) ^ 26037499 = 128352897649 := by
        calc
          (34 : ZMod 426598383733) ^ 26037499 = (34 : ZMod 426598383733) ^ (13018749 + 13018749 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 13018749 * (34 : ZMod 426598383733) ^ 13018749) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 128352897649 := by rw [factor_0_23]; decide
      have factor_0_25 : (34 : ZMod 426598383733) ^ 52074998 = 211678554287 := by
        calc
          (34 : ZMod 426598383733) ^ 52074998 = (34 : ZMod 426598383733) ^ (26037499 + 26037499) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 26037499 * (34 : ZMod 426598383733) ^ 26037499 := by rw [pow_add]
          _ = 211678554287 := by rw [factor_0_24]; decide
      have factor_0_26 : (34 : ZMod 426598383733) ^ 104149996 = 59414119142 := by
        calc
          (34 : ZMod 426598383733) ^ 104149996 = (34 : ZMod 426598383733) ^ (52074998 + 52074998) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 52074998 * (34 : ZMod 426598383733) ^ 52074998 := by rw [pow_add]
          _ = 59414119142 := by rw [factor_0_25]; decide
      have factor_0_27 : (34 : ZMod 426598383733) ^ 208299992 = 120243826633 := by
        calc
          (34 : ZMod 426598383733) ^ 208299992 = (34 : ZMod 426598383733) ^ (104149996 + 104149996) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 104149996 * (34 : ZMod 426598383733) ^ 104149996 := by rw [pow_add]
          _ = 120243826633 := by rw [factor_0_26]; decide
      have factor_0_28 : (34 : ZMod 426598383733) ^ 416599984 = 35085626538 := by
        calc
          (34 : ZMod 426598383733) ^ 416599984 = (34 : ZMod 426598383733) ^ (208299992 + 208299992) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 208299992 * (34 : ZMod 426598383733) ^ 208299992 := by rw [pow_add]
          _ = 35085626538 := by rw [factor_0_27]; decide
      have factor_0_29 : (34 : ZMod 426598383733) ^ 833199968 = 167559383593 := by
        calc
          (34 : ZMod 426598383733) ^ 833199968 = (34 : ZMod 426598383733) ^ (416599984 + 416599984) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 416599984 * (34 : ZMod 426598383733) ^ 416599984 := by rw [pow_add]
          _ = 167559383593 := by rw [factor_0_28]; decide
      have factor_0_30 : (34 : ZMod 426598383733) ^ 1666399936 = 129655433366 := by
        calc
          (34 : ZMod 426598383733) ^ 1666399936 = (34 : ZMod 426598383733) ^ (833199968 + 833199968) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 833199968 * (34 : ZMod 426598383733) ^ 833199968 := by rw [pow_add]
          _ = 129655433366 := by rw [factor_0_29]; decide
      have factor_0_31 : (34 : ZMod 426598383733) ^ 3332799872 = 234387380300 := by
        calc
          (34 : ZMod 426598383733) ^ 3332799872 = (34 : ZMod 426598383733) ^ (1666399936 + 1666399936) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 1666399936 * (34 : ZMod 426598383733) ^ 1666399936 := by rw [pow_add]
          _ = 234387380300 := by rw [factor_0_30]; decide
      have factor_0_32 : (34 : ZMod 426598383733) ^ 6665599745 = 185409126837 := by
        calc
          (34 : ZMod 426598383733) ^ 6665599745 = (34 : ZMod 426598383733) ^ (3332799872 + 3332799872 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 3332799872 * (34 : ZMod 426598383733) ^ 3332799872) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 185409126837 := by rw [factor_0_31]; decide
      have factor_0_33 : (34 : ZMod 426598383733) ^ 13331199491 = 120778840750 := by
        calc
          (34 : ZMod 426598383733) ^ 13331199491 = (34 : ZMod 426598383733) ^ (6665599745 + 6665599745 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 6665599745 * (34 : ZMod 426598383733) ^ 6665599745) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 120778840750 := by rw [factor_0_32]; decide
      have factor_0_34 : (34 : ZMod 426598383733) ^ 26662398983 = 387392832833 := by
        calc
          (34 : ZMod 426598383733) ^ 26662398983 = (34 : ZMod 426598383733) ^ (13331199491 + 13331199491 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 13331199491 * (34 : ZMod 426598383733) ^ 13331199491) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 387392832833 := by rw [factor_0_33]; decide
      have factor_0_35 : (34 : ZMod 426598383733) ^ 53324797966 = 397555736094 := by
        calc
          (34 : ZMod 426598383733) ^ 53324797966 = (34 : ZMod 426598383733) ^ (26662398983 + 26662398983) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 26662398983 * (34 : ZMod 426598383733) ^ 26662398983 := by rw [pow_add]
          _ = 397555736094 := by rw [factor_0_34]; decide
      have factor_0_36 : (34 : ZMod 426598383733) ^ 106649595933 = 135738375677 := by
        calc
          (34 : ZMod 426598383733) ^ 106649595933 = (34 : ZMod 426598383733) ^ (53324797966 + 53324797966 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 53324797966 * (34 : ZMod 426598383733) ^ 53324797966) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 135738375677 := by rw [factor_0_35]; decide
      have factor_0_37 : (34 : ZMod 426598383733) ^ 213299191866 = 426598383732 := by
        calc
          (34 : ZMod 426598383733) ^ 213299191866 = (34 : ZMod 426598383733) ^ (106649595933 + 106649595933) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 106649595933 * (34 : ZMod 426598383733) ^ 106649595933 := by rw [pow_add]
          _ = 426598383732 := by rw [factor_0_36]; decide
      change (34 : ZMod 426598383733) ^ 213299191866 ≠ 1
      rw [factor_0_37]
      decide
    ·
      have factor_1_0 : (34 : ZMod 426598383733) ^ 1 = 34 := by norm_num
      have factor_1_1 : (34 : ZMod 426598383733) ^ 2 = 1156 := by
        calc
          (34 : ZMod 426598383733) ^ 2 = (34 : ZMod 426598383733) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 1 * (34 : ZMod 426598383733) ^ 1 := by rw [pow_add]
          _ = 1156 := by rw [factor_1_0]; decide
      have factor_1_2 : (34 : ZMod 426598383733) ^ 4 = 1336336 := by
        calc
          (34 : ZMod 426598383733) ^ 4 = (34 : ZMod 426598383733) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 2 * (34 : ZMod 426598383733) ^ 2 := by rw [pow_add]
          _ = 1336336 := by rw [factor_1_1]; decide
      have factor_1_3 : (34 : ZMod 426598383733) ^ 8 = 79400369964 := by
        calc
          (34 : ZMod 426598383733) ^ 8 = (34 : ZMod 426598383733) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 4 * (34 : ZMod 426598383733) ^ 4 := by rw [pow_add]
          _ = 79400369964 := by rw [factor_1_2]; decide
      have factor_1_4 : (34 : ZMod 426598383733) ^ 16 = 76908608811 := by
        calc
          (34 : ZMod 426598383733) ^ 16 = (34 : ZMod 426598383733) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 8 * (34 : ZMod 426598383733) ^ 8 := by rw [pow_add]
          _ = 76908608811 := by rw [factor_1_3]; decide
      have factor_1_5 : (34 : ZMod 426598383733) ^ 33 = 351492485342 := by
        calc
          (34 : ZMod 426598383733) ^ 33 = (34 : ZMod 426598383733) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 16 * (34 : ZMod 426598383733) ^ 16) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 351492485342 := by rw [factor_1_4]; decide
      have factor_1_6 : (34 : ZMod 426598383733) ^ 66 = 303990181586 := by
        calc
          (34 : ZMod 426598383733) ^ 66 = (34 : ZMod 426598383733) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 33 * (34 : ZMod 426598383733) ^ 33 := by rw [pow_add]
          _ = 303990181586 := by rw [factor_1_5]; decide
      have factor_1_7 : (34 : ZMod 426598383733) ^ 132 = 30483763047 := by
        calc
          (34 : ZMod 426598383733) ^ 132 = (34 : ZMod 426598383733) ^ (66 + 66) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 66 * (34 : ZMod 426598383733) ^ 66 := by rw [pow_add]
          _ = 30483763047 := by rw [factor_1_6]; decide
      have factor_1_8 : (34 : ZMod 426598383733) ^ 264 = 334732192372 := by
        calc
          (34 : ZMod 426598383733) ^ 264 = (34 : ZMod 426598383733) ^ (132 + 132) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 132 * (34 : ZMod 426598383733) ^ 132 := by rw [pow_add]
          _ = 334732192372 := by rw [factor_1_7]; decide
      have factor_1_9 : (34 : ZMod 426598383733) ^ 529 = 114234881446 := by
        calc
          (34 : ZMod 426598383733) ^ 529 = (34 : ZMod 426598383733) ^ (264 + 264 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 264 * (34 : ZMod 426598383733) ^ 264) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 114234881446 := by rw [factor_1_8]; decide
      have factor_1_10 : (34 : ZMod 426598383733) ^ 1059 = 285735335065 := by
        calc
          (34 : ZMod 426598383733) ^ 1059 = (34 : ZMod 426598383733) ^ (529 + 529 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 529 * (34 : ZMod 426598383733) ^ 529) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 285735335065 := by rw [factor_1_9]; decide
      have factor_1_11 : (34 : ZMod 426598383733) ^ 2118 = 169251425591 := by
        calc
          (34 : ZMod 426598383733) ^ 2118 = (34 : ZMod 426598383733) ^ (1059 + 1059) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 1059 * (34 : ZMod 426598383733) ^ 1059 := by rw [pow_add]
          _ = 169251425591 := by rw [factor_1_10]; decide
      have factor_1_12 : (34 : ZMod 426598383733) ^ 4237 = 353496142842 := by
        calc
          (34 : ZMod 426598383733) ^ 4237 = (34 : ZMod 426598383733) ^ (2118 + 2118 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 2118 * (34 : ZMod 426598383733) ^ 2118) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 353496142842 := by rw [factor_1_11]; decide
      have factor_1_13 : (34 : ZMod 426598383733) ^ 8475 = 227159960922 := by
        calc
          (34 : ZMod 426598383733) ^ 8475 = (34 : ZMod 426598383733) ^ (4237 + 4237 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 4237 * (34 : ZMod 426598383733) ^ 4237) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 227159960922 := by rw [factor_1_12]; decide
      have factor_1_14 : (34 : ZMod 426598383733) ^ 16951 = 318798287340 := by
        calc
          (34 : ZMod 426598383733) ^ 16951 = (34 : ZMod 426598383733) ^ (8475 + 8475 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 8475 * (34 : ZMod 426598383733) ^ 8475) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 318798287340 := by rw [factor_1_13]; decide
      have factor_1_15 : (34 : ZMod 426598383733) ^ 33902 = 216431870988 := by
        calc
          (34 : ZMod 426598383733) ^ 33902 = (34 : ZMod 426598383733) ^ (16951 + 16951) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 16951 * (34 : ZMod 426598383733) ^ 16951 := by rw [pow_add]
          _ = 216431870988 := by rw [factor_1_14]; decide
      have factor_1_16 : (34 : ZMod 426598383733) ^ 67805 = 207650004809 := by
        calc
          (34 : ZMod 426598383733) ^ 67805 = (34 : ZMod 426598383733) ^ (33902 + 33902 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 33902 * (34 : ZMod 426598383733) ^ 33902) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 207650004809 := by rw [factor_1_15]; decide
      have factor_1_17 : (34 : ZMod 426598383733) ^ 135611 = 195147971112 := by
        calc
          (34 : ZMod 426598383733) ^ 135611 = (34 : ZMod 426598383733) ^ (67805 + 67805 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 67805 * (34 : ZMod 426598383733) ^ 67805) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 195147971112 := by rw [factor_1_16]; decide
      have factor_1_18 : (34 : ZMod 426598383733) ^ 271223 = 228979755717 := by
        calc
          (34 : ZMod 426598383733) ^ 271223 = (34 : ZMod 426598383733) ^ (135611 + 135611 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 135611 * (34 : ZMod 426598383733) ^ 135611) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 228979755717 := by rw [factor_1_17]; decide
      have factor_1_19 : (34 : ZMod 426598383733) ^ 542447 = 95248373011 := by
        calc
          (34 : ZMod 426598383733) ^ 542447 = (34 : ZMod 426598383733) ^ (271223 + 271223 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 271223 * (34 : ZMod 426598383733) ^ 271223) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 95248373011 := by rw [factor_1_18]; decide
      have factor_1_20 : (34 : ZMod 426598383733) ^ 1084895 = 86548178806 := by
        calc
          (34 : ZMod 426598383733) ^ 1084895 = (34 : ZMod 426598383733) ^ (542447 + 542447 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 542447 * (34 : ZMod 426598383733) ^ 542447) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 86548178806 := by rw [factor_1_19]; decide
      have factor_1_21 : (34 : ZMod 426598383733) ^ 2169791 = 125136410987 := by
        calc
          (34 : ZMod 426598383733) ^ 2169791 = (34 : ZMod 426598383733) ^ (1084895 + 1084895 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 1084895 * (34 : ZMod 426598383733) ^ 1084895) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 125136410987 := by rw [factor_1_20]; decide
      have factor_1_22 : (34 : ZMod 426598383733) ^ 4339583 = 83854321176 := by
        calc
          (34 : ZMod 426598383733) ^ 4339583 = (34 : ZMod 426598383733) ^ (2169791 + 2169791 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 2169791 * (34 : ZMod 426598383733) ^ 2169791) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 83854321176 := by rw [factor_1_21]; decide
      have factor_1_23 : (34 : ZMod 426598383733) ^ 8679166 = 228634848637 := by
        calc
          (34 : ZMod 426598383733) ^ 8679166 = (34 : ZMod 426598383733) ^ (4339583 + 4339583) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 4339583 * (34 : ZMod 426598383733) ^ 4339583 := by rw [pow_add]
          _ = 228634848637 := by rw [factor_1_22]; decide
      have factor_1_24 : (34 : ZMod 426598383733) ^ 17358332 = 272526031105 := by
        calc
          (34 : ZMod 426598383733) ^ 17358332 = (34 : ZMod 426598383733) ^ (8679166 + 8679166) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 8679166 * (34 : ZMod 426598383733) ^ 8679166 := by rw [pow_add]
          _ = 272526031105 := by rw [factor_1_23]; decide
      have factor_1_25 : (34 : ZMod 426598383733) ^ 34716665 = 296599072170 := by
        calc
          (34 : ZMod 426598383733) ^ 34716665 = (34 : ZMod 426598383733) ^ (17358332 + 17358332 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 17358332 * (34 : ZMod 426598383733) ^ 17358332) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 296599072170 := by rw [factor_1_24]; decide
      have factor_1_26 : (34 : ZMod 426598383733) ^ 69433330 = 191463657983 := by
        calc
          (34 : ZMod 426598383733) ^ 69433330 = (34 : ZMod 426598383733) ^ (34716665 + 34716665) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 34716665 * (34 : ZMod 426598383733) ^ 34716665 := by rw [pow_add]
          _ = 191463657983 := by rw [factor_1_25]; decide
      have factor_1_27 : (34 : ZMod 426598383733) ^ 138866661 = 73482885475 := by
        calc
          (34 : ZMod 426598383733) ^ 138866661 = (34 : ZMod 426598383733) ^ (69433330 + 69433330 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 69433330 * (34 : ZMod 426598383733) ^ 69433330) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 73482885475 := by rw [factor_1_26]; decide
      have factor_1_28 : (34 : ZMod 426598383733) ^ 277733322 = 182160089939 := by
        calc
          (34 : ZMod 426598383733) ^ 277733322 = (34 : ZMod 426598383733) ^ (138866661 + 138866661) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 138866661 * (34 : ZMod 426598383733) ^ 138866661 := by rw [pow_add]
          _ = 182160089939 := by rw [factor_1_27]; decide
      have factor_1_29 : (34 : ZMod 426598383733) ^ 555466645 = 48803162227 := by
        calc
          (34 : ZMod 426598383733) ^ 555466645 = (34 : ZMod 426598383733) ^ (277733322 + 277733322 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 277733322 * (34 : ZMod 426598383733) ^ 277733322) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 48803162227 := by rw [factor_1_28]; decide
      have factor_1_30 : (34 : ZMod 426598383733) ^ 1110933290 = 182072514227 := by
        calc
          (34 : ZMod 426598383733) ^ 1110933290 = (34 : ZMod 426598383733) ^ (555466645 + 555466645) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 555466645 * (34 : ZMod 426598383733) ^ 555466645 := by rw [pow_add]
          _ = 182072514227 := by rw [factor_1_29]; decide
      have factor_1_31 : (34 : ZMod 426598383733) ^ 2221866581 = 10684822256 := by
        calc
          (34 : ZMod 426598383733) ^ 2221866581 = (34 : ZMod 426598383733) ^ (1110933290 + 1110933290 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 1110933290 * (34 : ZMod 426598383733) ^ 1110933290) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 10684822256 := by rw [factor_1_30]; decide
      have factor_1_32 : (34 : ZMod 426598383733) ^ 4443733163 = 275692625832 := by
        calc
          (34 : ZMod 426598383733) ^ 4443733163 = (34 : ZMod 426598383733) ^ (2221866581 + 2221866581 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 2221866581 * (34 : ZMod 426598383733) ^ 2221866581) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 275692625832 := by rw [factor_1_31]; decide
      have factor_1_33 : (34 : ZMod 426598383733) ^ 8887466327 = 260785142398 := by
        calc
          (34 : ZMod 426598383733) ^ 8887466327 = (34 : ZMod 426598383733) ^ (4443733163 + 4443733163 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 4443733163 * (34 : ZMod 426598383733) ^ 4443733163) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 260785142398 := by rw [factor_1_32]; decide
      have factor_1_34 : (34 : ZMod 426598383733) ^ 17774932655 = 59671797791 := by
        calc
          (34 : ZMod 426598383733) ^ 17774932655 = (34 : ZMod 426598383733) ^ (8887466327 + 8887466327 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 8887466327 * (34 : ZMod 426598383733) ^ 8887466327) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 59671797791 := by rw [factor_1_33]; decide
      have factor_1_35 : (34 : ZMod 426598383733) ^ 35549865311 = 292679554274 := by
        calc
          (34 : ZMod 426598383733) ^ 35549865311 = (34 : ZMod 426598383733) ^ (17774932655 + 17774932655 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 17774932655 * (34 : ZMod 426598383733) ^ 17774932655) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 292679554274 := by rw [factor_1_34]; decide
      have factor_1_36 : (34 : ZMod 426598383733) ^ 71099730622 = 96725322421 := by
        calc
          (34 : ZMod 426598383733) ^ 71099730622 = (34 : ZMod 426598383733) ^ (35549865311 + 35549865311) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 35549865311 * (34 : ZMod 426598383733) ^ 35549865311 := by rw [pow_add]
          _ = 96725322421 := by rw [factor_1_35]; decide
      have factor_1_37 : (34 : ZMod 426598383733) ^ 142199461244 = 96725322420 := by
        calc
          (34 : ZMod 426598383733) ^ 142199461244 = (34 : ZMod 426598383733) ^ (71099730622 + 71099730622) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 71099730622 * (34 : ZMod 426598383733) ^ 71099730622 := by rw [pow_add]
          _ = 96725322420 := by rw [factor_1_36]; decide
      change (34 : ZMod 426598383733) ^ 142199461244 ≠ 1
      rw [factor_1_37]
      decide
    ·
      have factor_2_0 : (34 : ZMod 426598383733) ^ 1 = 34 := by norm_num
      have factor_2_1 : (34 : ZMod 426598383733) ^ 2 = 1156 := by
        calc
          (34 : ZMod 426598383733) ^ 2 = (34 : ZMod 426598383733) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 1 * (34 : ZMod 426598383733) ^ 1 := by rw [pow_add]
          _ = 1156 := by rw [factor_2_0]; decide
      have factor_2_2 : (34 : ZMod 426598383733) ^ 4 = 1336336 := by
        calc
          (34 : ZMod 426598383733) ^ 4 = (34 : ZMod 426598383733) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 2 * (34 : ZMod 426598383733) ^ 2 := by rw [pow_add]
          _ = 1336336 := by rw [factor_2_1]; decide
      have factor_2_3 : (34 : ZMod 426598383733) ^ 8 = 79400369964 := by
        calc
          (34 : ZMod 426598383733) ^ 8 = (34 : ZMod 426598383733) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 4 * (34 : ZMod 426598383733) ^ 4 := by rw [pow_add]
          _ = 79400369964 := by rw [factor_2_2]; decide
      have factor_2_4 : (34 : ZMod 426598383733) ^ 16 = 76908608811 := by
        calc
          (34 : ZMod 426598383733) ^ 16 = (34 : ZMod 426598383733) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 8 * (34 : ZMod 426598383733) ^ 8 := by rw [pow_add]
          _ = 76908608811 := by rw [factor_2_3]; decide
      have factor_2_5 : (34 : ZMod 426598383733) ^ 33 = 351492485342 := by
        calc
          (34 : ZMod 426598383733) ^ 33 = (34 : ZMod 426598383733) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 16 * (34 : ZMod 426598383733) ^ 16) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 351492485342 := by rw [factor_2_4]; decide
      have factor_2_6 : (34 : ZMod 426598383733) ^ 67 = 97304964332 := by
        calc
          (34 : ZMod 426598383733) ^ 67 = (34 : ZMod 426598383733) ^ (33 + 33 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 33 * (34 : ZMod 426598383733) ^ 33) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 97304964332 := by rw [factor_2_5]; decide
      have factor_2_7 : (34 : ZMod 426598383733) ^ 135 = 245561277024 := by
        calc
          (34 : ZMod 426598383733) ^ 135 = (34 : ZMod 426598383733) ^ (67 + 67 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 67 * (34 : ZMod 426598383733) ^ 67) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 245561277024 := by rw [factor_2_6]; decide
      have factor_2_8 : (34 : ZMod 426598383733) ^ 270 = 277376482084 := by
        calc
          (34 : ZMod 426598383733) ^ 270 = (34 : ZMod 426598383733) ^ (135 + 135) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 135 * (34 : ZMod 426598383733) ^ 135 := by rw [pow_add]
          _ = 277376482084 := by rw [factor_2_7]; decide
      have factor_2_9 : (34 : ZMod 426598383733) ^ 541 = 388456223520 := by
        calc
          (34 : ZMod 426598383733) ^ 541 = (34 : ZMod 426598383733) ^ (270 + 270 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 270 * (34 : ZMod 426598383733) ^ 270) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 388456223520 := by rw [factor_2_8]; decide
      have factor_2_10 : (34 : ZMod 426598383733) ^ 1082 = 216042630179 := by
        calc
          (34 : ZMod 426598383733) ^ 1082 = (34 : ZMod 426598383733) ^ (541 + 541) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 541 * (34 : ZMod 426598383733) ^ 541 := by rw [pow_add]
          _ = 216042630179 := by rw [factor_2_9]; decide
      have factor_2_11 : (34 : ZMod 426598383733) ^ 2164 = 140159503106 := by
        calc
          (34 : ZMod 426598383733) ^ 2164 = (34 : ZMod 426598383733) ^ (1082 + 1082) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 1082 * (34 : ZMod 426598383733) ^ 1082 := by rw [pow_add]
          _ = 140159503106 := by rw [factor_2_10]; decide
      have factor_2_12 : (34 : ZMod 426598383733) ^ 4328 = 177092238447 := by
        calc
          (34 : ZMod 426598383733) ^ 4328 = (34 : ZMod 426598383733) ^ (2164 + 2164) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 2164 * (34 : ZMod 426598383733) ^ 2164 := by rw [pow_add]
          _ = 177092238447 := by rw [factor_2_11]; decide
      have factor_2_13 : (34 : ZMod 426598383733) ^ 8656 = 40251040504 := by
        calc
          (34 : ZMod 426598383733) ^ 8656 = (34 : ZMod 426598383733) ^ (4328 + 4328) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 4328 * (34 : ZMod 426598383733) ^ 4328 := by rw [pow_add]
          _ = 40251040504 := by rw [factor_2_12]; decide
      have factor_2_14 : (34 : ZMod 426598383733) ^ 17312 = 274632760415 := by
        calc
          (34 : ZMod 426598383733) ^ 17312 = (34 : ZMod 426598383733) ^ (8656 + 8656) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 8656 * (34 : ZMod 426598383733) ^ 8656 := by rw [pow_add]
          _ = 274632760415 := by rw [factor_2_13]; decide
      have factor_2_15 : (34 : ZMod 426598383733) ^ 34624 = 166520137429 := by
        calc
          (34 : ZMod 426598383733) ^ 34624 = (34 : ZMod 426598383733) ^ (17312 + 17312) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 17312 * (34 : ZMod 426598383733) ^ 17312 := by rw [pow_add]
          _ = 166520137429 := by rw [factor_2_14]; decide
      have factor_2_16 : (34 : ZMod 426598383733) ^ 69248 = 48218218682 := by
        calc
          (34 : ZMod 426598383733) ^ 69248 = (34 : ZMod 426598383733) ^ (34624 + 34624) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 34624 * (34 : ZMod 426598383733) ^ 34624 := by rw [pow_add]
          _ = 48218218682 := by rw [factor_2_15]; decide
      have factor_2_17 : (34 : ZMod 426598383733) ^ 138497 = 87499614984 := by
        calc
          (34 : ZMod 426598383733) ^ 138497 = (34 : ZMod 426598383733) ^ (69248 + 69248 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 69248 * (34 : ZMod 426598383733) ^ 69248) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 87499614984 := by rw [factor_2_16]; decide
      have factor_2_18 : (34 : ZMod 426598383733) ^ 276994 = 175476260467 := by
        calc
          (34 : ZMod 426598383733) ^ 276994 = (34 : ZMod 426598383733) ^ (138497 + 138497) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 138497 * (34 : ZMod 426598383733) ^ 138497 := by rw [pow_add]
          _ = 175476260467 := by rw [factor_2_17]; decide
      have factor_2_19 : (34 : ZMod 426598383733) ^ 553989 = 327619669555 := by
        calc
          (34 : ZMod 426598383733) ^ 553989 = (34 : ZMod 426598383733) ^ (276994 + 276994 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 276994 * (34 : ZMod 426598383733) ^ 276994) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 327619669555 := by rw [factor_2_18]; decide
      have factor_2_20 : (34 : ZMod 426598383733) ^ 1107978 = 188707099190 := by
        calc
          (34 : ZMod 426598383733) ^ 1107978 = (34 : ZMod 426598383733) ^ (553989 + 553989) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 553989 * (34 : ZMod 426598383733) ^ 553989 := by rw [pow_add]
          _ = 188707099190 := by rw [factor_2_19]; decide
      have factor_2_21 : (34 : ZMod 426598383733) ^ 2215957 = 111066760288 := by
        calc
          (34 : ZMod 426598383733) ^ 2215957 = (34 : ZMod 426598383733) ^ (1107978 + 1107978 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 1107978 * (34 : ZMod 426598383733) ^ 1107978) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 111066760288 := by rw [factor_2_20]; decide
      have factor_2_22 : (34 : ZMod 426598383733) ^ 4431914 = 288404558339 := by
        calc
          (34 : ZMod 426598383733) ^ 4431914 = (34 : ZMod 426598383733) ^ (2215957 + 2215957) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 2215957 * (34 : ZMod 426598383733) ^ 2215957 := by rw [pow_add]
          _ = 288404558339 := by rw [factor_2_21]; decide
      have factor_2_23 : (34 : ZMod 426598383733) ^ 8863829 = 143879640403 := by
        calc
          (34 : ZMod 426598383733) ^ 8863829 = (34 : ZMod 426598383733) ^ (4431914 + 4431914 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 4431914 * (34 : ZMod 426598383733) ^ 4431914) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 143879640403 := by rw [factor_2_22]; decide
      have factor_2_24 : (34 : ZMod 426598383733) ^ 17727658 = 378014775650 := by
        calc
          (34 : ZMod 426598383733) ^ 17727658 = (34 : ZMod 426598383733) ^ (8863829 + 8863829) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 8863829 * (34 : ZMod 426598383733) ^ 8863829 := by rw [pow_add]
          _ = 378014775650 := by rw [factor_2_23]; decide
      have factor_2_25 : (34 : ZMod 426598383733) ^ 35455317 = 340291911405 := by
        calc
          (34 : ZMod 426598383733) ^ 35455317 = (34 : ZMod 426598383733) ^ (17727658 + 17727658 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 17727658 * (34 : ZMod 426598383733) ^ 17727658) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 340291911405 := by rw [factor_2_24]; decide
      have factor_2_26 : (34 : ZMod 426598383733) ^ 70910635 = 89318765304 := by
        calc
          (34 : ZMod 426598383733) ^ 70910635 = (34 : ZMod 426598383733) ^ (35455317 + 35455317 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 35455317 * (34 : ZMod 426598383733) ^ 35455317) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 89318765304 := by rw [factor_2_25]; decide
      have factor_2_27 : (34 : ZMod 426598383733) ^ 141821271 = 144478508433 := by
        calc
          (34 : ZMod 426598383733) ^ 141821271 = (34 : ZMod 426598383733) ^ (70910635 + 70910635 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 70910635 * (34 : ZMod 426598383733) ^ 70910635) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 144478508433 := by rw [factor_2_26]; decide
      have factor_2_28 : (34 : ZMod 426598383733) ^ 283642542 = 309655412797 := by
        calc
          (34 : ZMod 426598383733) ^ 283642542 = (34 : ZMod 426598383733) ^ (141821271 + 141821271) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 141821271 * (34 : ZMod 426598383733) ^ 141821271 := by rw [pow_add]
          _ = 309655412797 := by rw [factor_2_27]; decide
      have factor_2_29 : (34 : ZMod 426598383733) ^ 567285084 = 138615737066 := by
        calc
          (34 : ZMod 426598383733) ^ 567285084 = (34 : ZMod 426598383733) ^ (283642542 + 283642542) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 283642542 * (34 : ZMod 426598383733) ^ 283642542 := by rw [pow_add]
          _ = 138615737066 := by rw [factor_2_28]; decide
      have factor_2_30 : (34 : ZMod 426598383733) ^ 1134570169 = 46132281370 := by
        calc
          (34 : ZMod 426598383733) ^ 1134570169 = (34 : ZMod 426598383733) ^ (567285084 + 567285084 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 567285084 * (34 : ZMod 426598383733) ^ 567285084) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 46132281370 := by rw [factor_2_29]; decide
      have factor_2_31 : (34 : ZMod 426598383733) ^ 2269140339 = 259895366531 := by
        calc
          (34 : ZMod 426598383733) ^ 2269140339 = (34 : ZMod 426598383733) ^ (1134570169 + 1134570169 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 1134570169 * (34 : ZMod 426598383733) ^ 1134570169) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 259895366531 := by rw [factor_2_30]; decide
      have factor_2_32 : (34 : ZMod 426598383733) ^ 4538280678 = 562213998 := by
        calc
          (34 : ZMod 426598383733) ^ 4538280678 = (34 : ZMod 426598383733) ^ (2269140339 + 2269140339) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 2269140339 * (34 : ZMod 426598383733) ^ 2269140339 := by rw [pow_add]
          _ = 562213998 := by rw [factor_2_31]; decide
      have factor_2_33 : (34 : ZMod 426598383733) ^ 9076561356 = 346505631251 := by
        calc
          (34 : ZMod 426598383733) ^ 9076561356 = (34 : ZMod 426598383733) ^ (4538280678 + 4538280678) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 4538280678 * (34 : ZMod 426598383733) ^ 4538280678 := by rw [pow_add]
          _ = 346505631251 := by rw [factor_2_32]; decide
      change (34 : ZMod 426598383733) ^ 9076561356 ≠ 1
      rw [factor_2_33]
      decide
    ·
      have factor_3_0 : (34 : ZMod 426598383733) ^ 1 = 34 := by norm_num
      have factor_3_1 : (34 : ZMod 426598383733) ^ 2 = 1156 := by
        calc
          (34 : ZMod 426598383733) ^ 2 = (34 : ZMod 426598383733) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 1 * (34 : ZMod 426598383733) ^ 1 := by rw [pow_add]
          _ = 1156 := by rw [factor_3_0]; decide
      have factor_3_2 : (34 : ZMod 426598383733) ^ 5 = 45435424 := by
        calc
          (34 : ZMod 426598383733) ^ 5 = (34 : ZMod 426598383733) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 2 * (34 : ZMod 426598383733) ^ 2) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 45435424 := by rw [factor_3_1]; decide
      have factor_3_3 : (34 : ZMod 426598383733) ^ 11 = 184964058161 := by
        calc
          (34 : ZMod 426598383733) ^ 11 = (34 : ZMod 426598383733) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 5 * (34 : ZMod 426598383733) ^ 5) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 184964058161 := by rw [factor_3_2]; decide
      have factor_3_4 : (34 : ZMod 426598383733) ^ 23 = 293711254637 := by
        calc
          (34 : ZMod 426598383733) ^ 23 = (34 : ZMod 426598383733) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 11 * (34 : ZMod 426598383733) ^ 11) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 293711254637 := by rw [factor_3_3]; decide
      have factor_3_5 : (34 : ZMod 426598383733) ^ 46 = 370350255487 := by
        calc
          (34 : ZMod 426598383733) ^ 46 = (34 : ZMod 426598383733) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 23 * (34 : ZMod 426598383733) ^ 23 := by rw [pow_add]
          _ = 370350255487 := by rw [factor_3_4]; decide
      have factor_3_6 : (34 : ZMod 426598383733) ^ 92 = 357905239476 := by
        calc
          (34 : ZMod 426598383733) ^ 92 = (34 : ZMod 426598383733) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 46 * (34 : ZMod 426598383733) ^ 46 := by rw [pow_add]
          _ = 357905239476 := by rw [factor_3_5]; decide
      have factor_3_7 : (34 : ZMod 426598383733) ^ 185 = 134682664022 := by
        calc
          (34 : ZMod 426598383733) ^ 185 = (34 : ZMod 426598383733) ^ (92 + 92 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 92 * (34 : ZMod 426598383733) ^ 92) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 134682664022 := by rw [factor_3_6]; decide
      have factor_3_8 : (34 : ZMod 426598383733) ^ 371 = 357874427403 := by
        calc
          (34 : ZMod 426598383733) ^ 371 = (34 : ZMod 426598383733) ^ (185 + 185 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 185 * (34 : ZMod 426598383733) ^ 185) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 357874427403 := by rw [factor_3_7]; decide
      have factor_3_9 : (34 : ZMod 426598383733) ^ 743 = 173813963925 := by
        calc
          (34 : ZMod 426598383733) ^ 743 = (34 : ZMod 426598383733) ^ (371 + 371 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 371 * (34 : ZMod 426598383733) ^ 371) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 173813963925 := by rw [factor_3_8]; decide
      have factor_3_10 : (34 : ZMod 426598383733) ^ 1487 = 122283959813 := by
        calc
          (34 : ZMod 426598383733) ^ 1487 = (34 : ZMod 426598383733) ^ (743 + 743 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 743 * (34 : ZMod 426598383733) ^ 743) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 122283959813 := by rw [factor_3_9]; decide
      have factor_3_11 : (34 : ZMod 426598383733) ^ 2975 = 30665431630 := by
        calc
          (34 : ZMod 426598383733) ^ 2975 = (34 : ZMod 426598383733) ^ (1487 + 1487 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 1487 * (34 : ZMod 426598383733) ^ 1487) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 30665431630 := by rw [factor_3_10]; decide
      have factor_3_12 : (34 : ZMod 426598383733) ^ 5950 = 200093539404 := by
        calc
          (34 : ZMod 426598383733) ^ 5950 = (34 : ZMod 426598383733) ^ (2975 + 2975) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 2975 * (34 : ZMod 426598383733) ^ 2975 := by rw [pow_add]
          _ = 200093539404 := by rw [factor_3_11]; decide
      have factor_3_13 : (34 : ZMod 426598383733) ^ 11900 = 330660784587 := by
        calc
          (34 : ZMod 426598383733) ^ 11900 = (34 : ZMod 426598383733) ^ (5950 + 5950) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 5950 * (34 : ZMod 426598383733) ^ 5950 := by rw [pow_add]
          _ = 330660784587 := by rw [factor_3_12]; decide
      have factor_3_14 : (34 : ZMod 426598383733) ^ 23800 = 250912823191 := by
        calc
          (34 : ZMod 426598383733) ^ 23800 = (34 : ZMod 426598383733) ^ (11900 + 11900) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 11900 * (34 : ZMod 426598383733) ^ 11900 := by rw [pow_add]
          _ = 250912823191 := by rw [factor_3_13]; decide
      have factor_3_15 : (34 : ZMod 426598383733) ^ 47600 = 11924421471 := by
        calc
          (34 : ZMod 426598383733) ^ 47600 = (34 : ZMod 426598383733) ^ (23800 + 23800) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 23800 * (34 : ZMod 426598383733) ^ 23800 := by rw [pow_add]
          _ = 11924421471 := by rw [factor_3_14]; decide
      have factor_3_16 : (34 : ZMod 426598383733) ^ 95201 = 183857522899 := by
        calc
          (34 : ZMod 426598383733) ^ 95201 = (34 : ZMod 426598383733) ^ (47600 + 47600 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 47600 * (34 : ZMod 426598383733) ^ 47600) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 183857522899 := by rw [factor_3_15]; decide
      have factor_3_17 : (34 : ZMod 426598383733) ^ 190402 = 316983672492 := by
        calc
          (34 : ZMod 426598383733) ^ 190402 = (34 : ZMod 426598383733) ^ (95201 + 95201) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 95201 * (34 : ZMod 426598383733) ^ 95201 := by rw [pow_add]
          _ = 316983672492 := by rw [factor_3_16]; decide
      have factor_3_18 : (34 : ZMod 426598383733) ^ 380804 = 294027010338 := by
        calc
          (34 : ZMod 426598383733) ^ 380804 = (34 : ZMod 426598383733) ^ (190402 + 190402) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 190402 * (34 : ZMod 426598383733) ^ 190402 := by rw [pow_add]
          _ = 294027010338 := by rw [factor_3_17]; decide
      have factor_3_19 : (34 : ZMod 426598383733) ^ 761608 = 228033653945 := by
        calc
          (34 : ZMod 426598383733) ^ 761608 = (34 : ZMod 426598383733) ^ (380804 + 380804) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 380804 * (34 : ZMod 426598383733) ^ 380804 := by rw [pow_add]
          _ = 228033653945 := by rw [factor_3_18]; decide
      have factor_3_20 : (34 : ZMod 426598383733) ^ 1523217 = 409927460945 := by
        calc
          (34 : ZMod 426598383733) ^ 1523217 = (34 : ZMod 426598383733) ^ (761608 + 761608 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 761608 * (34 : ZMod 426598383733) ^ 761608) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 409927460945 := by rw [factor_3_19]; decide
      have factor_3_21 : (34 : ZMod 426598383733) ^ 3046434 = 425224510837 := by
        calc
          (34 : ZMod 426598383733) ^ 3046434 = (34 : ZMod 426598383733) ^ (1523217 + 1523217) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 1523217 * (34 : ZMod 426598383733) ^ 1523217 := by rw [pow_add]
          _ = 425224510837 := by rw [factor_3_20]; decide
      have factor_3_22 : (34 : ZMod 426598383733) ^ 6092869 = 84484012398 := by
        calc
          (34 : ZMod 426598383733) ^ 6092869 = (34 : ZMod 426598383733) ^ (3046434 + 3046434 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 3046434 * (34 : ZMod 426598383733) ^ 3046434) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 84484012398 := by rw [factor_3_21]; decide
      have factor_3_23 : (34 : ZMod 426598383733) ^ 12185739 = 367518696471 := by
        calc
          (34 : ZMod 426598383733) ^ 12185739 = (34 : ZMod 426598383733) ^ (6092869 + 6092869 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 6092869 * (34 : ZMod 426598383733) ^ 6092869) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 367518696471 := by rw [factor_3_22]; decide
      have factor_3_24 : (34 : ZMod 426598383733) ^ 24371479 = 289033714981 := by
        calc
          (34 : ZMod 426598383733) ^ 24371479 = (34 : ZMod 426598383733) ^ (12185739 + 12185739 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 12185739 * (34 : ZMod 426598383733) ^ 12185739) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 289033714981 := by rw [factor_3_23]; decide
      have factor_3_25 : (34 : ZMod 426598383733) ^ 48742959 = 136132470474 := by
        calc
          (34 : ZMod 426598383733) ^ 48742959 = (34 : ZMod 426598383733) ^ (24371479 + 24371479 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 24371479 * (34 : ZMod 426598383733) ^ 24371479) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 136132470474 := by rw [factor_3_24]; decide
      have factor_3_26 : (34 : ZMod 426598383733) ^ 97485919 = 42066999010 := by
        calc
          (34 : ZMod 426598383733) ^ 97485919 = (34 : ZMod 426598383733) ^ (48742959 + 48742959 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 48742959 * (34 : ZMod 426598383733) ^ 48742959) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 42066999010 := by rw [factor_3_25]; decide
      have factor_3_27 : (34 : ZMod 426598383733) ^ 194971839 = 311790172377 := by
        calc
          (34 : ZMod 426598383733) ^ 194971839 = (34 : ZMod 426598383733) ^ (97485919 + 97485919 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 97485919 * (34 : ZMod 426598383733) ^ 97485919) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 311790172377 := by rw [factor_3_26]; decide
      have factor_3_28 : (34 : ZMod 426598383733) ^ 389943678 = 73418954306 := by
        calc
          (34 : ZMod 426598383733) ^ 389943678 = (34 : ZMod 426598383733) ^ (194971839 + 194971839) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 194971839 * (34 : ZMod 426598383733) ^ 194971839 := by rw [pow_add]
          _ = 73418954306 := by rw [factor_3_27]; decide
      have factor_3_29 : (34 : ZMod 426598383733) ^ 779887356 = 341028807983 := by
        calc
          (34 : ZMod 426598383733) ^ 779887356 = (34 : ZMod 426598383733) ^ (389943678 + 389943678) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 389943678 * (34 : ZMod 426598383733) ^ 389943678 := by rw [pow_add]
          _ = 341028807983 := by rw [factor_3_28]; decide
      change (34 : ZMod 426598383733) ^ 779887356 ≠ 1
      rw [factor_3_29]
      decide
    ·
      have factor_4_0 : (34 : ZMod 426598383733) ^ 1 = 34 := by norm_num
      have factor_4_1 : (34 : ZMod 426598383733) ^ 2 = 1156 := by
        calc
          (34 : ZMod 426598383733) ^ 2 = (34 : ZMod 426598383733) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 1 * (34 : ZMod 426598383733) ^ 1 := by rw [pow_add]
          _ = 1156 := by rw [factor_4_0]; decide
      have factor_4_2 : (34 : ZMod 426598383733) ^ 4 = 1336336 := by
        calc
          (34 : ZMod 426598383733) ^ 4 = (34 : ZMod 426598383733) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 2 * (34 : ZMod 426598383733) ^ 2 := by rw [pow_add]
          _ = 1336336 := by rw [factor_4_1]; decide
      have factor_4_3 : (34 : ZMod 426598383733) ^ 9 = 140022276378 := by
        calc
          (34 : ZMod 426598383733) ^ 9 = (34 : ZMod 426598383733) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 4 * (34 : ZMod 426598383733) ^ 4) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 140022276378 := by rw [factor_4_2]; decide
      have factor_4_4 : (34 : ZMod 426598383733) ^ 18 = 173887969052 := by
        calc
          (34 : ZMod 426598383733) ^ 18 = (34 : ZMod 426598383733) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 9 * (34 : ZMod 426598383733) ^ 9 := by rw [pow_add]
          _ = 173887969052 := by rw [factor_4_3]; decide
      have factor_4_5 : (34 : ZMod 426598383733) ^ 37 = 365703778733 := by
        calc
          (34 : ZMod 426598383733) ^ 37 = (34 : ZMod 426598383733) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 18 * (34 : ZMod 426598383733) ^ 18) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 365703778733 := by rw [factor_4_4]; decide
      have factor_4_6 : (34 : ZMod 426598383733) ^ 75 = 275874566082 := by
        calc
          (34 : ZMod 426598383733) ^ 75 = (34 : ZMod 426598383733) ^ (37 + 37 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 37 * (34 : ZMod 426598383733) ^ 37) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 275874566082 := by rw [factor_4_5]; decide
      have factor_4_7 : (34 : ZMod 426598383733) ^ 150 = 196580088109 := by
        calc
          (34 : ZMod 426598383733) ^ 150 = (34 : ZMod 426598383733) ^ (75 + 75) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 75 * (34 : ZMod 426598383733) ^ 75 := by rw [pow_add]
          _ = 196580088109 := by rw [factor_4_6]; decide
      have factor_4_8 : (34 : ZMod 426598383733) ^ 301 = 275306060082 := by
        calc
          (34 : ZMod 426598383733) ^ 301 = (34 : ZMod 426598383733) ^ (150 + 150 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 150 * (34 : ZMod 426598383733) ^ 150) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 275306060082 := by rw [factor_4_7]; decide
      have factor_4_9 : (34 : ZMod 426598383733) ^ 602 = 99499448100 := by
        calc
          (34 : ZMod 426598383733) ^ 602 = (34 : ZMod 426598383733) ^ (301 + 301) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 301 * (34 : ZMod 426598383733) ^ 301 := by rw [pow_add]
          _ = 99499448100 := by rw [factor_4_8]; decide
      have factor_4_10 : (34 : ZMod 426598383733) ^ 1205 = 421676187282 := by
        calc
          (34 : ZMod 426598383733) ^ 1205 = (34 : ZMod 426598383733) ^ (602 + 602 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 602 * (34 : ZMod 426598383733) ^ 602) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 421676187282 := by rw [factor_4_9]; decide
      have factor_4_11 : (34 : ZMod 426598383733) ^ 2410 = 36106557503 := by
        calc
          (34 : ZMod 426598383733) ^ 2410 = (34 : ZMod 426598383733) ^ (1205 + 1205) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 1205 * (34 : ZMod 426598383733) ^ 1205 := by rw [pow_add]
          _ = 36106557503 := by rw [factor_4_10]; decide
      have factor_4_12 : (34 : ZMod 426598383733) ^ 4820 = 349378721031 := by
        calc
          (34 : ZMod 426598383733) ^ 4820 = (34 : ZMod 426598383733) ^ (2410 + 2410) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 2410 * (34 : ZMod 426598383733) ^ 2410 := by rw [pow_add]
          _ = 349378721031 := by rw [factor_4_11]; decide
      have factor_4_13 : (34 : ZMod 426598383733) ^ 9640 = 372660440909 := by
        calc
          (34 : ZMod 426598383733) ^ 9640 = (34 : ZMod 426598383733) ^ (4820 + 4820) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 4820 * (34 : ZMod 426598383733) ^ 4820 := by rw [pow_add]
          _ = 372660440909 := by rw [factor_4_12]; decide
      have factor_4_14 : (34 : ZMod 426598383733) ^ 19281 = 19282299613 := by
        calc
          (34 : ZMod 426598383733) ^ 19281 = (34 : ZMod 426598383733) ^ (9640 + 9640 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 9640 * (34 : ZMod 426598383733) ^ 9640) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 19282299613 := by rw [factor_4_13]; decide
      have factor_4_15 : (34 : ZMod 426598383733) ^ 38563 = 31722437408 := by
        calc
          (34 : ZMod 426598383733) ^ 38563 = (34 : ZMod 426598383733) ^ (19281 + 19281 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 19281 * (34 : ZMod 426598383733) ^ 19281) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 31722437408 := by rw [factor_4_14]; decide
      have factor_4_16 : (34 : ZMod 426598383733) ^ 77127 = 255781671505 := by
        calc
          (34 : ZMod 426598383733) ^ 77127 = (34 : ZMod 426598383733) ^ (38563 + 38563 + 1) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = ((34 : ZMod 426598383733) ^ 38563 * (34 : ZMod 426598383733) ^ 38563) * (34 : ZMod 426598383733) := by rw [pow_succ, pow_add]
          _ = 255781671505 := by rw [factor_4_15]; decide
      have factor_4_17 : (34 : ZMod 426598383733) ^ 154254 = 86980342558 := by
        calc
          (34 : ZMod 426598383733) ^ 154254 = (34 : ZMod 426598383733) ^ (77127 + 77127) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 77127 * (34 : ZMod 426598383733) ^ 77127 := by rw [pow_add]
          _ = 86980342558 := by rw [factor_4_16]; decide
      have factor_4_18 : (34 : ZMod 426598383733) ^ 308508 = 364766324673 := by
        calc
          (34 : ZMod 426598383733) ^ 308508 = (34 : ZMod 426598383733) ^ (154254 + 154254) :=
            congrArg (fun n : ℕ => (34 : ZMod 426598383733) ^ n) (by norm_num)
          _ = (34 : ZMod 426598383733) ^ 154254 * (34 : ZMod 426598383733) ^ 154254 := by rw [pow_add]
          _ = 364766324673 := by rw [factor_4_17]; decide
      change (34 : ZMod 426598383733) ^ 308508 ≠ 1
      rw [factor_4_18]
      decide

#print axioms prime_lucas_426598383733

end TotientTailPeriodKiller
end Erdos249257
