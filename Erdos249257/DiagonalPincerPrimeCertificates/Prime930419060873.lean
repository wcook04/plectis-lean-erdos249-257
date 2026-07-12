import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_930419060873 : Nat.Prime 930419060873 := by
  apply lucas_primality 930419060873 (3 : ZMod 930419060873)
  ·
      have fermat_0 : (3 : ZMod 930419060873) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 930419060873) ^ 3 = 27 := by
        calc
          (3 : ZMod 930419060873) ^ 3 = (3 : ZMod 930419060873) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 1 * (3 : ZMod 930419060873) ^ 1) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 930419060873) ^ 6 = 729 := by
        calc
          (3 : ZMod 930419060873) ^ 6 = (3 : ZMod 930419060873) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 3 * (3 : ZMod 930419060873) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 930419060873) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 930419060873) ^ 13 = (3 : ZMod 930419060873) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 6 * (3 : ZMod 930419060873) ^ 6) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 930419060873) ^ 27 = 182244998003 := by
        calc
          (3 : ZMod 930419060873) ^ 27 = (3 : ZMod 930419060873) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 13 * (3 : ZMod 930419060873) ^ 13) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 182244998003 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 930419060873) ^ 54 = 105489911903 := by
        calc
          (3 : ZMod 930419060873) ^ 54 = (3 : ZMod 930419060873) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 27 * (3 : ZMod 930419060873) ^ 27 := by rw [pow_add]
          _ = 105489911903 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 930419060873) ^ 108 = 422582999547 := by
        calc
          (3 : ZMod 930419060873) ^ 108 = (3 : ZMod 930419060873) ^ (54 + 54) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 54 * (3 : ZMod 930419060873) ^ 54 := by rw [pow_add]
          _ = 422582999547 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 930419060873) ^ 216 = 541795939979 := by
        calc
          (3 : ZMod 930419060873) ^ 216 = (3 : ZMod 930419060873) ^ (108 + 108) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 108 * (3 : ZMod 930419060873) ^ 108 := by rw [pow_add]
          _ = 541795939979 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 930419060873) ^ 433 = 162041906553 := by
        calc
          (3 : ZMod 930419060873) ^ 433 = (3 : ZMod 930419060873) ^ (216 + 216 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 216 * (3 : ZMod 930419060873) ^ 216) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 162041906553 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 930419060873) ^ 866 = 492081891886 := by
        calc
          (3 : ZMod 930419060873) ^ 866 = (3 : ZMod 930419060873) ^ (433 + 433) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 433 * (3 : ZMod 930419060873) ^ 433 := by rw [pow_add]
          _ = 492081891886 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 930419060873) ^ 1733 = 620608013805 := by
        calc
          (3 : ZMod 930419060873) ^ 1733 = (3 : ZMod 930419060873) ^ (866 + 866 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 866 * (3 : ZMod 930419060873) ^ 866) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 620608013805 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 930419060873) ^ 3466 = 925734189695 := by
        calc
          (3 : ZMod 930419060873) ^ 3466 = (3 : ZMod 930419060873) ^ (1733 + 1733) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 1733 * (3 : ZMod 930419060873) ^ 1733 := by rw [pow_add]
          _ = 925734189695 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 930419060873) ^ 6932 = 794507231087 := by
        calc
          (3 : ZMod 930419060873) ^ 6932 = (3 : ZMod 930419060873) ^ (3466 + 3466) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 3466 * (3 : ZMod 930419060873) ^ 3466 := by rw [pow_add]
          _ = 794507231087 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 930419060873) ^ 13864 = 163520009716 := by
        calc
          (3 : ZMod 930419060873) ^ 13864 = (3 : ZMod 930419060873) ^ (6932 + 6932) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 6932 * (3 : ZMod 930419060873) ^ 6932 := by rw [pow_add]
          _ = 163520009716 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 930419060873) ^ 27728 = 125449354407 := by
        calc
          (3 : ZMod 930419060873) ^ 27728 = (3 : ZMod 930419060873) ^ (13864 + 13864) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 13864 * (3 : ZMod 930419060873) ^ 13864 := by rw [pow_add]
          _ = 125449354407 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 930419060873) ^ 55457 = 202925566052 := by
        calc
          (3 : ZMod 930419060873) ^ 55457 = (3 : ZMod 930419060873) ^ (27728 + 27728 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 27728 * (3 : ZMod 930419060873) ^ 27728) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 202925566052 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 930419060873) ^ 110914 = 165356390607 := by
        calc
          (3 : ZMod 930419060873) ^ 110914 = (3 : ZMod 930419060873) ^ (55457 + 55457) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 55457 * (3 : ZMod 930419060873) ^ 55457 := by rw [pow_add]
          _ = 165356390607 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 930419060873) ^ 221829 = 593464808959 := by
        calc
          (3 : ZMod 930419060873) ^ 221829 = (3 : ZMod 930419060873) ^ (110914 + 110914 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 110914 * (3 : ZMod 930419060873) ^ 110914) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 593464808959 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 930419060873) ^ 443658 = 401463301647 := by
        calc
          (3 : ZMod 930419060873) ^ 443658 = (3 : ZMod 930419060873) ^ (221829 + 221829) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 221829 * (3 : ZMod 930419060873) ^ 221829 := by rw [pow_add]
          _ = 401463301647 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 930419060873) ^ 887316 = 80982039690 := by
        calc
          (3 : ZMod 930419060873) ^ 887316 = (3 : ZMod 930419060873) ^ (443658 + 443658) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 443658 * (3 : ZMod 930419060873) ^ 443658 := by rw [pow_add]
          _ = 80982039690 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 930419060873) ^ 1774633 = 77388207795 := by
        calc
          (3 : ZMod 930419060873) ^ 1774633 = (3 : ZMod 930419060873) ^ (887316 + 887316 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 887316 * (3 : ZMod 930419060873) ^ 887316) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 77388207795 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 930419060873) ^ 3549267 = 740853704057 := by
        calc
          (3 : ZMod 930419060873) ^ 3549267 = (3 : ZMod 930419060873) ^ (1774633 + 1774633 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 1774633 * (3 : ZMod 930419060873) ^ 1774633) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 740853704057 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 930419060873) ^ 7098534 = 127499404569 := by
        calc
          (3 : ZMod 930419060873) ^ 7098534 = (3 : ZMod 930419060873) ^ (3549267 + 3549267) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 3549267 * (3 : ZMod 930419060873) ^ 3549267 := by rw [pow_add]
          _ = 127499404569 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 930419060873) ^ 14197068 = 459936527707 := by
        calc
          (3 : ZMod 930419060873) ^ 14197068 = (3 : ZMod 930419060873) ^ (7098534 + 7098534) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 7098534 * (3 : ZMod 930419060873) ^ 7098534 := by rw [pow_add]
          _ = 459936527707 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 930419060873) ^ 28394136 = 866553614141 := by
        calc
          (3 : ZMod 930419060873) ^ 28394136 = (3 : ZMod 930419060873) ^ (14197068 + 14197068) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 14197068 * (3 : ZMod 930419060873) ^ 14197068 := by rw [pow_add]
          _ = 866553614141 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 930419060873) ^ 56788272 = 510165346983 := by
        calc
          (3 : ZMod 930419060873) ^ 56788272 = (3 : ZMod 930419060873) ^ (28394136 + 28394136) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 28394136 * (3 : ZMod 930419060873) ^ 28394136 := by rw [pow_add]
          _ = 510165346983 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 930419060873) ^ 113576545 = 550068223309 := by
        calc
          (3 : ZMod 930419060873) ^ 113576545 = (3 : ZMod 930419060873) ^ (56788272 + 56788272 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 56788272 * (3 : ZMod 930419060873) ^ 56788272) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 550068223309 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 930419060873) ^ 227153091 = 591089684188 := by
        calc
          (3 : ZMod 930419060873) ^ 227153091 = (3 : ZMod 930419060873) ^ (113576545 + 113576545 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 113576545 * (3 : ZMod 930419060873) ^ 113576545) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 591089684188 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 930419060873) ^ 454306182 = 835432918051 := by
        calc
          (3 : ZMod 930419060873) ^ 454306182 = (3 : ZMod 930419060873) ^ (227153091 + 227153091) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 227153091 * (3 : ZMod 930419060873) ^ 227153091 := by rw [pow_add]
          _ = 835432918051 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 930419060873) ^ 908612364 = 786052151711 := by
        calc
          (3 : ZMod 930419060873) ^ 908612364 = (3 : ZMod 930419060873) ^ (454306182 + 454306182) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 454306182 * (3 : ZMod 930419060873) ^ 454306182 := by rw [pow_add]
          _ = 786052151711 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 930419060873) ^ 1817224728 = 723383670557 := by
        calc
          (3 : ZMod 930419060873) ^ 1817224728 = (3 : ZMod 930419060873) ^ (908612364 + 908612364) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 908612364 * (3 : ZMod 930419060873) ^ 908612364 := by rw [pow_add]
          _ = 723383670557 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 930419060873) ^ 3634449456 = 341934943354 := by
        calc
          (3 : ZMod 930419060873) ^ 3634449456 = (3 : ZMod 930419060873) ^ (1817224728 + 1817224728) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 1817224728 * (3 : ZMod 930419060873) ^ 1817224728 := by rw [pow_add]
          _ = 341934943354 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 930419060873) ^ 7268898913 = 178070066001 := by
        calc
          (3 : ZMod 930419060873) ^ 7268898913 = (3 : ZMod 930419060873) ^ (3634449456 + 3634449456 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 3634449456 * (3 : ZMod 930419060873) ^ 3634449456) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 178070066001 := by rw [fermat_31]; decide
      have fermat_33 : (3 : ZMod 930419060873) ^ 14537797826 = 357083947029 := by
        calc
          (3 : ZMod 930419060873) ^ 14537797826 = (3 : ZMod 930419060873) ^ (7268898913 + 7268898913) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 7268898913 * (3 : ZMod 930419060873) ^ 7268898913 := by rw [pow_add]
          _ = 357083947029 := by rw [fermat_32]; decide
      have fermat_34 : (3 : ZMod 930419060873) ^ 29075595652 = 730945606920 := by
        calc
          (3 : ZMod 930419060873) ^ 29075595652 = (3 : ZMod 930419060873) ^ (14537797826 + 14537797826) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 14537797826 * (3 : ZMod 930419060873) ^ 14537797826 := by rw [pow_add]
          _ = 730945606920 := by rw [fermat_33]; decide
      have fermat_35 : (3 : ZMod 930419060873) ^ 58151191304 = 688791907625 := by
        calc
          (3 : ZMod 930419060873) ^ 58151191304 = (3 : ZMod 930419060873) ^ (29075595652 + 29075595652) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 29075595652 * (3 : ZMod 930419060873) ^ 29075595652 := by rw [pow_add]
          _ = 688791907625 := by rw [fermat_34]; decide
      have fermat_36 : (3 : ZMod 930419060873) ^ 116302382609 = 405385668664 := by
        calc
          (3 : ZMod 930419060873) ^ 116302382609 = (3 : ZMod 930419060873) ^ (58151191304 + 58151191304 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 58151191304 * (3 : ZMod 930419060873) ^ 58151191304) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 405385668664 := by rw [fermat_35]; decide
      have fermat_37 : (3 : ZMod 930419060873) ^ 232604765218 = 345957872813 := by
        calc
          (3 : ZMod 930419060873) ^ 232604765218 = (3 : ZMod 930419060873) ^ (116302382609 + 116302382609) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 116302382609 * (3 : ZMod 930419060873) ^ 116302382609 := by rw [pow_add]
          _ = 345957872813 := by rw [fermat_36]; decide
      have fermat_38 : (3 : ZMod 930419060873) ^ 465209530436 = 930419060872 := by
        calc
          (3 : ZMod 930419060873) ^ 465209530436 = (3 : ZMod 930419060873) ^ (232604765218 + 232604765218) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 232604765218 * (3 : ZMod 930419060873) ^ 232604765218 := by rw [pow_add]
          _ = 930419060872 := by rw [fermat_37]; decide
      have fermat_39 : (3 : ZMod 930419060873) ^ 930419060872 = 1 := by
        calc
          (3 : ZMod 930419060873) ^ 930419060872 = (3 : ZMod 930419060873) ^ (465209530436 + 465209530436) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 465209530436 * (3 : ZMod 930419060873) ^ 465209530436 := by rw [pow_add]
          _ = 1 := by rw [fermat_38]; decide
      simpa using fermat_39
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (727, 1), (751, 1), (30431, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (727, 1), (751, 1), (30431, 1)] : List FactorBlock).map factorBlockValue).prod = 930419060873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 930419060873) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 930419060873) ^ 3 = 27 := by
        calc
          (3 : ZMod 930419060873) ^ 3 = (3 : ZMod 930419060873) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 1 * (3 : ZMod 930419060873) ^ 1) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 930419060873) ^ 6 = 729 := by
        calc
          (3 : ZMod 930419060873) ^ 6 = (3 : ZMod 930419060873) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 3 * (3 : ZMod 930419060873) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 930419060873) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 930419060873) ^ 13 = (3 : ZMod 930419060873) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 6 * (3 : ZMod 930419060873) ^ 6) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 930419060873) ^ 27 = 182244998003 := by
        calc
          (3 : ZMod 930419060873) ^ 27 = (3 : ZMod 930419060873) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 13 * (3 : ZMod 930419060873) ^ 13) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 182244998003 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 930419060873) ^ 54 = 105489911903 := by
        calc
          (3 : ZMod 930419060873) ^ 54 = (3 : ZMod 930419060873) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 27 * (3 : ZMod 930419060873) ^ 27 := by rw [pow_add]
          _ = 105489911903 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 930419060873) ^ 108 = 422582999547 := by
        calc
          (3 : ZMod 930419060873) ^ 108 = (3 : ZMod 930419060873) ^ (54 + 54) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 54 * (3 : ZMod 930419060873) ^ 54 := by rw [pow_add]
          _ = 422582999547 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 930419060873) ^ 216 = 541795939979 := by
        calc
          (3 : ZMod 930419060873) ^ 216 = (3 : ZMod 930419060873) ^ (108 + 108) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 108 * (3 : ZMod 930419060873) ^ 108 := by rw [pow_add]
          _ = 541795939979 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 930419060873) ^ 433 = 162041906553 := by
        calc
          (3 : ZMod 930419060873) ^ 433 = (3 : ZMod 930419060873) ^ (216 + 216 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 216 * (3 : ZMod 930419060873) ^ 216) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 162041906553 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 930419060873) ^ 866 = 492081891886 := by
        calc
          (3 : ZMod 930419060873) ^ 866 = (3 : ZMod 930419060873) ^ (433 + 433) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 433 * (3 : ZMod 930419060873) ^ 433 := by rw [pow_add]
          _ = 492081891886 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 930419060873) ^ 1733 = 620608013805 := by
        calc
          (3 : ZMod 930419060873) ^ 1733 = (3 : ZMod 930419060873) ^ (866 + 866 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 866 * (3 : ZMod 930419060873) ^ 866) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 620608013805 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 930419060873) ^ 3466 = 925734189695 := by
        calc
          (3 : ZMod 930419060873) ^ 3466 = (3 : ZMod 930419060873) ^ (1733 + 1733) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 1733 * (3 : ZMod 930419060873) ^ 1733 := by rw [pow_add]
          _ = 925734189695 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 930419060873) ^ 6932 = 794507231087 := by
        calc
          (3 : ZMod 930419060873) ^ 6932 = (3 : ZMod 930419060873) ^ (3466 + 3466) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 3466 * (3 : ZMod 930419060873) ^ 3466 := by rw [pow_add]
          _ = 794507231087 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 930419060873) ^ 13864 = 163520009716 := by
        calc
          (3 : ZMod 930419060873) ^ 13864 = (3 : ZMod 930419060873) ^ (6932 + 6932) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 6932 * (3 : ZMod 930419060873) ^ 6932 := by rw [pow_add]
          _ = 163520009716 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 930419060873) ^ 27728 = 125449354407 := by
        calc
          (3 : ZMod 930419060873) ^ 27728 = (3 : ZMod 930419060873) ^ (13864 + 13864) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 13864 * (3 : ZMod 930419060873) ^ 13864 := by rw [pow_add]
          _ = 125449354407 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 930419060873) ^ 55457 = 202925566052 := by
        calc
          (3 : ZMod 930419060873) ^ 55457 = (3 : ZMod 930419060873) ^ (27728 + 27728 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 27728 * (3 : ZMod 930419060873) ^ 27728) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 202925566052 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 930419060873) ^ 110914 = 165356390607 := by
        calc
          (3 : ZMod 930419060873) ^ 110914 = (3 : ZMod 930419060873) ^ (55457 + 55457) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 55457 * (3 : ZMod 930419060873) ^ 55457 := by rw [pow_add]
          _ = 165356390607 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 930419060873) ^ 221829 = 593464808959 := by
        calc
          (3 : ZMod 930419060873) ^ 221829 = (3 : ZMod 930419060873) ^ (110914 + 110914 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 110914 * (3 : ZMod 930419060873) ^ 110914) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 593464808959 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 930419060873) ^ 443658 = 401463301647 := by
        calc
          (3 : ZMod 930419060873) ^ 443658 = (3 : ZMod 930419060873) ^ (221829 + 221829) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 221829 * (3 : ZMod 930419060873) ^ 221829 := by rw [pow_add]
          _ = 401463301647 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 930419060873) ^ 887316 = 80982039690 := by
        calc
          (3 : ZMod 930419060873) ^ 887316 = (3 : ZMod 930419060873) ^ (443658 + 443658) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 443658 * (3 : ZMod 930419060873) ^ 443658 := by rw [pow_add]
          _ = 80982039690 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 930419060873) ^ 1774633 = 77388207795 := by
        calc
          (3 : ZMod 930419060873) ^ 1774633 = (3 : ZMod 930419060873) ^ (887316 + 887316 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 887316 * (3 : ZMod 930419060873) ^ 887316) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 77388207795 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 930419060873) ^ 3549267 = 740853704057 := by
        calc
          (3 : ZMod 930419060873) ^ 3549267 = (3 : ZMod 930419060873) ^ (1774633 + 1774633 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 1774633 * (3 : ZMod 930419060873) ^ 1774633) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 740853704057 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 930419060873) ^ 7098534 = 127499404569 := by
        calc
          (3 : ZMod 930419060873) ^ 7098534 = (3 : ZMod 930419060873) ^ (3549267 + 3549267) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 3549267 * (3 : ZMod 930419060873) ^ 3549267 := by rw [pow_add]
          _ = 127499404569 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 930419060873) ^ 14197068 = 459936527707 := by
        calc
          (3 : ZMod 930419060873) ^ 14197068 = (3 : ZMod 930419060873) ^ (7098534 + 7098534) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 7098534 * (3 : ZMod 930419060873) ^ 7098534 := by rw [pow_add]
          _ = 459936527707 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 930419060873) ^ 28394136 = 866553614141 := by
        calc
          (3 : ZMod 930419060873) ^ 28394136 = (3 : ZMod 930419060873) ^ (14197068 + 14197068) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 14197068 * (3 : ZMod 930419060873) ^ 14197068 := by rw [pow_add]
          _ = 866553614141 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 930419060873) ^ 56788272 = 510165346983 := by
        calc
          (3 : ZMod 930419060873) ^ 56788272 = (3 : ZMod 930419060873) ^ (28394136 + 28394136) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 28394136 * (3 : ZMod 930419060873) ^ 28394136 := by rw [pow_add]
          _ = 510165346983 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 930419060873) ^ 113576545 = 550068223309 := by
        calc
          (3 : ZMod 930419060873) ^ 113576545 = (3 : ZMod 930419060873) ^ (56788272 + 56788272 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 56788272 * (3 : ZMod 930419060873) ^ 56788272) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 550068223309 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 930419060873) ^ 227153091 = 591089684188 := by
        calc
          (3 : ZMod 930419060873) ^ 227153091 = (3 : ZMod 930419060873) ^ (113576545 + 113576545 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 113576545 * (3 : ZMod 930419060873) ^ 113576545) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 591089684188 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 930419060873) ^ 454306182 = 835432918051 := by
        calc
          (3 : ZMod 930419060873) ^ 454306182 = (3 : ZMod 930419060873) ^ (227153091 + 227153091) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 227153091 * (3 : ZMod 930419060873) ^ 227153091 := by rw [pow_add]
          _ = 835432918051 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 930419060873) ^ 908612364 = 786052151711 := by
        calc
          (3 : ZMod 930419060873) ^ 908612364 = (3 : ZMod 930419060873) ^ (454306182 + 454306182) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 454306182 * (3 : ZMod 930419060873) ^ 454306182 := by rw [pow_add]
          _ = 786052151711 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 930419060873) ^ 1817224728 = 723383670557 := by
        calc
          (3 : ZMod 930419060873) ^ 1817224728 = (3 : ZMod 930419060873) ^ (908612364 + 908612364) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 908612364 * (3 : ZMod 930419060873) ^ 908612364 := by rw [pow_add]
          _ = 723383670557 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 930419060873) ^ 3634449456 = 341934943354 := by
        calc
          (3 : ZMod 930419060873) ^ 3634449456 = (3 : ZMod 930419060873) ^ (1817224728 + 1817224728) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 1817224728 * (3 : ZMod 930419060873) ^ 1817224728 := by rw [pow_add]
          _ = 341934943354 := by rw [factor_0_30]; decide
      have factor_0_32 : (3 : ZMod 930419060873) ^ 7268898913 = 178070066001 := by
        calc
          (3 : ZMod 930419060873) ^ 7268898913 = (3 : ZMod 930419060873) ^ (3634449456 + 3634449456 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 3634449456 * (3 : ZMod 930419060873) ^ 3634449456) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 178070066001 := by rw [factor_0_31]; decide
      have factor_0_33 : (3 : ZMod 930419060873) ^ 14537797826 = 357083947029 := by
        calc
          (3 : ZMod 930419060873) ^ 14537797826 = (3 : ZMod 930419060873) ^ (7268898913 + 7268898913) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 7268898913 * (3 : ZMod 930419060873) ^ 7268898913 := by rw [pow_add]
          _ = 357083947029 := by rw [factor_0_32]; decide
      have factor_0_34 : (3 : ZMod 930419060873) ^ 29075595652 = 730945606920 := by
        calc
          (3 : ZMod 930419060873) ^ 29075595652 = (3 : ZMod 930419060873) ^ (14537797826 + 14537797826) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 14537797826 * (3 : ZMod 930419060873) ^ 14537797826 := by rw [pow_add]
          _ = 730945606920 := by rw [factor_0_33]; decide
      have factor_0_35 : (3 : ZMod 930419060873) ^ 58151191304 = 688791907625 := by
        calc
          (3 : ZMod 930419060873) ^ 58151191304 = (3 : ZMod 930419060873) ^ (29075595652 + 29075595652) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 29075595652 * (3 : ZMod 930419060873) ^ 29075595652 := by rw [pow_add]
          _ = 688791907625 := by rw [factor_0_34]; decide
      have factor_0_36 : (3 : ZMod 930419060873) ^ 116302382609 = 405385668664 := by
        calc
          (3 : ZMod 930419060873) ^ 116302382609 = (3 : ZMod 930419060873) ^ (58151191304 + 58151191304 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 58151191304 * (3 : ZMod 930419060873) ^ 58151191304) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 405385668664 := by rw [factor_0_35]; decide
      have factor_0_37 : (3 : ZMod 930419060873) ^ 232604765218 = 345957872813 := by
        calc
          (3 : ZMod 930419060873) ^ 232604765218 = (3 : ZMod 930419060873) ^ (116302382609 + 116302382609) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 116302382609 * (3 : ZMod 930419060873) ^ 116302382609 := by rw [pow_add]
          _ = 345957872813 := by rw [factor_0_36]; decide
      have factor_0_38 : (3 : ZMod 930419060873) ^ 465209530436 = 930419060872 := by
        calc
          (3 : ZMod 930419060873) ^ 465209530436 = (3 : ZMod 930419060873) ^ (232604765218 + 232604765218) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 232604765218 * (3 : ZMod 930419060873) ^ 232604765218 := by rw [pow_add]
          _ = 930419060872 := by rw [factor_0_37]; decide
      change (3 : ZMod 930419060873) ^ 465209530436 ≠ 1
      rw [factor_0_38]
      decide
    ·
      have factor_1_0 : (3 : ZMod 930419060873) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 930419060873) ^ 3 = 27 := by
        calc
          (3 : ZMod 930419060873) ^ 3 = (3 : ZMod 930419060873) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 1 * (3 : ZMod 930419060873) ^ 1) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 930419060873) ^ 7 = 2187 := by
        calc
          (3 : ZMod 930419060873) ^ 7 = (3 : ZMod 930419060873) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 3 * (3 : ZMod 930419060873) ^ 3) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 930419060873) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 930419060873) ^ 15 = (3 : ZMod 930419060873) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 7 * (3 : ZMod 930419060873) ^ 7) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 930419060873) ^ 30 = 268519641716 := by
        calc
          (3 : ZMod 930419060873) ^ 30 = (3 : ZMod 930419060873) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 15 * (3 : ZMod 930419060873) ^ 15 := by rw [pow_add]
          _ = 268519641716 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 930419060873) ^ 61 = 892929296230 := by
        calc
          (3 : ZMod 930419060873) ^ 61 = (3 : ZMod 930419060873) ^ (30 + 30 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 30 * (3 : ZMod 930419060873) ^ 30) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 892929296230 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 930419060873) ^ 123 = 802494525638 := by
        calc
          (3 : ZMod 930419060873) ^ 123 = (3 : ZMod 930419060873) ^ (61 + 61 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 61 * (3 : ZMod 930419060873) ^ 61) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 802494525638 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 930419060873) ^ 247 = 730086675765 := by
        calc
          (3 : ZMod 930419060873) ^ 247 = (3 : ZMod 930419060873) ^ (123 + 123 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 123 * (3 : ZMod 930419060873) ^ 123) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 730086675765 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 930419060873) ^ 495 = 715441491960 := by
        calc
          (3 : ZMod 930419060873) ^ 495 = (3 : ZMod 930419060873) ^ (247 + 247 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 247 * (3 : ZMod 930419060873) ^ 247) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 715441491960 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 930419060873) ^ 990 = 433616510269 := by
        calc
          (3 : ZMod 930419060873) ^ 990 = (3 : ZMod 930419060873) ^ (495 + 495) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 495 * (3 : ZMod 930419060873) ^ 495 := by rw [pow_add]
          _ = 433616510269 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 930419060873) ^ 1980 = 581472290739 := by
        calc
          (3 : ZMod 930419060873) ^ 1980 = (3 : ZMod 930419060873) ^ (990 + 990) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 990 * (3 : ZMod 930419060873) ^ 990 := by rw [pow_add]
          _ = 581472290739 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 930419060873) ^ 3961 = 654461619607 := by
        calc
          (3 : ZMod 930419060873) ^ 3961 = (3 : ZMod 930419060873) ^ (1980 + 1980 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 1980 * (3 : ZMod 930419060873) ^ 1980) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 654461619607 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 930419060873) ^ 7922 = 523707356771 := by
        calc
          (3 : ZMod 930419060873) ^ 7922 = (3 : ZMod 930419060873) ^ (3961 + 3961) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 3961 * (3 : ZMod 930419060873) ^ 3961 := by rw [pow_add]
          _ = 523707356771 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 930419060873) ^ 15844 = 621480717624 := by
        calc
          (3 : ZMod 930419060873) ^ 15844 = (3 : ZMod 930419060873) ^ (7922 + 7922) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 7922 * (3 : ZMod 930419060873) ^ 7922 := by rw [pow_add]
          _ = 621480717624 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 930419060873) ^ 31689 = 450740767654 := by
        calc
          (3 : ZMod 930419060873) ^ 31689 = (3 : ZMod 930419060873) ^ (15844 + 15844 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 15844 * (3 : ZMod 930419060873) ^ 15844) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 450740767654 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 930419060873) ^ 63379 = 700866678845 := by
        calc
          (3 : ZMod 930419060873) ^ 63379 = (3 : ZMod 930419060873) ^ (31689 + 31689 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 31689 * (3 : ZMod 930419060873) ^ 31689) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 700866678845 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 930419060873) ^ 126759 = 388626621615 := by
        calc
          (3 : ZMod 930419060873) ^ 126759 = (3 : ZMod 930419060873) ^ (63379 + 63379 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 63379 * (3 : ZMod 930419060873) ^ 63379) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 388626621615 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 930419060873) ^ 253519 = 902099162778 := by
        calc
          (3 : ZMod 930419060873) ^ 253519 = (3 : ZMod 930419060873) ^ (126759 + 126759 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 126759 * (3 : ZMod 930419060873) ^ 126759) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 902099162778 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 930419060873) ^ 507038 = 421752767756 := by
        calc
          (3 : ZMod 930419060873) ^ 507038 = (3 : ZMod 930419060873) ^ (253519 + 253519) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 253519 * (3 : ZMod 930419060873) ^ 253519 := by rw [pow_add]
          _ = 421752767756 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 930419060873) ^ 1014076 = 611013237085 := by
        calc
          (3 : ZMod 930419060873) ^ 1014076 = (3 : ZMod 930419060873) ^ (507038 + 507038) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 507038 * (3 : ZMod 930419060873) ^ 507038 := by rw [pow_add]
          _ = 611013237085 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 930419060873) ^ 2028152 = 14181025255 := by
        calc
          (3 : ZMod 930419060873) ^ 2028152 = (3 : ZMod 930419060873) ^ (1014076 + 1014076) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 1014076 * (3 : ZMod 930419060873) ^ 1014076 := by rw [pow_add]
          _ = 14181025255 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 930419060873) ^ 4056305 = 720076151222 := by
        calc
          (3 : ZMod 930419060873) ^ 4056305 = (3 : ZMod 930419060873) ^ (2028152 + 2028152 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 2028152 * (3 : ZMod 930419060873) ^ 2028152) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 720076151222 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 930419060873) ^ 8112610 = 428928612217 := by
        calc
          (3 : ZMod 930419060873) ^ 8112610 = (3 : ZMod 930419060873) ^ (4056305 + 4056305) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 4056305 * (3 : ZMod 930419060873) ^ 4056305 := by rw [pow_add]
          _ = 428928612217 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 930419060873) ^ 16225220 = 852774945982 := by
        calc
          (3 : ZMod 930419060873) ^ 16225220 = (3 : ZMod 930419060873) ^ (8112610 + 8112610) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 8112610 * (3 : ZMod 930419060873) ^ 8112610 := by rw [pow_add]
          _ = 852774945982 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 930419060873) ^ 32450441 = 73158483428 := by
        calc
          (3 : ZMod 930419060873) ^ 32450441 = (3 : ZMod 930419060873) ^ (16225220 + 16225220 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 16225220 * (3 : ZMod 930419060873) ^ 16225220) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 73158483428 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 930419060873) ^ 64900883 = 148243503441 := by
        calc
          (3 : ZMod 930419060873) ^ 64900883 = (3 : ZMod 930419060873) ^ (32450441 + 32450441 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 32450441 * (3 : ZMod 930419060873) ^ 32450441) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 148243503441 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 930419060873) ^ 129801766 = 674045672164 := by
        calc
          (3 : ZMod 930419060873) ^ 129801766 = (3 : ZMod 930419060873) ^ (64900883 + 64900883) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 64900883 * (3 : ZMod 930419060873) ^ 64900883 := by rw [pow_add]
          _ = 674045672164 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 930419060873) ^ 259603532 = 122076630726 := by
        calc
          (3 : ZMod 930419060873) ^ 259603532 = (3 : ZMod 930419060873) ^ (129801766 + 129801766) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 129801766 * (3 : ZMod 930419060873) ^ 129801766 := by rw [pow_add]
          _ = 122076630726 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 930419060873) ^ 519207065 = 793853162272 := by
        calc
          (3 : ZMod 930419060873) ^ 519207065 = (3 : ZMod 930419060873) ^ (259603532 + 259603532 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 259603532 * (3 : ZMod 930419060873) ^ 259603532) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 793853162272 := by rw [factor_1_27]; decide
      have factor_1_29 : (3 : ZMod 930419060873) ^ 1038414130 = 538263038061 := by
        calc
          (3 : ZMod 930419060873) ^ 1038414130 = (3 : ZMod 930419060873) ^ (519207065 + 519207065) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 519207065 * (3 : ZMod 930419060873) ^ 519207065 := by rw [pow_add]
          _ = 538263038061 := by rw [factor_1_28]; decide
      have factor_1_30 : (3 : ZMod 930419060873) ^ 2076828260 = 811345382482 := by
        calc
          (3 : ZMod 930419060873) ^ 2076828260 = (3 : ZMod 930419060873) ^ (1038414130 + 1038414130) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 1038414130 * (3 : ZMod 930419060873) ^ 1038414130 := by rw [pow_add]
          _ = 811345382482 := by rw [factor_1_29]; decide
      have factor_1_31 : (3 : ZMod 930419060873) ^ 4153656521 = 24396730986 := by
        calc
          (3 : ZMod 930419060873) ^ 4153656521 = (3 : ZMod 930419060873) ^ (2076828260 + 2076828260 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 2076828260 * (3 : ZMod 930419060873) ^ 2076828260) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 24396730986 := by rw [factor_1_30]; decide
      have factor_1_32 : (3 : ZMod 930419060873) ^ 8307313043 = 431971900664 := by
        calc
          (3 : ZMod 930419060873) ^ 8307313043 = (3 : ZMod 930419060873) ^ (4153656521 + 4153656521 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 4153656521 * (3 : ZMod 930419060873) ^ 4153656521) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 431971900664 := by rw [factor_1_31]; decide
      have factor_1_33 : (3 : ZMod 930419060873) ^ 16614626087 = 805868086875 := by
        calc
          (3 : ZMod 930419060873) ^ 16614626087 = (3 : ZMod 930419060873) ^ (8307313043 + 8307313043 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 8307313043 * (3 : ZMod 930419060873) ^ 8307313043) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 805868086875 := by rw [factor_1_32]; decide
      have factor_1_34 : (3 : ZMod 930419060873) ^ 33229252174 = 352982226436 := by
        calc
          (3 : ZMod 930419060873) ^ 33229252174 = (3 : ZMod 930419060873) ^ (16614626087 + 16614626087) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 16614626087 * (3 : ZMod 930419060873) ^ 16614626087 := by rw [pow_add]
          _ = 352982226436 := by rw [factor_1_33]; decide
      have factor_1_35 : (3 : ZMod 930419060873) ^ 66458504348 = 875495702692 := by
        calc
          (3 : ZMod 930419060873) ^ 66458504348 = (3 : ZMod 930419060873) ^ (33229252174 + 33229252174) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 33229252174 * (3 : ZMod 930419060873) ^ 33229252174 := by rw [pow_add]
          _ = 875495702692 := by rw [factor_1_34]; decide
      have factor_1_36 : (3 : ZMod 930419060873) ^ 132917008696 = 610397919926 := by
        calc
          (3 : ZMod 930419060873) ^ 132917008696 = (3 : ZMod 930419060873) ^ (66458504348 + 66458504348) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 66458504348 * (3 : ZMod 930419060873) ^ 66458504348 := by rw [pow_add]
          _ = 610397919926 := by rw [factor_1_35]; decide
      change (3 : ZMod 930419060873) ^ 132917008696 ≠ 1
      rw [factor_1_36]
      decide
    ·
      have factor_2_0 : (3 : ZMod 930419060873) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 930419060873) ^ 2 = 9 := by
        calc
          (3 : ZMod 930419060873) ^ 2 = (3 : ZMod 930419060873) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 1 * (3 : ZMod 930419060873) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 930419060873) ^ 4 = 81 := by
        calc
          (3 : ZMod 930419060873) ^ 4 = (3 : ZMod 930419060873) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 2 * (3 : ZMod 930419060873) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 930419060873) ^ 9 = 19683 := by
        calc
          (3 : ZMod 930419060873) ^ 9 = (3 : ZMod 930419060873) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 4 * (3 : ZMod 930419060873) ^ 4) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 930419060873) ^ 19 = 1162261467 := by
        calc
          (3 : ZMod 930419060873) ^ 19 = (3 : ZMod 930419060873) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 9 * (3 : ZMod 930419060873) ^ 9) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 1162261467 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 930419060873) ^ 38 = 474087066087 := by
        calc
          (3 : ZMod 930419060873) ^ 38 = (3 : ZMod 930419060873) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 19 * (3 : ZMod 930419060873) ^ 19 := by rw [pow_add]
          _ = 474087066087 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 930419060873) ^ 76 = 450853464590 := by
        calc
          (3 : ZMod 930419060873) ^ 76 = (3 : ZMod 930419060873) ^ (38 + 38) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 38 * (3 : ZMod 930419060873) ^ 38 := by rw [pow_add]
          _ = 450853464590 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 930419060873) ^ 152 = 747915516018 := by
        calc
          (3 : ZMod 930419060873) ^ 152 = (3 : ZMod 930419060873) ^ (76 + 76) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 76 * (3 : ZMod 930419060873) ^ 76 := by rw [pow_add]
          _ = 747915516018 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 930419060873) ^ 305 = 671615552794 := by
        calc
          (3 : ZMod 930419060873) ^ 305 = (3 : ZMod 930419060873) ^ (152 + 152 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 152 * (3 : ZMod 930419060873) ^ 152) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 671615552794 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 930419060873) ^ 610 = 304279022654 := by
        calc
          (3 : ZMod 930419060873) ^ 610 = (3 : ZMod 930419060873) ^ (305 + 305) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 305 * (3 : ZMod 930419060873) ^ 305 := by rw [pow_add]
          _ = 304279022654 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 930419060873) ^ 1220 = 466400922401 := by
        calc
          (3 : ZMod 930419060873) ^ 1220 = (3 : ZMod 930419060873) ^ (610 + 610) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 610 * (3 : ZMod 930419060873) ^ 610 := by rw [pow_add]
          _ = 466400922401 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 930419060873) ^ 2441 = 408028118264 := by
        calc
          (3 : ZMod 930419060873) ^ 2441 = (3 : ZMod 930419060873) ^ (1220 + 1220 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 1220 * (3 : ZMod 930419060873) ^ 1220) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 408028118264 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 930419060873) ^ 4882 = 49413604901 := by
        calc
          (3 : ZMod 930419060873) ^ 4882 = (3 : ZMod 930419060873) ^ (2441 + 2441) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 2441 * (3 : ZMod 930419060873) ^ 2441 := by rw [pow_add]
          _ = 49413604901 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 930419060873) ^ 9764 = 227437438230 := by
        calc
          (3 : ZMod 930419060873) ^ 9764 = (3 : ZMod 930419060873) ^ (4882 + 4882) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 4882 * (3 : ZMod 930419060873) ^ 4882 := by rw [pow_add]
          _ = 227437438230 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 930419060873) ^ 19528 = 55525104740 := by
        calc
          (3 : ZMod 930419060873) ^ 19528 = (3 : ZMod 930419060873) ^ (9764 + 9764) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 9764 * (3 : ZMod 930419060873) ^ 9764 := by rw [pow_add]
          _ = 55525104740 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 930419060873) ^ 39056 = 333759752135 := by
        calc
          (3 : ZMod 930419060873) ^ 39056 = (3 : ZMod 930419060873) ^ (19528 + 19528) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 19528 * (3 : ZMod 930419060873) ^ 19528 := by rw [pow_add]
          _ = 333759752135 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 930419060873) ^ 78113 = 568853594092 := by
        calc
          (3 : ZMod 930419060873) ^ 78113 = (3 : ZMod 930419060873) ^ (39056 + 39056 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 39056 * (3 : ZMod 930419060873) ^ 39056) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 568853594092 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 930419060873) ^ 156226 = 429678749114 := by
        calc
          (3 : ZMod 930419060873) ^ 156226 = (3 : ZMod 930419060873) ^ (78113 + 78113) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 78113 * (3 : ZMod 930419060873) ^ 78113 := by rw [pow_add]
          _ = 429678749114 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 930419060873) ^ 312452 = 807332530647 := by
        calc
          (3 : ZMod 930419060873) ^ 312452 = (3 : ZMod 930419060873) ^ (156226 + 156226) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 156226 * (3 : ZMod 930419060873) ^ 156226 := by rw [pow_add]
          _ = 807332530647 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 930419060873) ^ 624905 = 237333893529 := by
        calc
          (3 : ZMod 930419060873) ^ 624905 = (3 : ZMod 930419060873) ^ (312452 + 312452 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 312452 * (3 : ZMod 930419060873) ^ 312452) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 237333893529 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 930419060873) ^ 1249810 = 358074455629 := by
        calc
          (3 : ZMod 930419060873) ^ 1249810 = (3 : ZMod 930419060873) ^ (624905 + 624905) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 624905 * (3 : ZMod 930419060873) ^ 624905 := by rw [pow_add]
          _ = 358074455629 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 930419060873) ^ 2499621 = 640134495844 := by
        calc
          (3 : ZMod 930419060873) ^ 2499621 = (3 : ZMod 930419060873) ^ (1249810 + 1249810 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 1249810 * (3 : ZMod 930419060873) ^ 1249810) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 640134495844 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 930419060873) ^ 4999242 = 511148449580 := by
        calc
          (3 : ZMod 930419060873) ^ 4999242 = (3 : ZMod 930419060873) ^ (2499621 + 2499621) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 2499621 * (3 : ZMod 930419060873) ^ 2499621 := by rw [pow_add]
          _ = 511148449580 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 930419060873) ^ 9998485 = 855653652028 := by
        calc
          (3 : ZMod 930419060873) ^ 9998485 = (3 : ZMod 930419060873) ^ (4999242 + 4999242 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 4999242 * (3 : ZMod 930419060873) ^ 4999242) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 855653652028 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 930419060873) ^ 19996970 = 813026414768 := by
        calc
          (3 : ZMod 930419060873) ^ 19996970 = (3 : ZMod 930419060873) ^ (9998485 + 9998485) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 9998485 * (3 : ZMod 930419060873) ^ 9998485 := by rw [pow_add]
          _ = 813026414768 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 930419060873) ^ 39993941 = 129065109564 := by
        calc
          (3 : ZMod 930419060873) ^ 39993941 = (3 : ZMod 930419060873) ^ (19996970 + 19996970 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 19996970 * (3 : ZMod 930419060873) ^ 19996970) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 129065109564 := by rw [factor_2_24]; decide
      have factor_2_26 : (3 : ZMod 930419060873) ^ 79987883 = 591056283139 := by
        calc
          (3 : ZMod 930419060873) ^ 79987883 = (3 : ZMod 930419060873) ^ (39993941 + 39993941 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 39993941 * (3 : ZMod 930419060873) ^ 39993941) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 591056283139 := by rw [factor_2_25]; decide
      have factor_2_27 : (3 : ZMod 930419060873) ^ 159975767 = 649893208809 := by
        calc
          (3 : ZMod 930419060873) ^ 159975767 = (3 : ZMod 930419060873) ^ (79987883 + 79987883 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 79987883 * (3 : ZMod 930419060873) ^ 79987883) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 649893208809 := by rw [factor_2_26]; decide
      have factor_2_28 : (3 : ZMod 930419060873) ^ 319951534 = 152733568076 := by
        calc
          (3 : ZMod 930419060873) ^ 319951534 = (3 : ZMod 930419060873) ^ (159975767 + 159975767) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 159975767 * (3 : ZMod 930419060873) ^ 159975767 := by rw [pow_add]
          _ = 152733568076 := by rw [factor_2_27]; decide
      have factor_2_29 : (3 : ZMod 930419060873) ^ 639903068 = 782805017281 := by
        calc
          (3 : ZMod 930419060873) ^ 639903068 = (3 : ZMod 930419060873) ^ (319951534 + 319951534) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 319951534 * (3 : ZMod 930419060873) ^ 319951534 := by rw [pow_add]
          _ = 782805017281 := by rw [factor_2_28]; decide
      have factor_2_30 : (3 : ZMod 930419060873) ^ 1279806136 = 11736678947 := by
        calc
          (3 : ZMod 930419060873) ^ 1279806136 = (3 : ZMod 930419060873) ^ (639903068 + 639903068) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 639903068 * (3 : ZMod 930419060873) ^ 639903068 := by rw [pow_add]
          _ = 11736678947 := by rw [factor_2_29]; decide
      change (3 : ZMod 930419060873) ^ 1279806136 ≠ 1
      rw [factor_2_30]
      decide
    ·
      have factor_3_0 : (3 : ZMod 930419060873) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 930419060873) ^ 2 = 9 := by
        calc
          (3 : ZMod 930419060873) ^ 2 = (3 : ZMod 930419060873) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 1 * (3 : ZMod 930419060873) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 930419060873) ^ 4 = 81 := by
        calc
          (3 : ZMod 930419060873) ^ 4 = (3 : ZMod 930419060873) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 2 * (3 : ZMod 930419060873) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 930419060873) ^ 9 = 19683 := by
        calc
          (3 : ZMod 930419060873) ^ 9 = (3 : ZMod 930419060873) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 4 * (3 : ZMod 930419060873) ^ 4) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 930419060873) ^ 18 = 387420489 := by
        calc
          (3 : ZMod 930419060873) ^ 18 = (3 : ZMod 930419060873) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 9 * (3 : ZMod 930419060873) ^ 9 := by rw [pow_add]
          _ = 387420489 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 930419060873) ^ 36 = 362816027634 := by
        calc
          (3 : ZMod 930419060873) ^ 36 = (3 : ZMod 930419060873) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 18 * (3 : ZMod 930419060873) ^ 18 := by rw [pow_add]
          _ = 362816027634 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 930419060873) ^ 73 = 395757893859 := by
        calc
          (3 : ZMod 930419060873) ^ 73 = (3 : ZMod 930419060873) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 36 * (3 : ZMod 930419060873) ^ 36) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 395757893859 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 930419060873) ^ 147 = 554437285110 := by
        calc
          (3 : ZMod 930419060873) ^ 147 = (3 : ZMod 930419060873) ^ (73 + 73 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 73 * (3 : ZMod 930419060873) ^ 73) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 554437285110 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 930419060873) ^ 295 = 684121254915 := by
        calc
          (3 : ZMod 930419060873) ^ 295 = (3 : ZMod 930419060873) ^ (147 + 147 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 147 * (3 : ZMod 930419060873) ^ 147) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 684121254915 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 930419060873) ^ 590 = 347832531940 := by
        calc
          (3 : ZMod 930419060873) ^ 590 = (3 : ZMod 930419060873) ^ (295 + 295) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 295 * (3 : ZMod 930419060873) ^ 295 := by rw [pow_add]
          _ = 347832531940 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 930419060873) ^ 1181 = 409989188880 := by
        calc
          (3 : ZMod 930419060873) ^ 1181 = (3 : ZMod 930419060873) ^ (590 + 590 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 590 * (3 : ZMod 930419060873) ^ 590) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 409989188880 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 930419060873) ^ 2363 = 166285286970 := by
        calc
          (3 : ZMod 930419060873) ^ 2363 = (3 : ZMod 930419060873) ^ (1181 + 1181 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 1181 * (3 : ZMod 930419060873) ^ 1181) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 166285286970 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 930419060873) ^ 4726 = 565152563489 := by
        calc
          (3 : ZMod 930419060873) ^ 4726 = (3 : ZMod 930419060873) ^ (2363 + 2363) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 2363 * (3 : ZMod 930419060873) ^ 2363 := by rw [pow_add]
          _ = 565152563489 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 930419060873) ^ 9452 = 807976621954 := by
        calc
          (3 : ZMod 930419060873) ^ 9452 = (3 : ZMod 930419060873) ^ (4726 + 4726) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 4726 * (3 : ZMod 930419060873) ^ 4726 := by rw [pow_add]
          _ = 807976621954 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 930419060873) ^ 18904 = 138744827872 := by
        calc
          (3 : ZMod 930419060873) ^ 18904 = (3 : ZMod 930419060873) ^ (9452 + 9452) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 9452 * (3 : ZMod 930419060873) ^ 9452 := by rw [pow_add]
          _ = 138744827872 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 930419060873) ^ 37808 = 34534493681 := by
        calc
          (3 : ZMod 930419060873) ^ 37808 = (3 : ZMod 930419060873) ^ (18904 + 18904) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 18904 * (3 : ZMod 930419060873) ^ 18904 := by rw [pow_add]
          _ = 34534493681 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 930419060873) ^ 75616 = 802626429469 := by
        calc
          (3 : ZMod 930419060873) ^ 75616 = (3 : ZMod 930419060873) ^ (37808 + 37808) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 37808 * (3 : ZMod 930419060873) ^ 37808 := by rw [pow_add]
          _ = 802626429469 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 930419060873) ^ 151233 = 213221630997 := by
        calc
          (3 : ZMod 930419060873) ^ 151233 = (3 : ZMod 930419060873) ^ (75616 + 75616 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 75616 * (3 : ZMod 930419060873) ^ 75616) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 213221630997 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 930419060873) ^ 302467 = 406153667443 := by
        calc
          (3 : ZMod 930419060873) ^ 302467 = (3 : ZMod 930419060873) ^ (151233 + 151233 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 151233 * (3 : ZMod 930419060873) ^ 151233) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 406153667443 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 930419060873) ^ 604934 = 207664179682 := by
        calc
          (3 : ZMod 930419060873) ^ 604934 = (3 : ZMod 930419060873) ^ (302467 + 302467) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 302467 * (3 : ZMod 930419060873) ^ 302467 := by rw [pow_add]
          _ = 207664179682 := by rw [factor_3_18]; decide
      have factor_3_20 : (3 : ZMod 930419060873) ^ 1209869 = 138335107091 := by
        calc
          (3 : ZMod 930419060873) ^ 1209869 = (3 : ZMod 930419060873) ^ (604934 + 604934 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 604934 * (3 : ZMod 930419060873) ^ 604934) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 138335107091 := by rw [factor_3_19]; decide
      have factor_3_21 : (3 : ZMod 930419060873) ^ 2419739 = 123465984384 := by
        calc
          (3 : ZMod 930419060873) ^ 2419739 = (3 : ZMod 930419060873) ^ (1209869 + 1209869 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 1209869 * (3 : ZMod 930419060873) ^ 1209869) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 123465984384 := by rw [factor_3_20]; decide
      have factor_3_22 : (3 : ZMod 930419060873) ^ 4839479 = 446003630266 := by
        calc
          (3 : ZMod 930419060873) ^ 4839479 = (3 : ZMod 930419060873) ^ (2419739 + 2419739 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 2419739 * (3 : ZMod 930419060873) ^ 2419739) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 446003630266 := by rw [factor_3_21]; decide
      have factor_3_23 : (3 : ZMod 930419060873) ^ 9678959 = 56187371974 := by
        calc
          (3 : ZMod 930419060873) ^ 9678959 = (3 : ZMod 930419060873) ^ (4839479 + 4839479 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 4839479 * (3 : ZMod 930419060873) ^ 4839479) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 56187371974 := by rw [factor_3_22]; decide
      have factor_3_24 : (3 : ZMod 930419060873) ^ 19357919 = 527839364014 := by
        calc
          (3 : ZMod 930419060873) ^ 19357919 = (3 : ZMod 930419060873) ^ (9678959 + 9678959 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 9678959 * (3 : ZMod 930419060873) ^ 9678959) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 527839364014 := by rw [factor_3_23]; decide
      have factor_3_25 : (3 : ZMod 930419060873) ^ 38715839 = 542028249373 := by
        calc
          (3 : ZMod 930419060873) ^ 38715839 = (3 : ZMod 930419060873) ^ (19357919 + 19357919 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 19357919 * (3 : ZMod 930419060873) ^ 19357919) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 542028249373 := by rw [factor_3_24]; decide
      have factor_3_26 : (3 : ZMod 930419060873) ^ 77431679 = 342034579473 := by
        calc
          (3 : ZMod 930419060873) ^ 77431679 = (3 : ZMod 930419060873) ^ (38715839 + 38715839 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 38715839 * (3 : ZMod 930419060873) ^ 38715839) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 342034579473 := by rw [factor_3_25]; decide
      have factor_3_27 : (3 : ZMod 930419060873) ^ 154863359 = 475854294549 := by
        calc
          (3 : ZMod 930419060873) ^ 154863359 = (3 : ZMod 930419060873) ^ (77431679 + 77431679 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 77431679 * (3 : ZMod 930419060873) ^ 77431679) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 475854294549 := by rw [factor_3_26]; decide
      have factor_3_28 : (3 : ZMod 930419060873) ^ 309726718 = 257041260135 := by
        calc
          (3 : ZMod 930419060873) ^ 309726718 = (3 : ZMod 930419060873) ^ (154863359 + 154863359) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 154863359 * (3 : ZMod 930419060873) ^ 154863359 := by rw [pow_add]
          _ = 257041260135 := by rw [factor_3_27]; decide
      have factor_3_29 : (3 : ZMod 930419060873) ^ 619453436 = 391629826686 := by
        calc
          (3 : ZMod 930419060873) ^ 619453436 = (3 : ZMod 930419060873) ^ (309726718 + 309726718) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 309726718 * (3 : ZMod 930419060873) ^ 309726718 := by rw [pow_add]
          _ = 391629826686 := by rw [factor_3_28]; decide
      have factor_3_30 : (3 : ZMod 930419060873) ^ 1238906872 = 413389997685 := by
        calc
          (3 : ZMod 930419060873) ^ 1238906872 = (3 : ZMod 930419060873) ^ (619453436 + 619453436) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 619453436 * (3 : ZMod 930419060873) ^ 619453436 := by rw [pow_add]
          _ = 413389997685 := by rw [factor_3_29]; decide
      change (3 : ZMod 930419060873) ^ 1238906872 ≠ 1
      rw [factor_3_30]
      decide
    ·
      have factor_4_0 : (3 : ZMod 930419060873) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 930419060873) ^ 3 = 27 := by
        calc
          (3 : ZMod 930419060873) ^ 3 = (3 : ZMod 930419060873) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 1 * (3 : ZMod 930419060873) ^ 1) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 930419060873) ^ 7 = 2187 := by
        calc
          (3 : ZMod 930419060873) ^ 7 = (3 : ZMod 930419060873) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 3 * (3 : ZMod 930419060873) ^ 3) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 930419060873) ^ 14 = 4782969 := by
        calc
          (3 : ZMod 930419060873) ^ 14 = (3 : ZMod 930419060873) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 7 * (3 : ZMod 930419060873) ^ 7 := by rw [pow_add]
          _ = 4782969 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 930419060873) ^ 29 = 709785921154 := by
        calc
          (3 : ZMod 930419060873) ^ 29 = (3 : ZMod 930419060873) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 14 * (3 : ZMod 930419060873) ^ 14) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 709785921154 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 930419060873) ^ 58 = 170911316286 := by
        calc
          (3 : ZMod 930419060873) ^ 58 = (3 : ZMod 930419060873) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 29 * (3 : ZMod 930419060873) ^ 29 := by rw [pow_add]
          _ = 170911316286 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 930419060873) ^ 116 = 848677687200 := by
        calc
          (3 : ZMod 930419060873) ^ 116 = (3 : ZMod 930419060873) ^ (58 + 58) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 58 * (3 : ZMod 930419060873) ^ 58 := by rw [pow_add]
          _ = 848677687200 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 930419060873) ^ 233 = 277879980547 := by
        calc
          (3 : ZMod 930419060873) ^ 233 = (3 : ZMod 930419060873) ^ (116 + 116 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 116 * (3 : ZMod 930419060873) ^ 116) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 277879980547 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 930419060873) ^ 466 = 341315109618 := by
        calc
          (3 : ZMod 930419060873) ^ 466 = (3 : ZMod 930419060873) ^ (233 + 233) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 233 * (3 : ZMod 930419060873) ^ 233 := by rw [pow_add]
          _ = 341315109618 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 930419060873) ^ 933 = 261582473629 := by
        calc
          (3 : ZMod 930419060873) ^ 933 = (3 : ZMod 930419060873) ^ (466 + 466 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 466 * (3 : ZMod 930419060873) ^ 466) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 261582473629 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 930419060873) ^ 1866 = 899059948454 := by
        calc
          (3 : ZMod 930419060873) ^ 1866 = (3 : ZMod 930419060873) ^ (933 + 933) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 933 * (3 : ZMod 930419060873) ^ 933 := by rw [pow_add]
          _ = 899059948454 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 930419060873) ^ 3732 = 845750205951 := by
        calc
          (3 : ZMod 930419060873) ^ 3732 = (3 : ZMod 930419060873) ^ (1866 + 1866) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 1866 * (3 : ZMod 930419060873) ^ 1866 := by rw [pow_add]
          _ = 845750205951 := by rw [factor_4_10]; decide
      have factor_4_12 : (3 : ZMod 930419060873) ^ 7464 = 253490374915 := by
        calc
          (3 : ZMod 930419060873) ^ 7464 = (3 : ZMod 930419060873) ^ (3732 + 3732) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 3732 * (3 : ZMod 930419060873) ^ 3732 := by rw [pow_add]
          _ = 253490374915 := by rw [factor_4_11]; decide
      have factor_4_13 : (3 : ZMod 930419060873) ^ 14929 = 755713985556 := by
        calc
          (3 : ZMod 930419060873) ^ 14929 = (3 : ZMod 930419060873) ^ (7464 + 7464 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 7464 * (3 : ZMod 930419060873) ^ 7464) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 755713985556 := by rw [factor_4_12]; decide
      have factor_4_14 : (3 : ZMod 930419060873) ^ 29858 = 331369569475 := by
        calc
          (3 : ZMod 930419060873) ^ 29858 = (3 : ZMod 930419060873) ^ (14929 + 14929) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 14929 * (3 : ZMod 930419060873) ^ 14929 := by rw [pow_add]
          _ = 331369569475 := by rw [factor_4_13]; decide
      have factor_4_15 : (3 : ZMod 930419060873) ^ 59716 = 778033045221 := by
        calc
          (3 : ZMod 930419060873) ^ 59716 = (3 : ZMod 930419060873) ^ (29858 + 29858) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 29858 * (3 : ZMod 930419060873) ^ 29858 := by rw [pow_add]
          _ = 778033045221 := by rw [factor_4_14]; decide
      have factor_4_16 : (3 : ZMod 930419060873) ^ 119432 = 93485020203 := by
        calc
          (3 : ZMod 930419060873) ^ 119432 = (3 : ZMod 930419060873) ^ (59716 + 59716) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 59716 * (3 : ZMod 930419060873) ^ 59716 := by rw [pow_add]
          _ = 93485020203 := by rw [factor_4_15]; decide
      have factor_4_17 : (3 : ZMod 930419060873) ^ 238864 = 872904903264 := by
        calc
          (3 : ZMod 930419060873) ^ 238864 = (3 : ZMod 930419060873) ^ (119432 + 119432) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 119432 * (3 : ZMod 930419060873) ^ 119432 := by rw [pow_add]
          _ = 872904903264 := by rw [factor_4_16]; decide
      have factor_4_18 : (3 : ZMod 930419060873) ^ 477729 = 840642426821 := by
        calc
          (3 : ZMod 930419060873) ^ 477729 = (3 : ZMod 930419060873) ^ (238864 + 238864 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 238864 * (3 : ZMod 930419060873) ^ 238864) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 840642426821 := by rw [factor_4_17]; decide
      have factor_4_19 : (3 : ZMod 930419060873) ^ 955459 = 242167035821 := by
        calc
          (3 : ZMod 930419060873) ^ 955459 = (3 : ZMod 930419060873) ^ (477729 + 477729 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 477729 * (3 : ZMod 930419060873) ^ 477729) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 242167035821 := by rw [factor_4_18]; decide
      have factor_4_20 : (3 : ZMod 930419060873) ^ 1910919 = 648653945061 := by
        calc
          (3 : ZMod 930419060873) ^ 1910919 = (3 : ZMod 930419060873) ^ (955459 + 955459 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 955459 * (3 : ZMod 930419060873) ^ 955459) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 648653945061 := by rw [factor_4_19]; decide
      have factor_4_21 : (3 : ZMod 930419060873) ^ 3821839 = 81353109607 := by
        calc
          (3 : ZMod 930419060873) ^ 3821839 = (3 : ZMod 930419060873) ^ (1910919 + 1910919 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = ((3 : ZMod 930419060873) ^ 1910919 * (3 : ZMod 930419060873) ^ 1910919) * (3 : ZMod 930419060873) := by rw [pow_succ, pow_add]
          _ = 81353109607 := by rw [factor_4_20]; decide
      have factor_4_22 : (3 : ZMod 930419060873) ^ 7643678 = 857960073686 := by
        calc
          (3 : ZMod 930419060873) ^ 7643678 = (3 : ZMod 930419060873) ^ (3821839 + 3821839) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 3821839 * (3 : ZMod 930419060873) ^ 3821839 := by rw [pow_add]
          _ = 857960073686 := by rw [factor_4_21]; decide
      have factor_4_23 : (3 : ZMod 930419060873) ^ 15287356 = 180907287752 := by
        calc
          (3 : ZMod 930419060873) ^ 15287356 = (3 : ZMod 930419060873) ^ (7643678 + 7643678) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 7643678 * (3 : ZMod 930419060873) ^ 7643678 := by rw [pow_add]
          _ = 180907287752 := by rw [factor_4_22]; decide
      have factor_4_24 : (3 : ZMod 930419060873) ^ 30574712 = 151700600933 := by
        calc
          (3 : ZMod 930419060873) ^ 30574712 = (3 : ZMod 930419060873) ^ (15287356 + 15287356) :=
            congrArg (fun n : ℕ => (3 : ZMod 930419060873) ^ n) (by norm_num)
          _ = (3 : ZMod 930419060873) ^ 15287356 * (3 : ZMod 930419060873) ^ 15287356 := by rw [pow_add]
          _ = 151700600933 := by rw [factor_4_23]; decide
      change (3 : ZMod 930419060873) ^ 30574712 ≠ 1
      rw [factor_4_24]
      decide

#print axioms prime_lucas_930419060873

end TotientTailPeriodKiller
end Erdos249257
