import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1780883040649 : Nat.Prime 1780883040649 := by
  apply lucas_primality 1780883040649 (7 : ZMod 1780883040649)
  ·
      have fermat_0 : (7 : ZMod 1780883040649) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 1780883040649) ^ 3 = 343 := by
        calc
          (7 : ZMod 1780883040649) ^ 3 = (7 : ZMod 1780883040649) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 1 * (7 : ZMod 1780883040649) ^ 1) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 1780883040649) ^ 6 = 117649 := by
        calc
          (7 : ZMod 1780883040649) ^ 6 = (7 : ZMod 1780883040649) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 3 * (7 : ZMod 1780883040649) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 1780883040649) ^ 12 = 13841287201 := by
        calc
          (7 : ZMod 1780883040649) ^ 12 = (7 : ZMod 1780883040649) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 6 * (7 : ZMod 1780883040649) ^ 6 := by rw [pow_add]
          _ = 13841287201 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 1780883040649) ^ 25 = 335085170620 := by
        calc
          (7 : ZMod 1780883040649) ^ 25 = (7 : ZMod 1780883040649) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 12 * (7 : ZMod 1780883040649) ^ 12) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 335085170620 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 1780883040649) ^ 51 = 432996853264 := by
        calc
          (7 : ZMod 1780883040649) ^ 51 = (7 : ZMod 1780883040649) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 25 * (7 : ZMod 1780883040649) ^ 25) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 432996853264 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 1780883040649) ^ 103 = 200439750871 := by
        calc
          (7 : ZMod 1780883040649) ^ 103 = (7 : ZMod 1780883040649) ^ (51 + 51 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 51 * (7 : ZMod 1780883040649) ^ 51) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 200439750871 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 1780883040649) ^ 207 = 628462299804 := by
        calc
          (7 : ZMod 1780883040649) ^ 207 = (7 : ZMod 1780883040649) ^ (103 + 103 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 103 * (7 : ZMod 1780883040649) ^ 103) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 628462299804 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 1780883040649) ^ 414 = 520787140661 := by
        calc
          (7 : ZMod 1780883040649) ^ 414 = (7 : ZMod 1780883040649) ^ (207 + 207) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 207 * (7 : ZMod 1780883040649) ^ 207 := by rw [pow_add]
          _ = 520787140661 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 1780883040649) ^ 829 = 160030943468 := by
        calc
          (7 : ZMod 1780883040649) ^ 829 = (7 : ZMod 1780883040649) ^ (414 + 414 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 414 * (7 : ZMod 1780883040649) ^ 414) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 160030943468 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 1780883040649) ^ 1658 = 858949478202 := by
        calc
          (7 : ZMod 1780883040649) ^ 1658 = (7 : ZMod 1780883040649) ^ (829 + 829) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 829 * (7 : ZMod 1780883040649) ^ 829 := by rw [pow_add]
          _ = 858949478202 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 1780883040649) ^ 3317 = 1021074333150 := by
        calc
          (7 : ZMod 1780883040649) ^ 3317 = (7 : ZMod 1780883040649) ^ (1658 + 1658 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 1658 * (7 : ZMod 1780883040649) ^ 1658) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 1021074333150 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 1780883040649) ^ 6634 = 634576497438 := by
        calc
          (7 : ZMod 1780883040649) ^ 6634 = (7 : ZMod 1780883040649) ^ (3317 + 3317) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 3317 * (7 : ZMod 1780883040649) ^ 3317 := by rw [pow_add]
          _ = 634576497438 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 1780883040649) ^ 13268 = 740377041668 := by
        calc
          (7 : ZMod 1780883040649) ^ 13268 = (7 : ZMod 1780883040649) ^ (6634 + 6634) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 6634 * (7 : ZMod 1780883040649) ^ 6634 := by rw [pow_add]
          _ = 740377041668 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 1780883040649) ^ 26537 = 816957486162 := by
        calc
          (7 : ZMod 1780883040649) ^ 26537 = (7 : ZMod 1780883040649) ^ (13268 + 13268 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 13268 * (7 : ZMod 1780883040649) ^ 13268) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 816957486162 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 1780883040649) ^ 53074 = 579211176650 := by
        calc
          (7 : ZMod 1780883040649) ^ 53074 = (7 : ZMod 1780883040649) ^ (26537 + 26537) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 26537 * (7 : ZMod 1780883040649) ^ 26537 := by rw [pow_add]
          _ = 579211176650 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 1780883040649) ^ 106148 = 661909628041 := by
        calc
          (7 : ZMod 1780883040649) ^ 106148 = (7 : ZMod 1780883040649) ^ (53074 + 53074) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 53074 * (7 : ZMod 1780883040649) ^ 53074 := by rw [pow_add]
          _ = 661909628041 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 1780883040649) ^ 212297 = 1727481514860 := by
        calc
          (7 : ZMod 1780883040649) ^ 212297 = (7 : ZMod 1780883040649) ^ (106148 + 106148 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 106148 * (7 : ZMod 1780883040649) ^ 106148) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 1727481514860 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 1780883040649) ^ 424595 = 264351506522 := by
        calc
          (7 : ZMod 1780883040649) ^ 424595 = (7 : ZMod 1780883040649) ^ (212297 + 212297 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 212297 * (7 : ZMod 1780883040649) ^ 212297) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 264351506522 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 1780883040649) ^ 849191 = 245240686852 := by
        calc
          (7 : ZMod 1780883040649) ^ 849191 = (7 : ZMod 1780883040649) ^ (424595 + 424595 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 424595 * (7 : ZMod 1780883040649) ^ 424595) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 245240686852 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 1780883040649) ^ 1698382 = 819643963119 := by
        calc
          (7 : ZMod 1780883040649) ^ 1698382 = (7 : ZMod 1780883040649) ^ (849191 + 849191) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 849191 * (7 : ZMod 1780883040649) ^ 849191 := by rw [pow_add]
          _ = 819643963119 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 1780883040649) ^ 3396764 = 695564391037 := by
        calc
          (7 : ZMod 1780883040649) ^ 3396764 = (7 : ZMod 1780883040649) ^ (1698382 + 1698382) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 1698382 * (7 : ZMod 1780883040649) ^ 1698382 := by rw [pow_add]
          _ = 695564391037 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 1780883040649) ^ 6793529 = 968137547339 := by
        calc
          (7 : ZMod 1780883040649) ^ 6793529 = (7 : ZMod 1780883040649) ^ (3396764 + 3396764 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 3396764 * (7 : ZMod 1780883040649) ^ 3396764) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 968137547339 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 1780883040649) ^ 13587059 = 1006125793790 := by
        calc
          (7 : ZMod 1780883040649) ^ 13587059 = (7 : ZMod 1780883040649) ^ (6793529 + 6793529 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 6793529 * (7 : ZMod 1780883040649) ^ 6793529) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 1006125793790 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 1780883040649) ^ 27174118 = 84802098334 := by
        calc
          (7 : ZMod 1780883040649) ^ 27174118 = (7 : ZMod 1780883040649) ^ (13587059 + 13587059) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 13587059 * (7 : ZMod 1780883040649) ^ 13587059 := by rw [pow_add]
          _ = 84802098334 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 1780883040649) ^ 54348237 = 109364756 := by
        calc
          (7 : ZMod 1780883040649) ^ 54348237 = (7 : ZMod 1780883040649) ^ (27174118 + 27174118 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 27174118 * (7 : ZMod 1780883040649) ^ 27174118) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 109364756 := by rw [fermat_24]; decide
      have fermat_26 : (7 : ZMod 1780883040649) ^ 108696474 = 239353940852 := by
        calc
          (7 : ZMod 1780883040649) ^ 108696474 = (7 : ZMod 1780883040649) ^ (54348237 + 54348237) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 54348237 * (7 : ZMod 1780883040649) ^ 54348237 := by rw [pow_add]
          _ = 239353940852 := by rw [fermat_25]; decide
      have fermat_27 : (7 : ZMod 1780883040649) ^ 217392949 = 1671541849108 := by
        calc
          (7 : ZMod 1780883040649) ^ 217392949 = (7 : ZMod 1780883040649) ^ (108696474 + 108696474 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 108696474 * (7 : ZMod 1780883040649) ^ 108696474) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 1671541849108 := by rw [fermat_26]; decide
      have fermat_28 : (7 : ZMod 1780883040649) ^ 434785898 = 891455585638 := by
        calc
          (7 : ZMod 1780883040649) ^ 434785898 = (7 : ZMod 1780883040649) ^ (217392949 + 217392949) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 217392949 * (7 : ZMod 1780883040649) ^ 217392949 := by rw [pow_add]
          _ = 891455585638 := by rw [fermat_27]; decide
      have fermat_29 : (7 : ZMod 1780883040649) ^ 869571797 = 690236166171 := by
        calc
          (7 : ZMod 1780883040649) ^ 869571797 = (7 : ZMod 1780883040649) ^ (434785898 + 434785898 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 434785898 * (7 : ZMod 1780883040649) ^ 434785898) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 690236166171 := by rw [fermat_28]; decide
      have fermat_30 : (7 : ZMod 1780883040649) ^ 1739143594 = 1392551204442 := by
        calc
          (7 : ZMod 1780883040649) ^ 1739143594 = (7 : ZMod 1780883040649) ^ (869571797 + 869571797) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 869571797 * (7 : ZMod 1780883040649) ^ 869571797 := by rw [pow_add]
          _ = 1392551204442 := by rw [fermat_29]; decide
      have fermat_31 : (7 : ZMod 1780883040649) ^ 3478287188 = 40084700402 := by
        calc
          (7 : ZMod 1780883040649) ^ 3478287188 = (7 : ZMod 1780883040649) ^ (1739143594 + 1739143594) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 1739143594 * (7 : ZMod 1780883040649) ^ 1739143594 := by rw [pow_add]
          _ = 40084700402 := by rw [fermat_30]; decide
      have fermat_32 : (7 : ZMod 1780883040649) ^ 6956574377 = 39001578044 := by
        calc
          (7 : ZMod 1780883040649) ^ 6956574377 = (7 : ZMod 1780883040649) ^ (3478287188 + 3478287188 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 3478287188 * (7 : ZMod 1780883040649) ^ 3478287188) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 39001578044 := by rw [fermat_31]; decide
      have fermat_33 : (7 : ZMod 1780883040649) ^ 13913148755 = 1132832055874 := by
        calc
          (7 : ZMod 1780883040649) ^ 13913148755 = (7 : ZMod 1780883040649) ^ (6956574377 + 6956574377 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 6956574377 * (7 : ZMod 1780883040649) ^ 6956574377) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 1132832055874 := by rw [fermat_32]; decide
      have fermat_34 : (7 : ZMod 1780883040649) ^ 27826297510 = 1139427326002 := by
        calc
          (7 : ZMod 1780883040649) ^ 27826297510 = (7 : ZMod 1780883040649) ^ (13913148755 + 13913148755) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 13913148755 * (7 : ZMod 1780883040649) ^ 13913148755 := by rw [pow_add]
          _ = 1139427326002 := by rw [fermat_33]; decide
      have fermat_35 : (7 : ZMod 1780883040649) ^ 55652595020 = 1113747947818 := by
        calc
          (7 : ZMod 1780883040649) ^ 55652595020 = (7 : ZMod 1780883040649) ^ (27826297510 + 27826297510) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 27826297510 * (7 : ZMod 1780883040649) ^ 27826297510 := by rw [pow_add]
          _ = 1113747947818 := by rw [fermat_34]; decide
      have fermat_36 : (7 : ZMod 1780883040649) ^ 111305190040 = 1645654278588 := by
        calc
          (7 : ZMod 1780883040649) ^ 111305190040 = (7 : ZMod 1780883040649) ^ (55652595020 + 55652595020) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 55652595020 * (7 : ZMod 1780883040649) ^ 55652595020 := by rw [pow_add]
          _ = 1645654278588 := by rw [fermat_35]; decide
      have fermat_37 : (7 : ZMod 1780883040649) ^ 222610380081 = 1395820477284 := by
        calc
          (7 : ZMod 1780883040649) ^ 222610380081 = (7 : ZMod 1780883040649) ^ (111305190040 + 111305190040 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 111305190040 * (7 : ZMod 1780883040649) ^ 111305190040) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 1395820477284 := by rw [fermat_36]; decide
      have fermat_38 : (7 : ZMod 1780883040649) ^ 445220760162 = 211914452963 := by
        calc
          (7 : ZMod 1780883040649) ^ 445220760162 = (7 : ZMod 1780883040649) ^ (222610380081 + 222610380081) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 222610380081 * (7 : ZMod 1780883040649) ^ 222610380081 := by rw [pow_add]
          _ = 211914452963 := by rw [fermat_37]; decide
      have fermat_39 : (7 : ZMod 1780883040649) ^ 890441520324 = 1780883040648 := by
        calc
          (7 : ZMod 1780883040649) ^ 890441520324 = (7 : ZMod 1780883040649) ^ (445220760162 + 445220760162) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 445220760162 * (7 : ZMod 1780883040649) ^ 445220760162 := by rw [pow_add]
          _ = 1780883040648 := by rw [fermat_38]; decide
      have fermat_40 : (7 : ZMod 1780883040649) ^ 1780883040648 = 1 := by
        calc
          (7 : ZMod 1780883040649) ^ 1780883040648 = (7 : ZMod 1780883040649) ^ (890441520324 + 890441520324) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 890441520324 * (7 : ZMod 1780883040649) ^ 890441520324 := by rw [pow_add]
          _ = 1 := by rw [fermat_39]; decide
      simpa using fermat_40
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (21937, 1), (3382571, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (21937, 1), (3382571, 1)] : List FactorBlock).map factorBlockValue).prod = 1780883040649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 1780883040649) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 1780883040649) ^ 3 = 343 := by
        calc
          (7 : ZMod 1780883040649) ^ 3 = (7 : ZMod 1780883040649) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 1 * (7 : ZMod 1780883040649) ^ 1) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 1780883040649) ^ 6 = 117649 := by
        calc
          (7 : ZMod 1780883040649) ^ 6 = (7 : ZMod 1780883040649) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 3 * (7 : ZMod 1780883040649) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 1780883040649) ^ 12 = 13841287201 := by
        calc
          (7 : ZMod 1780883040649) ^ 12 = (7 : ZMod 1780883040649) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 6 * (7 : ZMod 1780883040649) ^ 6 := by rw [pow_add]
          _ = 13841287201 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 1780883040649) ^ 25 = 335085170620 := by
        calc
          (7 : ZMod 1780883040649) ^ 25 = (7 : ZMod 1780883040649) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 12 * (7 : ZMod 1780883040649) ^ 12) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 335085170620 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 1780883040649) ^ 51 = 432996853264 := by
        calc
          (7 : ZMod 1780883040649) ^ 51 = (7 : ZMod 1780883040649) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 25 * (7 : ZMod 1780883040649) ^ 25) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 432996853264 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 1780883040649) ^ 103 = 200439750871 := by
        calc
          (7 : ZMod 1780883040649) ^ 103 = (7 : ZMod 1780883040649) ^ (51 + 51 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 51 * (7 : ZMod 1780883040649) ^ 51) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 200439750871 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 1780883040649) ^ 207 = 628462299804 := by
        calc
          (7 : ZMod 1780883040649) ^ 207 = (7 : ZMod 1780883040649) ^ (103 + 103 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 103 * (7 : ZMod 1780883040649) ^ 103) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 628462299804 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 1780883040649) ^ 414 = 520787140661 := by
        calc
          (7 : ZMod 1780883040649) ^ 414 = (7 : ZMod 1780883040649) ^ (207 + 207) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 207 * (7 : ZMod 1780883040649) ^ 207 := by rw [pow_add]
          _ = 520787140661 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 1780883040649) ^ 829 = 160030943468 := by
        calc
          (7 : ZMod 1780883040649) ^ 829 = (7 : ZMod 1780883040649) ^ (414 + 414 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 414 * (7 : ZMod 1780883040649) ^ 414) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 160030943468 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 1780883040649) ^ 1658 = 858949478202 := by
        calc
          (7 : ZMod 1780883040649) ^ 1658 = (7 : ZMod 1780883040649) ^ (829 + 829) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 829 * (7 : ZMod 1780883040649) ^ 829 := by rw [pow_add]
          _ = 858949478202 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 1780883040649) ^ 3317 = 1021074333150 := by
        calc
          (7 : ZMod 1780883040649) ^ 3317 = (7 : ZMod 1780883040649) ^ (1658 + 1658 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 1658 * (7 : ZMod 1780883040649) ^ 1658) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 1021074333150 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 1780883040649) ^ 6634 = 634576497438 := by
        calc
          (7 : ZMod 1780883040649) ^ 6634 = (7 : ZMod 1780883040649) ^ (3317 + 3317) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 3317 * (7 : ZMod 1780883040649) ^ 3317 := by rw [pow_add]
          _ = 634576497438 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 1780883040649) ^ 13268 = 740377041668 := by
        calc
          (7 : ZMod 1780883040649) ^ 13268 = (7 : ZMod 1780883040649) ^ (6634 + 6634) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 6634 * (7 : ZMod 1780883040649) ^ 6634 := by rw [pow_add]
          _ = 740377041668 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 1780883040649) ^ 26537 = 816957486162 := by
        calc
          (7 : ZMod 1780883040649) ^ 26537 = (7 : ZMod 1780883040649) ^ (13268 + 13268 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 13268 * (7 : ZMod 1780883040649) ^ 13268) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 816957486162 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 1780883040649) ^ 53074 = 579211176650 := by
        calc
          (7 : ZMod 1780883040649) ^ 53074 = (7 : ZMod 1780883040649) ^ (26537 + 26537) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 26537 * (7 : ZMod 1780883040649) ^ 26537 := by rw [pow_add]
          _ = 579211176650 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 1780883040649) ^ 106148 = 661909628041 := by
        calc
          (7 : ZMod 1780883040649) ^ 106148 = (7 : ZMod 1780883040649) ^ (53074 + 53074) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 53074 * (7 : ZMod 1780883040649) ^ 53074 := by rw [pow_add]
          _ = 661909628041 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 1780883040649) ^ 212297 = 1727481514860 := by
        calc
          (7 : ZMod 1780883040649) ^ 212297 = (7 : ZMod 1780883040649) ^ (106148 + 106148 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 106148 * (7 : ZMod 1780883040649) ^ 106148) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 1727481514860 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 1780883040649) ^ 424595 = 264351506522 := by
        calc
          (7 : ZMod 1780883040649) ^ 424595 = (7 : ZMod 1780883040649) ^ (212297 + 212297 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 212297 * (7 : ZMod 1780883040649) ^ 212297) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 264351506522 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 1780883040649) ^ 849191 = 245240686852 := by
        calc
          (7 : ZMod 1780883040649) ^ 849191 = (7 : ZMod 1780883040649) ^ (424595 + 424595 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 424595 * (7 : ZMod 1780883040649) ^ 424595) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 245240686852 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 1780883040649) ^ 1698382 = 819643963119 := by
        calc
          (7 : ZMod 1780883040649) ^ 1698382 = (7 : ZMod 1780883040649) ^ (849191 + 849191) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 849191 * (7 : ZMod 1780883040649) ^ 849191 := by rw [pow_add]
          _ = 819643963119 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 1780883040649) ^ 3396764 = 695564391037 := by
        calc
          (7 : ZMod 1780883040649) ^ 3396764 = (7 : ZMod 1780883040649) ^ (1698382 + 1698382) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 1698382 * (7 : ZMod 1780883040649) ^ 1698382 := by rw [pow_add]
          _ = 695564391037 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 1780883040649) ^ 6793529 = 968137547339 := by
        calc
          (7 : ZMod 1780883040649) ^ 6793529 = (7 : ZMod 1780883040649) ^ (3396764 + 3396764 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 3396764 * (7 : ZMod 1780883040649) ^ 3396764) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 968137547339 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 1780883040649) ^ 13587059 = 1006125793790 := by
        calc
          (7 : ZMod 1780883040649) ^ 13587059 = (7 : ZMod 1780883040649) ^ (6793529 + 6793529 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 6793529 * (7 : ZMod 1780883040649) ^ 6793529) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 1006125793790 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 1780883040649) ^ 27174118 = 84802098334 := by
        calc
          (7 : ZMod 1780883040649) ^ 27174118 = (7 : ZMod 1780883040649) ^ (13587059 + 13587059) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 13587059 * (7 : ZMod 1780883040649) ^ 13587059 := by rw [pow_add]
          _ = 84802098334 := by rw [factor_0_23]; decide
      have factor_0_25 : (7 : ZMod 1780883040649) ^ 54348237 = 109364756 := by
        calc
          (7 : ZMod 1780883040649) ^ 54348237 = (7 : ZMod 1780883040649) ^ (27174118 + 27174118 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 27174118 * (7 : ZMod 1780883040649) ^ 27174118) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 109364756 := by rw [factor_0_24]; decide
      have factor_0_26 : (7 : ZMod 1780883040649) ^ 108696474 = 239353940852 := by
        calc
          (7 : ZMod 1780883040649) ^ 108696474 = (7 : ZMod 1780883040649) ^ (54348237 + 54348237) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 54348237 * (7 : ZMod 1780883040649) ^ 54348237 := by rw [pow_add]
          _ = 239353940852 := by rw [factor_0_25]; decide
      have factor_0_27 : (7 : ZMod 1780883040649) ^ 217392949 = 1671541849108 := by
        calc
          (7 : ZMod 1780883040649) ^ 217392949 = (7 : ZMod 1780883040649) ^ (108696474 + 108696474 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 108696474 * (7 : ZMod 1780883040649) ^ 108696474) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 1671541849108 := by rw [factor_0_26]; decide
      have factor_0_28 : (7 : ZMod 1780883040649) ^ 434785898 = 891455585638 := by
        calc
          (7 : ZMod 1780883040649) ^ 434785898 = (7 : ZMod 1780883040649) ^ (217392949 + 217392949) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 217392949 * (7 : ZMod 1780883040649) ^ 217392949 := by rw [pow_add]
          _ = 891455585638 := by rw [factor_0_27]; decide
      have factor_0_29 : (7 : ZMod 1780883040649) ^ 869571797 = 690236166171 := by
        calc
          (7 : ZMod 1780883040649) ^ 869571797 = (7 : ZMod 1780883040649) ^ (434785898 + 434785898 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 434785898 * (7 : ZMod 1780883040649) ^ 434785898) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 690236166171 := by rw [factor_0_28]; decide
      have factor_0_30 : (7 : ZMod 1780883040649) ^ 1739143594 = 1392551204442 := by
        calc
          (7 : ZMod 1780883040649) ^ 1739143594 = (7 : ZMod 1780883040649) ^ (869571797 + 869571797) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 869571797 * (7 : ZMod 1780883040649) ^ 869571797 := by rw [pow_add]
          _ = 1392551204442 := by rw [factor_0_29]; decide
      have factor_0_31 : (7 : ZMod 1780883040649) ^ 3478287188 = 40084700402 := by
        calc
          (7 : ZMod 1780883040649) ^ 3478287188 = (7 : ZMod 1780883040649) ^ (1739143594 + 1739143594) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 1739143594 * (7 : ZMod 1780883040649) ^ 1739143594 := by rw [pow_add]
          _ = 40084700402 := by rw [factor_0_30]; decide
      have factor_0_32 : (7 : ZMod 1780883040649) ^ 6956574377 = 39001578044 := by
        calc
          (7 : ZMod 1780883040649) ^ 6956574377 = (7 : ZMod 1780883040649) ^ (3478287188 + 3478287188 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 3478287188 * (7 : ZMod 1780883040649) ^ 3478287188) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 39001578044 := by rw [factor_0_31]; decide
      have factor_0_33 : (7 : ZMod 1780883040649) ^ 13913148755 = 1132832055874 := by
        calc
          (7 : ZMod 1780883040649) ^ 13913148755 = (7 : ZMod 1780883040649) ^ (6956574377 + 6956574377 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 6956574377 * (7 : ZMod 1780883040649) ^ 6956574377) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 1132832055874 := by rw [factor_0_32]; decide
      have factor_0_34 : (7 : ZMod 1780883040649) ^ 27826297510 = 1139427326002 := by
        calc
          (7 : ZMod 1780883040649) ^ 27826297510 = (7 : ZMod 1780883040649) ^ (13913148755 + 13913148755) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 13913148755 * (7 : ZMod 1780883040649) ^ 13913148755 := by rw [pow_add]
          _ = 1139427326002 := by rw [factor_0_33]; decide
      have factor_0_35 : (7 : ZMod 1780883040649) ^ 55652595020 = 1113747947818 := by
        calc
          (7 : ZMod 1780883040649) ^ 55652595020 = (7 : ZMod 1780883040649) ^ (27826297510 + 27826297510) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 27826297510 * (7 : ZMod 1780883040649) ^ 27826297510 := by rw [pow_add]
          _ = 1113747947818 := by rw [factor_0_34]; decide
      have factor_0_36 : (7 : ZMod 1780883040649) ^ 111305190040 = 1645654278588 := by
        calc
          (7 : ZMod 1780883040649) ^ 111305190040 = (7 : ZMod 1780883040649) ^ (55652595020 + 55652595020) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 55652595020 * (7 : ZMod 1780883040649) ^ 55652595020 := by rw [pow_add]
          _ = 1645654278588 := by rw [factor_0_35]; decide
      have factor_0_37 : (7 : ZMod 1780883040649) ^ 222610380081 = 1395820477284 := by
        calc
          (7 : ZMod 1780883040649) ^ 222610380081 = (7 : ZMod 1780883040649) ^ (111305190040 + 111305190040 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 111305190040 * (7 : ZMod 1780883040649) ^ 111305190040) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 1395820477284 := by rw [factor_0_36]; decide
      have factor_0_38 : (7 : ZMod 1780883040649) ^ 445220760162 = 211914452963 := by
        calc
          (7 : ZMod 1780883040649) ^ 445220760162 = (7 : ZMod 1780883040649) ^ (222610380081 + 222610380081) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 222610380081 * (7 : ZMod 1780883040649) ^ 222610380081 := by rw [pow_add]
          _ = 211914452963 := by rw [factor_0_37]; decide
      have factor_0_39 : (7 : ZMod 1780883040649) ^ 890441520324 = 1780883040648 := by
        calc
          (7 : ZMod 1780883040649) ^ 890441520324 = (7 : ZMod 1780883040649) ^ (445220760162 + 445220760162) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 445220760162 * (7 : ZMod 1780883040649) ^ 445220760162 := by rw [pow_add]
          _ = 1780883040648 := by rw [factor_0_38]; decide
      change (7 : ZMod 1780883040649) ^ 890441520324 ≠ 1
      rw [factor_0_39]
      decide
    ·
      have factor_1_0 : (7 : ZMod 1780883040649) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 1780883040649) ^ 2 = 49 := by
        calc
          (7 : ZMod 1780883040649) ^ 2 = (7 : ZMod 1780883040649) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 1 * (7 : ZMod 1780883040649) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 1780883040649) ^ 4 = 2401 := by
        calc
          (7 : ZMod 1780883040649) ^ 4 = (7 : ZMod 1780883040649) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 2 * (7 : ZMod 1780883040649) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 1780883040649) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 1780883040649) ^ 8 = (7 : ZMod 1780883040649) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 4 * (7 : ZMod 1780883040649) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 1780883040649) ^ 17 = 1115718702837 := by
        calc
          (7 : ZMod 1780883040649) ^ 17 = (7 : ZMod 1780883040649) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 8 * (7 : ZMod 1780883040649) ^ 8) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 1115718702837 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 1780883040649) ^ 34 = 1193038577193 := by
        calc
          (7 : ZMod 1780883040649) ^ 34 = (7 : ZMod 1780883040649) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 17 * (7 : ZMod 1780883040649) ^ 17 := by rw [pow_add]
          _ = 1193038577193 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 1780883040649) ^ 69 = 778302672316 := by
        calc
          (7 : ZMod 1780883040649) ^ 69 = (7 : ZMod 1780883040649) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 34 * (7 : ZMod 1780883040649) ^ 34) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 778302672316 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 1780883040649) ^ 138 = 56575271631 := by
        calc
          (7 : ZMod 1780883040649) ^ 138 = (7 : ZMod 1780883040649) ^ (69 + 69) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 69 * (7 : ZMod 1780883040649) ^ 69 := by rw [pow_add]
          _ = 56575271631 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 1780883040649) ^ 276 = 1566193050432 := by
        calc
          (7 : ZMod 1780883040649) ^ 276 = (7 : ZMod 1780883040649) ^ (138 + 138) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 138 * (7 : ZMod 1780883040649) ^ 138 := by rw [pow_add]
          _ = 1566193050432 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 1780883040649) ^ 552 = 106399939828 := by
        calc
          (7 : ZMod 1780883040649) ^ 552 = (7 : ZMod 1780883040649) ^ (276 + 276) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 276 * (7 : ZMod 1780883040649) ^ 276 := by rw [pow_add]
          _ = 106399939828 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 1780883040649) ^ 1105 = 809800501072 := by
        calc
          (7 : ZMod 1780883040649) ^ 1105 = (7 : ZMod 1780883040649) ^ (552 + 552 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 552 * (7 : ZMod 1780883040649) ^ 552) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 809800501072 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 1780883040649) ^ 2211 = 1615034587739 := by
        calc
          (7 : ZMod 1780883040649) ^ 2211 = (7 : ZMod 1780883040649) ^ (1105 + 1105 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 1105 * (7 : ZMod 1780883040649) ^ 1105) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 1615034587739 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 1780883040649) ^ 4422 = 1230911680786 := by
        calc
          (7 : ZMod 1780883040649) ^ 4422 = (7 : ZMod 1780883040649) ^ (2211 + 2211) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 2211 * (7 : ZMod 1780883040649) ^ 2211 := by rw [pow_add]
          _ = 1230911680786 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 1780883040649) ^ 8845 = 588859084799 := by
        calc
          (7 : ZMod 1780883040649) ^ 8845 = (7 : ZMod 1780883040649) ^ (4422 + 4422 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 4422 * (7 : ZMod 1780883040649) ^ 4422) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 588859084799 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 1780883040649) ^ 17691 = 372160285782 := by
        calc
          (7 : ZMod 1780883040649) ^ 17691 = (7 : ZMod 1780883040649) ^ (8845 + 8845 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 8845 * (7 : ZMod 1780883040649) ^ 8845) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 372160285782 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 1780883040649) ^ 35382 = 1347369782282 := by
        calc
          (7 : ZMod 1780883040649) ^ 35382 = (7 : ZMod 1780883040649) ^ (17691 + 17691) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 17691 * (7 : ZMod 1780883040649) ^ 17691 := by rw [pow_add]
          _ = 1347369782282 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 1780883040649) ^ 70765 = 562543891318 := by
        calc
          (7 : ZMod 1780883040649) ^ 70765 = (7 : ZMod 1780883040649) ^ (35382 + 35382 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 35382 * (7 : ZMod 1780883040649) ^ 35382) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 562543891318 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 1780883040649) ^ 141531 = 1588786107105 := by
        calc
          (7 : ZMod 1780883040649) ^ 141531 = (7 : ZMod 1780883040649) ^ (70765 + 70765 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 70765 * (7 : ZMod 1780883040649) ^ 70765) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 1588786107105 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 1780883040649) ^ 283063 = 1427053498628 := by
        calc
          (7 : ZMod 1780883040649) ^ 283063 = (7 : ZMod 1780883040649) ^ (141531 + 141531 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 141531 * (7 : ZMod 1780883040649) ^ 141531) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 1427053498628 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 1780883040649) ^ 566127 = 527887575425 := by
        calc
          (7 : ZMod 1780883040649) ^ 566127 = (7 : ZMod 1780883040649) ^ (283063 + 283063 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 283063 * (7 : ZMod 1780883040649) ^ 283063) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 527887575425 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 1780883040649) ^ 1132254 = 407786306445 := by
        calc
          (7 : ZMod 1780883040649) ^ 1132254 = (7 : ZMod 1780883040649) ^ (566127 + 566127) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 566127 * (7 : ZMod 1780883040649) ^ 566127 := by rw [pow_add]
          _ = 407786306445 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 1780883040649) ^ 2264509 = 1024799124763 := by
        calc
          (7 : ZMod 1780883040649) ^ 2264509 = (7 : ZMod 1780883040649) ^ (1132254 + 1132254 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 1132254 * (7 : ZMod 1780883040649) ^ 1132254) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 1024799124763 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 1780883040649) ^ 4529019 = 678049989387 := by
        calc
          (7 : ZMod 1780883040649) ^ 4529019 = (7 : ZMod 1780883040649) ^ (2264509 + 2264509 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 2264509 * (7 : ZMod 1780883040649) ^ 2264509) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 678049989387 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 1780883040649) ^ 9058039 = 966683419384 := by
        calc
          (7 : ZMod 1780883040649) ^ 9058039 = (7 : ZMod 1780883040649) ^ (4529019 + 4529019 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 4529019 * (7 : ZMod 1780883040649) ^ 4529019) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 966683419384 := by rw [factor_1_22]; decide
      have factor_1_24 : (7 : ZMod 1780883040649) ^ 18116079 = 388571822275 := by
        calc
          (7 : ZMod 1780883040649) ^ 18116079 = (7 : ZMod 1780883040649) ^ (9058039 + 9058039 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 9058039 * (7 : ZMod 1780883040649) ^ 9058039) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 388571822275 := by rw [factor_1_23]; decide
      have factor_1_25 : (7 : ZMod 1780883040649) ^ 36232158 = 186656468165 := by
        calc
          (7 : ZMod 1780883040649) ^ 36232158 = (7 : ZMod 1780883040649) ^ (18116079 + 18116079) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 18116079 * (7 : ZMod 1780883040649) ^ 18116079 := by rw [pow_add]
          _ = 186656468165 := by rw [factor_1_24]; decide
      have factor_1_26 : (7 : ZMod 1780883040649) ^ 72464316 = 983017912154 := by
        calc
          (7 : ZMod 1780883040649) ^ 72464316 = (7 : ZMod 1780883040649) ^ (36232158 + 36232158) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 36232158 * (7 : ZMod 1780883040649) ^ 36232158 := by rw [pow_add]
          _ = 983017912154 := by rw [factor_1_25]; decide
      have factor_1_27 : (7 : ZMod 1780883040649) ^ 144928632 = 1133270781355 := by
        calc
          (7 : ZMod 1780883040649) ^ 144928632 = (7 : ZMod 1780883040649) ^ (72464316 + 72464316) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 72464316 * (7 : ZMod 1780883040649) ^ 72464316 := by rw [pow_add]
          _ = 1133270781355 := by rw [factor_1_26]; decide
      have factor_1_28 : (7 : ZMod 1780883040649) ^ 289857265 = 1554239811435 := by
        calc
          (7 : ZMod 1780883040649) ^ 289857265 = (7 : ZMod 1780883040649) ^ (144928632 + 144928632 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 144928632 * (7 : ZMod 1780883040649) ^ 144928632) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 1554239811435 := by rw [factor_1_27]; decide
      have factor_1_29 : (7 : ZMod 1780883040649) ^ 579714531 = 863478093909 := by
        calc
          (7 : ZMod 1780883040649) ^ 579714531 = (7 : ZMod 1780883040649) ^ (289857265 + 289857265 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 289857265 * (7 : ZMod 1780883040649) ^ 289857265) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 863478093909 := by rw [factor_1_28]; decide
      have factor_1_30 : (7 : ZMod 1780883040649) ^ 1159429062 = 1423946023281 := by
        calc
          (7 : ZMod 1780883040649) ^ 1159429062 = (7 : ZMod 1780883040649) ^ (579714531 + 579714531) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 579714531 * (7 : ZMod 1780883040649) ^ 579714531 := by rw [pow_add]
          _ = 1423946023281 := by rw [factor_1_29]; decide
      have factor_1_31 : (7 : ZMod 1780883040649) ^ 2318858125 = 1320653563796 := by
        calc
          (7 : ZMod 1780883040649) ^ 2318858125 = (7 : ZMod 1780883040649) ^ (1159429062 + 1159429062 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 1159429062 * (7 : ZMod 1780883040649) ^ 1159429062) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 1320653563796 := by rw [factor_1_30]; decide
      have factor_1_32 : (7 : ZMod 1780883040649) ^ 4637716251 = 1772084614598 := by
        calc
          (7 : ZMod 1780883040649) ^ 4637716251 = (7 : ZMod 1780883040649) ^ (2318858125 + 2318858125 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 2318858125 * (7 : ZMod 1780883040649) ^ 2318858125) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 1772084614598 := by rw [factor_1_31]; decide
      have factor_1_33 : (7 : ZMod 1780883040649) ^ 9275432503 = 44051941104 := by
        calc
          (7 : ZMod 1780883040649) ^ 9275432503 = (7 : ZMod 1780883040649) ^ (4637716251 + 4637716251 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 4637716251 * (7 : ZMod 1780883040649) ^ 4637716251) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 44051941104 := by rw [factor_1_32]; decide
      have factor_1_34 : (7 : ZMod 1780883040649) ^ 18550865006 = 1075323785831 := by
        calc
          (7 : ZMod 1780883040649) ^ 18550865006 = (7 : ZMod 1780883040649) ^ (9275432503 + 9275432503) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 9275432503 * (7 : ZMod 1780883040649) ^ 9275432503 := by rw [pow_add]
          _ = 1075323785831 := by rw [factor_1_33]; decide
      have factor_1_35 : (7 : ZMod 1780883040649) ^ 37101730013 = 454360300645 := by
        calc
          (7 : ZMod 1780883040649) ^ 37101730013 = (7 : ZMod 1780883040649) ^ (18550865006 + 18550865006 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 18550865006 * (7 : ZMod 1780883040649) ^ 18550865006) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 454360300645 := by rw [factor_1_34]; decide
      have factor_1_36 : (7 : ZMod 1780883040649) ^ 74203460027 = 43769750351 := by
        calc
          (7 : ZMod 1780883040649) ^ 74203460027 = (7 : ZMod 1780883040649) ^ (37101730013 + 37101730013 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 37101730013 * (7 : ZMod 1780883040649) ^ 37101730013) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 43769750351 := by rw [factor_1_35]; decide
      have factor_1_37 : (7 : ZMod 1780883040649) ^ 148406920054 = 1039224325184 := by
        calc
          (7 : ZMod 1780883040649) ^ 148406920054 = (7 : ZMod 1780883040649) ^ (74203460027 + 74203460027) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 74203460027 * (7 : ZMod 1780883040649) ^ 74203460027 := by rw [pow_add]
          _ = 1039224325184 := by rw [factor_1_36]; decide
      have factor_1_38 : (7 : ZMod 1780883040649) ^ 296813840108 = 1534476793069 := by
        calc
          (7 : ZMod 1780883040649) ^ 296813840108 = (7 : ZMod 1780883040649) ^ (148406920054 + 148406920054) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 148406920054 * (7 : ZMod 1780883040649) ^ 148406920054 := by rw [pow_add]
          _ = 1534476793069 := by rw [factor_1_37]; decide
      have factor_1_39 : (7 : ZMod 1780883040649) ^ 593627680216 = 1534476793068 := by
        calc
          (7 : ZMod 1780883040649) ^ 593627680216 = (7 : ZMod 1780883040649) ^ (296813840108 + 296813840108) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 296813840108 * (7 : ZMod 1780883040649) ^ 296813840108 := by rw [pow_add]
          _ = 1534476793068 := by rw [factor_1_38]; decide
      change (7 : ZMod 1780883040649) ^ 593627680216 ≠ 1
      rw [factor_1_39]
      decide
    ·
      have factor_2_0 : (7 : ZMod 1780883040649) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 1780883040649) ^ 2 = 49 := by
        calc
          (7 : ZMod 1780883040649) ^ 2 = (7 : ZMod 1780883040649) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 1 * (7 : ZMod 1780883040649) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 1780883040649) ^ 4 = 2401 := by
        calc
          (7 : ZMod 1780883040649) ^ 4 = (7 : ZMod 1780883040649) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 2 * (7 : ZMod 1780883040649) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 1780883040649) ^ 9 = 40353607 := by
        calc
          (7 : ZMod 1780883040649) ^ 9 = (7 : ZMod 1780883040649) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 4 * (7 : ZMod 1780883040649) ^ 4) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 40353607 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 1780883040649) ^ 19 = 1243725219543 := by
        calc
          (7 : ZMod 1780883040649) ^ 19 = (7 : ZMod 1780883040649) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 9 * (7 : ZMod 1780883040649) ^ 9) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 1243725219543 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 1780883040649) ^ 38 = 825694476801 := by
        calc
          (7 : ZMod 1780883040649) ^ 38 = (7 : ZMod 1780883040649) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 19 * (7 : ZMod 1780883040649) ^ 19 := by rw [pow_add]
          _ = 825694476801 := by rw [factor_2_4]; decide
      have factor_2_6 : (7 : ZMod 1780883040649) ^ 77 = 1510175817867 := by
        calc
          (7 : ZMod 1780883040649) ^ 77 = (7 : ZMod 1780883040649) ^ (38 + 38 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 38 * (7 : ZMod 1780883040649) ^ 38) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 1510175817867 := by rw [factor_2_5]; decide
      have factor_2_7 : (7 : ZMod 1780883040649) ^ 154 = 853142201723 := by
        calc
          (7 : ZMod 1780883040649) ^ 154 = (7 : ZMod 1780883040649) ^ (77 + 77) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 77 * (7 : ZMod 1780883040649) ^ 77 := by rw [pow_add]
          _ = 853142201723 := by rw [factor_2_6]; decide
      have factor_2_8 : (7 : ZMod 1780883040649) ^ 309 = 462899668900 := by
        calc
          (7 : ZMod 1780883040649) ^ 309 = (7 : ZMod 1780883040649) ^ (154 + 154 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 154 * (7 : ZMod 1780883040649) ^ 154) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 462899668900 := by rw [factor_2_7]; decide
      have factor_2_9 : (7 : ZMod 1780883040649) ^ 619 = 1042761056108 := by
        calc
          (7 : ZMod 1780883040649) ^ 619 = (7 : ZMod 1780883040649) ^ (309 + 309 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 309 * (7 : ZMod 1780883040649) ^ 309) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 1042761056108 := by rw [factor_2_8]; decide
      have factor_2_10 : (7 : ZMod 1780883040649) ^ 1238 = 688071434220 := by
        calc
          (7 : ZMod 1780883040649) ^ 1238 = (7 : ZMod 1780883040649) ^ (619 + 619) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 619 * (7 : ZMod 1780883040649) ^ 619 := by rw [pow_add]
          _ = 688071434220 := by rw [factor_2_9]; decide
      have factor_2_11 : (7 : ZMod 1780883040649) ^ 2477 = 1496002202863 := by
        calc
          (7 : ZMod 1780883040649) ^ 2477 = (7 : ZMod 1780883040649) ^ (1238 + 1238 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 1238 * (7 : ZMod 1780883040649) ^ 1238) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 1496002202863 := by rw [factor_2_10]; decide
      have factor_2_12 : (7 : ZMod 1780883040649) ^ 4954 = 1288256769798 := by
        calc
          (7 : ZMod 1780883040649) ^ 4954 = (7 : ZMod 1780883040649) ^ (2477 + 2477) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 2477 * (7 : ZMod 1780883040649) ^ 2477 := by rw [pow_add]
          _ = 1288256769798 := by rw [factor_2_11]; decide
      have factor_2_13 : (7 : ZMod 1780883040649) ^ 9909 = 10100835852 := by
        calc
          (7 : ZMod 1780883040649) ^ 9909 = (7 : ZMod 1780883040649) ^ (4954 + 4954 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 4954 * (7 : ZMod 1780883040649) ^ 4954) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 10100835852 := by rw [factor_2_12]; decide
      have factor_2_14 : (7 : ZMod 1780883040649) ^ 19819 = 740731247953 := by
        calc
          (7 : ZMod 1780883040649) ^ 19819 = (7 : ZMod 1780883040649) ^ (9909 + 9909 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 9909 * (7 : ZMod 1780883040649) ^ 9909) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 740731247953 := by rw [factor_2_13]; decide
      have factor_2_15 : (7 : ZMod 1780883040649) ^ 39639 = 831181802792 := by
        calc
          (7 : ZMod 1780883040649) ^ 39639 = (7 : ZMod 1780883040649) ^ (19819 + 19819 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 19819 * (7 : ZMod 1780883040649) ^ 19819) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 831181802792 := by rw [factor_2_14]; decide
      have factor_2_16 : (7 : ZMod 1780883040649) ^ 79279 = 641122570957 := by
        calc
          (7 : ZMod 1780883040649) ^ 79279 = (7 : ZMod 1780883040649) ^ (39639 + 39639 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 39639 * (7 : ZMod 1780883040649) ^ 39639) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 641122570957 := by rw [factor_2_15]; decide
      have factor_2_17 : (7 : ZMod 1780883040649) ^ 158558 = 372029513432 := by
        calc
          (7 : ZMod 1780883040649) ^ 158558 = (7 : ZMod 1780883040649) ^ (79279 + 79279) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 79279 * (7 : ZMod 1780883040649) ^ 79279 := by rw [pow_add]
          _ = 372029513432 := by rw [factor_2_16]; decide
      have factor_2_18 : (7 : ZMod 1780883040649) ^ 317116 = 1389116102344 := by
        calc
          (7 : ZMod 1780883040649) ^ 317116 = (7 : ZMod 1780883040649) ^ (158558 + 158558) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 158558 * (7 : ZMod 1780883040649) ^ 158558 := by rw [pow_add]
          _ = 1389116102344 := by rw [factor_2_17]; decide
      have factor_2_19 : (7 : ZMod 1780883040649) ^ 634232 = 396932578231 := by
        calc
          (7 : ZMod 1780883040649) ^ 634232 = (7 : ZMod 1780883040649) ^ (317116 + 317116) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 317116 * (7 : ZMod 1780883040649) ^ 317116 := by rw [pow_add]
          _ = 396932578231 := by rw [factor_2_18]; decide
      have factor_2_20 : (7 : ZMod 1780883040649) ^ 1268464 = 1237943794769 := by
        calc
          (7 : ZMod 1780883040649) ^ 1268464 = (7 : ZMod 1780883040649) ^ (634232 + 634232) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 634232 * (7 : ZMod 1780883040649) ^ 634232 := by rw [pow_add]
          _ = 1237943794769 := by rw [factor_2_19]; decide
      have factor_2_21 : (7 : ZMod 1780883040649) ^ 2536928 = 1516552943505 := by
        calc
          (7 : ZMod 1780883040649) ^ 2536928 = (7 : ZMod 1780883040649) ^ (1268464 + 1268464) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 1268464 * (7 : ZMod 1780883040649) ^ 1268464 := by rw [pow_add]
          _ = 1516552943505 := by rw [factor_2_20]; decide
      have factor_2_22 : (7 : ZMod 1780883040649) ^ 5073856 = 1615774368845 := by
        calc
          (7 : ZMod 1780883040649) ^ 5073856 = (7 : ZMod 1780883040649) ^ (2536928 + 2536928) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 2536928 * (7 : ZMod 1780883040649) ^ 2536928 := by rw [pow_add]
          _ = 1615774368845 := by rw [factor_2_21]; decide
      have factor_2_23 : (7 : ZMod 1780883040649) ^ 10147713 = 729786616561 := by
        calc
          (7 : ZMod 1780883040649) ^ 10147713 = (7 : ZMod 1780883040649) ^ (5073856 + 5073856 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 5073856 * (7 : ZMod 1780883040649) ^ 5073856) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 729786616561 := by rw [factor_2_22]; decide
      have factor_2_24 : (7 : ZMod 1780883040649) ^ 20295426 = 1419488858162 := by
        calc
          (7 : ZMod 1780883040649) ^ 20295426 = (7 : ZMod 1780883040649) ^ (10147713 + 10147713) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 10147713 * (7 : ZMod 1780883040649) ^ 10147713 := by rw [pow_add]
          _ = 1419488858162 := by rw [factor_2_23]; decide
      have factor_2_25 : (7 : ZMod 1780883040649) ^ 40590852 = 1519591629670 := by
        calc
          (7 : ZMod 1780883040649) ^ 40590852 = (7 : ZMod 1780883040649) ^ (20295426 + 20295426) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 20295426 * (7 : ZMod 1780883040649) ^ 20295426 := by rw [pow_add]
          _ = 1519591629670 := by rw [factor_2_24]; decide
      have factor_2_26 : (7 : ZMod 1780883040649) ^ 81181704 = 8558887174 := by
        calc
          (7 : ZMod 1780883040649) ^ 81181704 = (7 : ZMod 1780883040649) ^ (40590852 + 40590852) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 40590852 * (7 : ZMod 1780883040649) ^ 40590852 := by rw [pow_add]
          _ = 8558887174 := by rw [factor_2_25]; decide
      change (7 : ZMod 1780883040649) ^ 81181704 ≠ 1
      rw [factor_2_26]
      decide
    ·
      have factor_3_0 : (7 : ZMod 1780883040649) ^ 1 = 7 := by norm_num
      have factor_3_1 : (7 : ZMod 1780883040649) ^ 2 = 49 := by
        calc
          (7 : ZMod 1780883040649) ^ 2 = (7 : ZMod 1780883040649) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 1 * (7 : ZMod 1780883040649) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_3_0]; decide
      have factor_3_2 : (7 : ZMod 1780883040649) ^ 4 = 2401 := by
        calc
          (7 : ZMod 1780883040649) ^ 4 = (7 : ZMod 1780883040649) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 2 * (7 : ZMod 1780883040649) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_3_1]; decide
      have factor_3_3 : (7 : ZMod 1780883040649) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 1780883040649) ^ 8 = (7 : ZMod 1780883040649) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 4 * (7 : ZMod 1780883040649) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [factor_3_2]; decide
      have factor_3_4 : (7 : ZMod 1780883040649) ^ 16 = 1177035837919 := by
        calc
          (7 : ZMod 1780883040649) ^ 16 = (7 : ZMod 1780883040649) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 8 * (7 : ZMod 1780883040649) ^ 8 := by rw [pow_add]
          _ = 1177035837919 := by rw [factor_3_3]; decide
      have factor_3_5 : (7 : ZMod 1780883040649) ^ 32 = 315104140865 := by
        calc
          (7 : ZMod 1780883040649) ^ 32 = (7 : ZMod 1780883040649) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 16 * (7 : ZMod 1780883040649) ^ 16 := by rw [pow_add]
          _ = 315104140865 := by rw [factor_3_4]; decide
      have factor_3_6 : (7 : ZMod 1780883040649) ^ 64 = 386591279524 := by
        calc
          (7 : ZMod 1780883040649) ^ 64 = (7 : ZMod 1780883040649) ^ (32 + 32) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 32 * (7 : ZMod 1780883040649) ^ 32 := by rw [pow_add]
          _ = 386591279524 := by rw [factor_3_5]; decide
      have factor_3_7 : (7 : ZMod 1780883040649) ^ 128 = 1127413634740 := by
        calc
          (7 : ZMod 1780883040649) ^ 128 = (7 : ZMod 1780883040649) ^ (64 + 64) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 64 * (7 : ZMod 1780883040649) ^ 64 := by rw [pow_add]
          _ = 1127413634740 := by rw [factor_3_6]; decide
      have factor_3_8 : (7 : ZMod 1780883040649) ^ 257 = 658816405028 := by
        calc
          (7 : ZMod 1780883040649) ^ 257 = (7 : ZMod 1780883040649) ^ (128 + 128 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 128 * (7 : ZMod 1780883040649) ^ 128) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 658816405028 := by rw [factor_3_7]; decide
      have factor_3_9 : (7 : ZMod 1780883040649) ^ 514 = 1503128491223 := by
        calc
          (7 : ZMod 1780883040649) ^ 514 = (7 : ZMod 1780883040649) ^ (257 + 257) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 257 * (7 : ZMod 1780883040649) ^ 257 := by rw [pow_add]
          _ = 1503128491223 := by rw [factor_3_8]; decide
      have factor_3_10 : (7 : ZMod 1780883040649) ^ 1028 = 1547975550562 := by
        calc
          (7 : ZMod 1780883040649) ^ 1028 = (7 : ZMod 1780883040649) ^ (514 + 514) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 514 * (7 : ZMod 1780883040649) ^ 514 := by rw [pow_add]
          _ = 1547975550562 := by rw [factor_3_9]; decide
      have factor_3_11 : (7 : ZMod 1780883040649) ^ 2056 = 1075232548676 := by
        calc
          (7 : ZMod 1780883040649) ^ 2056 = (7 : ZMod 1780883040649) ^ (1028 + 1028) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 1028 * (7 : ZMod 1780883040649) ^ 1028 := by rw [pow_add]
          _ = 1075232548676 := by rw [factor_3_10]; decide
      have factor_3_12 : (7 : ZMod 1780883040649) ^ 4113 = 475658278568 := by
        calc
          (7 : ZMod 1780883040649) ^ 4113 = (7 : ZMod 1780883040649) ^ (2056 + 2056 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 2056 * (7 : ZMod 1780883040649) ^ 2056) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 475658278568 := by rw [factor_3_11]; decide
      have factor_3_13 : (7 : ZMod 1780883040649) ^ 8226 = 582228410773 := by
        calc
          (7 : ZMod 1780883040649) ^ 8226 = (7 : ZMod 1780883040649) ^ (4113 + 4113) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 4113 * (7 : ZMod 1780883040649) ^ 4113 := by rw [pow_add]
          _ = 582228410773 := by rw [factor_3_12]; decide
      have factor_3_14 : (7 : ZMod 1780883040649) ^ 16452 = 395159863053 := by
        calc
          (7 : ZMod 1780883040649) ^ 16452 = (7 : ZMod 1780883040649) ^ (8226 + 8226) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 8226 * (7 : ZMod 1780883040649) ^ 8226 := by rw [pow_add]
          _ = 395159863053 := by rw [factor_3_13]; decide
      have factor_3_15 : (7 : ZMod 1780883040649) ^ 32905 = 1149749209618 := by
        calc
          (7 : ZMod 1780883040649) ^ 32905 = (7 : ZMod 1780883040649) ^ (16452 + 16452 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 16452 * (7 : ZMod 1780883040649) ^ 16452) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 1149749209618 := by rw [factor_3_14]; decide
      have factor_3_16 : (7 : ZMod 1780883040649) ^ 65811 = 1329562441373 := by
        calc
          (7 : ZMod 1780883040649) ^ 65811 = (7 : ZMod 1780883040649) ^ (32905 + 32905 + 1) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = ((7 : ZMod 1780883040649) ^ 32905 * (7 : ZMod 1780883040649) ^ 32905) * (7 : ZMod 1780883040649) := by rw [pow_succ, pow_add]
          _ = 1329562441373 := by rw [factor_3_15]; decide
      have factor_3_17 : (7 : ZMod 1780883040649) ^ 131622 = 540649061200 := by
        calc
          (7 : ZMod 1780883040649) ^ 131622 = (7 : ZMod 1780883040649) ^ (65811 + 65811) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 65811 * (7 : ZMod 1780883040649) ^ 65811 := by rw [pow_add]
          _ = 540649061200 := by rw [factor_3_16]; decide
      have factor_3_18 : (7 : ZMod 1780883040649) ^ 263244 = 849862374100 := by
        calc
          (7 : ZMod 1780883040649) ^ 263244 = (7 : ZMod 1780883040649) ^ (131622 + 131622) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 131622 * (7 : ZMod 1780883040649) ^ 131622 := by rw [pow_add]
          _ = 849862374100 := by rw [factor_3_17]; decide
      have factor_3_19 : (7 : ZMod 1780883040649) ^ 526488 = 576462493716 := by
        calc
          (7 : ZMod 1780883040649) ^ 526488 = (7 : ZMod 1780883040649) ^ (263244 + 263244) :=
            congrArg (fun n : ℕ => (7 : ZMod 1780883040649) ^ n) (by norm_num)
          _ = (7 : ZMod 1780883040649) ^ 263244 * (7 : ZMod 1780883040649) ^ 263244 := by rw [pow_add]
          _ = 576462493716 := by rw [factor_3_18]; decide
      change (7 : ZMod 1780883040649) ^ 526488 ≠ 1
      rw [factor_3_19]
      decide

#print axioms prime_lucas_1780883040649

end TotientTailPeriodKiller
end Erdos249257
