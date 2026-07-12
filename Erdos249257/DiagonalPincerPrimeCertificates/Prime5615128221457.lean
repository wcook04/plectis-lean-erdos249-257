import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_5615128221457 : Nat.Prime 5615128221457 := by
  apply lucas_primality 5615128221457 (5 : ZMod 5615128221457)
  ·
      have fermat_0 : (5 : ZMod 5615128221457) ^ 1 = 5 := by norm_num
      have fermat_1 : (5 : ZMod 5615128221457) ^ 2 = 25 := by
        calc
          (5 : ZMod 5615128221457) ^ 2 = (5 : ZMod 5615128221457) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 1 * (5 : ZMod 5615128221457) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [fermat_0]; decide
      have fermat_2 : (5 : ZMod 5615128221457) ^ 5 = 3125 := by
        calc
          (5 : ZMod 5615128221457) ^ 5 = (5 : ZMod 5615128221457) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 2 * (5 : ZMod 5615128221457) ^ 2) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [fermat_1]; decide
      have fermat_3 : (5 : ZMod 5615128221457) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 5615128221457) ^ 10 = (5 : ZMod 5615128221457) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 5 * (5 : ZMod 5615128221457) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [fermat_2]; decide
      have fermat_4 : (5 : ZMod 5615128221457) ^ 20 = 5525380097313 := by
        calc
          (5 : ZMod 5615128221457) ^ 20 = (5 : ZMod 5615128221457) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 10 * (5 : ZMod 5615128221457) ^ 10 := by rw [pow_add]
          _ = 5525380097313 := by rw [fermat_3]; decide
      have fermat_5 : (5 : ZMod 5615128221457) ^ 40 = 512664629153 := by
        calc
          (5 : ZMod 5615128221457) ^ 40 = (5 : ZMod 5615128221457) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 20 * (5 : ZMod 5615128221457) ^ 20 := by rw [pow_add]
          _ = 512664629153 := by rw [fermat_4]; decide
      have fermat_6 : (5 : ZMod 5615128221457) ^ 81 = 3004183500560 := by
        calc
          (5 : ZMod 5615128221457) ^ 81 = (5 : ZMod 5615128221457) ^ (40 + 40 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 40 * (5 : ZMod 5615128221457) ^ 40) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 3004183500560 := by rw [fermat_5]; decide
      have fermat_7 : (5 : ZMod 5615128221457) ^ 163 = 1812793926180 := by
        calc
          (5 : ZMod 5615128221457) ^ 163 = (5 : ZMod 5615128221457) ^ (81 + 81 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 81 * (5 : ZMod 5615128221457) ^ 81) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 1812793926180 := by rw [fermat_6]; decide
      have fermat_8 : (5 : ZMod 5615128221457) ^ 326 = 2624298401793 := by
        calc
          (5 : ZMod 5615128221457) ^ 326 = (5 : ZMod 5615128221457) ^ (163 + 163) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 163 * (5 : ZMod 5615128221457) ^ 163 := by rw [pow_add]
          _ = 2624298401793 := by rw [fermat_7]; decide
      have fermat_9 : (5 : ZMod 5615128221457) ^ 653 = 5302702295464 := by
        calc
          (5 : ZMod 5615128221457) ^ 653 = (5 : ZMod 5615128221457) ^ (326 + 326 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 326 * (5 : ZMod 5615128221457) ^ 326) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 5302702295464 := by rw [fermat_8]; decide
      have fermat_10 : (5 : ZMod 5615128221457) ^ 1307 = 2529096602353 := by
        calc
          (5 : ZMod 5615128221457) ^ 1307 = (5 : ZMod 5615128221457) ^ (653 + 653 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 653 * (5 : ZMod 5615128221457) ^ 653) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 2529096602353 := by rw [fermat_9]; decide
      have fermat_11 : (5 : ZMod 5615128221457) ^ 2614 = 1780545108052 := by
        calc
          (5 : ZMod 5615128221457) ^ 2614 = (5 : ZMod 5615128221457) ^ (1307 + 1307) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 1307 * (5 : ZMod 5615128221457) ^ 1307 := by rw [pow_add]
          _ = 1780545108052 := by rw [fermat_10]; decide
      have fermat_12 : (5 : ZMod 5615128221457) ^ 5229 = 3556364571567 := by
        calc
          (5 : ZMod 5615128221457) ^ 5229 = (5 : ZMod 5615128221457) ^ (2614 + 2614 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 2614 * (5 : ZMod 5615128221457) ^ 2614) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 3556364571567 := by rw [fermat_11]; decide
      have fermat_13 : (5 : ZMod 5615128221457) ^ 10458 = 2998554482518 := by
        calc
          (5 : ZMod 5615128221457) ^ 10458 = (5 : ZMod 5615128221457) ^ (5229 + 5229) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 5229 * (5 : ZMod 5615128221457) ^ 5229 := by rw [pow_add]
          _ = 2998554482518 := by rw [fermat_12]; decide
      have fermat_14 : (5 : ZMod 5615128221457) ^ 20917 = 373845685306 := by
        calc
          (5 : ZMod 5615128221457) ^ 20917 = (5 : ZMod 5615128221457) ^ (10458 + 10458 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 10458 * (5 : ZMod 5615128221457) ^ 10458) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 373845685306 := by rw [fermat_13]; decide
      have fermat_15 : (5 : ZMod 5615128221457) ^ 41835 = 4486907926175 := by
        calc
          (5 : ZMod 5615128221457) ^ 41835 = (5 : ZMod 5615128221457) ^ (20917 + 20917 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 20917 * (5 : ZMod 5615128221457) ^ 20917) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 4486907926175 := by rw [fermat_14]; decide
      have fermat_16 : (5 : ZMod 5615128221457) ^ 83671 = 1265893063302 := by
        calc
          (5 : ZMod 5615128221457) ^ 83671 = (5 : ZMod 5615128221457) ^ (41835 + 41835 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 41835 * (5 : ZMod 5615128221457) ^ 41835) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 1265893063302 := by rw [fermat_15]; decide
      have fermat_17 : (5 : ZMod 5615128221457) ^ 167343 = 26226940845 := by
        calc
          (5 : ZMod 5615128221457) ^ 167343 = (5 : ZMod 5615128221457) ^ (83671 + 83671 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 83671 * (5 : ZMod 5615128221457) ^ 83671) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 26226940845 := by rw [fermat_16]; decide
      have fermat_18 : (5 : ZMod 5615128221457) ^ 334687 = 2922476204197 := by
        calc
          (5 : ZMod 5615128221457) ^ 334687 = (5 : ZMod 5615128221457) ^ (167343 + 167343 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 167343 * (5 : ZMod 5615128221457) ^ 167343) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 2922476204197 := by rw [fermat_17]; decide
      have fermat_19 : (5 : ZMod 5615128221457) ^ 669375 = 500089060598 := by
        calc
          (5 : ZMod 5615128221457) ^ 669375 = (5 : ZMod 5615128221457) ^ (334687 + 334687 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 334687 * (5 : ZMod 5615128221457) ^ 334687) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 500089060598 := by rw [fermat_18]; decide
      have fermat_20 : (5 : ZMod 5615128221457) ^ 1338750 = 3134348929383 := by
        calc
          (5 : ZMod 5615128221457) ^ 1338750 = (5 : ZMod 5615128221457) ^ (669375 + 669375) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 669375 * (5 : ZMod 5615128221457) ^ 669375 := by rw [pow_add]
          _ = 3134348929383 := by rw [fermat_19]; decide
      have fermat_21 : (5 : ZMod 5615128221457) ^ 2677501 = 1958451655357 := by
        calc
          (5 : ZMod 5615128221457) ^ 2677501 = (5 : ZMod 5615128221457) ^ (1338750 + 1338750 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 1338750 * (5 : ZMod 5615128221457) ^ 1338750) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 1958451655357 := by rw [fermat_20]; decide
      have fermat_22 : (5 : ZMod 5615128221457) ^ 5355003 = 4104573768942 := by
        calc
          (5 : ZMod 5615128221457) ^ 5355003 = (5 : ZMod 5615128221457) ^ (2677501 + 2677501 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 2677501 * (5 : ZMod 5615128221457) ^ 2677501) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 4104573768942 := by rw [fermat_21]; decide
      have fermat_23 : (5 : ZMod 5615128221457) ^ 10710007 = 3942313427829 := by
        calc
          (5 : ZMod 5615128221457) ^ 10710007 = (5 : ZMod 5615128221457) ^ (5355003 + 5355003 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 5355003 * (5 : ZMod 5615128221457) ^ 5355003) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 3942313427829 := by rw [fermat_22]; decide
      have fermat_24 : (5 : ZMod 5615128221457) ^ 21420014 = 4711636903467 := by
        calc
          (5 : ZMod 5615128221457) ^ 21420014 = (5 : ZMod 5615128221457) ^ (10710007 + 10710007) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 10710007 * (5 : ZMod 5615128221457) ^ 10710007 := by rw [pow_add]
          _ = 4711636903467 := by rw [fermat_23]; decide
      have fermat_25 : (5 : ZMod 5615128221457) ^ 42840028 = 4780707541890 := by
        calc
          (5 : ZMod 5615128221457) ^ 42840028 = (5 : ZMod 5615128221457) ^ (21420014 + 21420014) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 21420014 * (5 : ZMod 5615128221457) ^ 21420014 := by rw [pow_add]
          _ = 4780707541890 := by rw [fermat_24]; decide
      have fermat_26 : (5 : ZMod 5615128221457) ^ 85680057 = 493367049084 := by
        calc
          (5 : ZMod 5615128221457) ^ 85680057 = (5 : ZMod 5615128221457) ^ (42840028 + 42840028 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 42840028 * (5 : ZMod 5615128221457) ^ 42840028) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 493367049084 := by rw [fermat_25]; decide
      have fermat_27 : (5 : ZMod 5615128221457) ^ 171360114 = 1272607883414 := by
        calc
          (5 : ZMod 5615128221457) ^ 171360114 = (5 : ZMod 5615128221457) ^ (85680057 + 85680057) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 85680057 * (5 : ZMod 5615128221457) ^ 85680057 := by rw [pow_add]
          _ = 1272607883414 := by rw [fermat_26]; decide
      have fermat_28 : (5 : ZMod 5615128221457) ^ 342720228 = 2251978959126 := by
        calc
          (5 : ZMod 5615128221457) ^ 342720228 = (5 : ZMod 5615128221457) ^ (171360114 + 171360114) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 171360114 * (5 : ZMod 5615128221457) ^ 171360114 := by rw [pow_add]
          _ = 2251978959126 := by rw [fermat_27]; decide
      have fermat_29 : (5 : ZMod 5615128221457) ^ 685440456 = 4992264857344 := by
        calc
          (5 : ZMod 5615128221457) ^ 685440456 = (5 : ZMod 5615128221457) ^ (342720228 + 342720228) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 342720228 * (5 : ZMod 5615128221457) ^ 342720228 := by rw [pow_add]
          _ = 4992264857344 := by rw [fermat_28]; decide
      have fermat_30 : (5 : ZMod 5615128221457) ^ 1370880913 = 764304104914 := by
        calc
          (5 : ZMod 5615128221457) ^ 1370880913 = (5 : ZMod 5615128221457) ^ (685440456 + 685440456 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 685440456 * (5 : ZMod 5615128221457) ^ 685440456) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 764304104914 := by rw [fermat_29]; decide
      have fermat_31 : (5 : ZMod 5615128221457) ^ 2741761826 = 5529211625171 := by
        calc
          (5 : ZMod 5615128221457) ^ 2741761826 = (5 : ZMod 5615128221457) ^ (1370880913 + 1370880913) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 1370880913 * (5 : ZMod 5615128221457) ^ 1370880913 := by rw [pow_add]
          _ = 5529211625171 := by rw [fermat_30]; decide
      have fermat_32 : (5 : ZMod 5615128221457) ^ 5483523653 = 2407147701384 := by
        calc
          (5 : ZMod 5615128221457) ^ 5483523653 = (5 : ZMod 5615128221457) ^ (2741761826 + 2741761826 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 2741761826 * (5 : ZMod 5615128221457) ^ 2741761826) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 2407147701384 := by rw [fermat_31]; decide
      have fermat_33 : (5 : ZMod 5615128221457) ^ 10967047307 = 905030759936 := by
        calc
          (5 : ZMod 5615128221457) ^ 10967047307 = (5 : ZMod 5615128221457) ^ (5483523653 + 5483523653 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 5483523653 * (5 : ZMod 5615128221457) ^ 5483523653) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 905030759936 := by rw [fermat_32]; decide
      have fermat_34 : (5 : ZMod 5615128221457) ^ 21934094615 = 2523560447070 := by
        calc
          (5 : ZMod 5615128221457) ^ 21934094615 = (5 : ZMod 5615128221457) ^ (10967047307 + 10967047307 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 10967047307 * (5 : ZMod 5615128221457) ^ 10967047307) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 2523560447070 := by rw [fermat_33]; decide
      have fermat_35 : (5 : ZMod 5615128221457) ^ 43868189230 = 5444421782331 := by
        calc
          (5 : ZMod 5615128221457) ^ 43868189230 = (5 : ZMod 5615128221457) ^ (21934094615 + 21934094615) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 21934094615 * (5 : ZMod 5615128221457) ^ 21934094615 := by rw [pow_add]
          _ = 5444421782331 := by rw [fermat_34]; decide
      have fermat_36 : (5 : ZMod 5615128221457) ^ 87736378460 = 1904021758563 := by
        calc
          (5 : ZMod 5615128221457) ^ 87736378460 = (5 : ZMod 5615128221457) ^ (43868189230 + 43868189230) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 43868189230 * (5 : ZMod 5615128221457) ^ 43868189230 := by rw [pow_add]
          _ = 1904021758563 := by rw [fermat_35]; decide
      have fermat_37 : (5 : ZMod 5615128221457) ^ 175472756920 = 2969462958498 := by
        calc
          (5 : ZMod 5615128221457) ^ 175472756920 = (5 : ZMod 5615128221457) ^ (87736378460 + 87736378460) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 87736378460 * (5 : ZMod 5615128221457) ^ 87736378460 := by rw [pow_add]
          _ = 2969462958498 := by rw [fermat_36]; decide
      have fermat_38 : (5 : ZMod 5615128221457) ^ 350945513841 = 1166026253811 := by
        calc
          (5 : ZMod 5615128221457) ^ 350945513841 = (5 : ZMod 5615128221457) ^ (175472756920 + 175472756920 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 175472756920 * (5 : ZMod 5615128221457) ^ 175472756920) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 1166026253811 := by rw [fermat_37]; decide
      have fermat_39 : (5 : ZMod 5615128221457) ^ 701891027682 = 672602383608 := by
        calc
          (5 : ZMod 5615128221457) ^ 701891027682 = (5 : ZMod 5615128221457) ^ (350945513841 + 350945513841) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 350945513841 * (5 : ZMod 5615128221457) ^ 350945513841 := by rw [pow_add]
          _ = 672602383608 := by rw [fermat_38]; decide
      have fermat_40 : (5 : ZMod 5615128221457) ^ 1403782055364 = 4502396918366 := by
        calc
          (5 : ZMod 5615128221457) ^ 1403782055364 = (5 : ZMod 5615128221457) ^ (701891027682 + 701891027682) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 701891027682 * (5 : ZMod 5615128221457) ^ 701891027682 := by rw [pow_add]
          _ = 4502396918366 := by rw [fermat_39]; decide
      have fermat_41 : (5 : ZMod 5615128221457) ^ 2807564110728 = 5615128221456 := by
        calc
          (5 : ZMod 5615128221457) ^ 2807564110728 = (5 : ZMod 5615128221457) ^ (1403782055364 + 1403782055364) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 1403782055364 * (5 : ZMod 5615128221457) ^ 1403782055364 := by rw [pow_add]
          _ = 5615128221456 := by rw [fermat_40]; decide
      have fermat_42 : (5 : ZMod 5615128221457) ^ 5615128221456 = 1 := by
        calc
          (5 : ZMod 5615128221457) ^ 5615128221456 = (5 : ZMod 5615128221457) ^ (2807564110728 + 2807564110728) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 2807564110728 * (5 : ZMod 5615128221457) ^ 2807564110728 := by rw [pow_add]
          _ = 1 := by rw [fermat_41]; decide
      simpa using fermat_42
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (13, 1), (467, 1), (19268957, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (13, 1), (467, 1), (19268957, 1)] : List FactorBlock).map factorBlockValue).prod = 5615128221457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (5 : ZMod 5615128221457) ^ 1 = 5 := by norm_num
      have factor_0_1 : (5 : ZMod 5615128221457) ^ 2 = 25 := by
        calc
          (5 : ZMod 5615128221457) ^ 2 = (5 : ZMod 5615128221457) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 1 * (5 : ZMod 5615128221457) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_0_0]; decide
      have factor_0_2 : (5 : ZMod 5615128221457) ^ 5 = 3125 := by
        calc
          (5 : ZMod 5615128221457) ^ 5 = (5 : ZMod 5615128221457) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 2 * (5 : ZMod 5615128221457) ^ 2) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_0_1]; decide
      have factor_0_3 : (5 : ZMod 5615128221457) ^ 10 = 9765625 := by
        calc
          (5 : ZMod 5615128221457) ^ 10 = (5 : ZMod 5615128221457) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 5 * (5 : ZMod 5615128221457) ^ 5 := by rw [pow_add]
          _ = 9765625 := by rw [factor_0_2]; decide
      have factor_0_4 : (5 : ZMod 5615128221457) ^ 20 = 5525380097313 := by
        calc
          (5 : ZMod 5615128221457) ^ 20 = (5 : ZMod 5615128221457) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 10 * (5 : ZMod 5615128221457) ^ 10 := by rw [pow_add]
          _ = 5525380097313 := by rw [factor_0_3]; decide
      have factor_0_5 : (5 : ZMod 5615128221457) ^ 40 = 512664629153 := by
        calc
          (5 : ZMod 5615128221457) ^ 40 = (5 : ZMod 5615128221457) ^ (20 + 20) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 20 * (5 : ZMod 5615128221457) ^ 20 := by rw [pow_add]
          _ = 512664629153 := by rw [factor_0_4]; decide
      have factor_0_6 : (5 : ZMod 5615128221457) ^ 81 = 3004183500560 := by
        calc
          (5 : ZMod 5615128221457) ^ 81 = (5 : ZMod 5615128221457) ^ (40 + 40 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 40 * (5 : ZMod 5615128221457) ^ 40) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 3004183500560 := by rw [factor_0_5]; decide
      have factor_0_7 : (5 : ZMod 5615128221457) ^ 163 = 1812793926180 := by
        calc
          (5 : ZMod 5615128221457) ^ 163 = (5 : ZMod 5615128221457) ^ (81 + 81 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 81 * (5 : ZMod 5615128221457) ^ 81) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 1812793926180 := by rw [factor_0_6]; decide
      have factor_0_8 : (5 : ZMod 5615128221457) ^ 326 = 2624298401793 := by
        calc
          (5 : ZMod 5615128221457) ^ 326 = (5 : ZMod 5615128221457) ^ (163 + 163) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 163 * (5 : ZMod 5615128221457) ^ 163 := by rw [pow_add]
          _ = 2624298401793 := by rw [factor_0_7]; decide
      have factor_0_9 : (5 : ZMod 5615128221457) ^ 653 = 5302702295464 := by
        calc
          (5 : ZMod 5615128221457) ^ 653 = (5 : ZMod 5615128221457) ^ (326 + 326 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 326 * (5 : ZMod 5615128221457) ^ 326) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 5302702295464 := by rw [factor_0_8]; decide
      have factor_0_10 : (5 : ZMod 5615128221457) ^ 1307 = 2529096602353 := by
        calc
          (5 : ZMod 5615128221457) ^ 1307 = (5 : ZMod 5615128221457) ^ (653 + 653 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 653 * (5 : ZMod 5615128221457) ^ 653) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 2529096602353 := by rw [factor_0_9]; decide
      have factor_0_11 : (5 : ZMod 5615128221457) ^ 2614 = 1780545108052 := by
        calc
          (5 : ZMod 5615128221457) ^ 2614 = (5 : ZMod 5615128221457) ^ (1307 + 1307) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 1307 * (5 : ZMod 5615128221457) ^ 1307 := by rw [pow_add]
          _ = 1780545108052 := by rw [factor_0_10]; decide
      have factor_0_12 : (5 : ZMod 5615128221457) ^ 5229 = 3556364571567 := by
        calc
          (5 : ZMod 5615128221457) ^ 5229 = (5 : ZMod 5615128221457) ^ (2614 + 2614 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 2614 * (5 : ZMod 5615128221457) ^ 2614) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 3556364571567 := by rw [factor_0_11]; decide
      have factor_0_13 : (5 : ZMod 5615128221457) ^ 10458 = 2998554482518 := by
        calc
          (5 : ZMod 5615128221457) ^ 10458 = (5 : ZMod 5615128221457) ^ (5229 + 5229) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 5229 * (5 : ZMod 5615128221457) ^ 5229 := by rw [pow_add]
          _ = 2998554482518 := by rw [factor_0_12]; decide
      have factor_0_14 : (5 : ZMod 5615128221457) ^ 20917 = 373845685306 := by
        calc
          (5 : ZMod 5615128221457) ^ 20917 = (5 : ZMod 5615128221457) ^ (10458 + 10458 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 10458 * (5 : ZMod 5615128221457) ^ 10458) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 373845685306 := by rw [factor_0_13]; decide
      have factor_0_15 : (5 : ZMod 5615128221457) ^ 41835 = 4486907926175 := by
        calc
          (5 : ZMod 5615128221457) ^ 41835 = (5 : ZMod 5615128221457) ^ (20917 + 20917 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 20917 * (5 : ZMod 5615128221457) ^ 20917) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 4486907926175 := by rw [factor_0_14]; decide
      have factor_0_16 : (5 : ZMod 5615128221457) ^ 83671 = 1265893063302 := by
        calc
          (5 : ZMod 5615128221457) ^ 83671 = (5 : ZMod 5615128221457) ^ (41835 + 41835 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 41835 * (5 : ZMod 5615128221457) ^ 41835) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 1265893063302 := by rw [factor_0_15]; decide
      have factor_0_17 : (5 : ZMod 5615128221457) ^ 167343 = 26226940845 := by
        calc
          (5 : ZMod 5615128221457) ^ 167343 = (5 : ZMod 5615128221457) ^ (83671 + 83671 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 83671 * (5 : ZMod 5615128221457) ^ 83671) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 26226940845 := by rw [factor_0_16]; decide
      have factor_0_18 : (5 : ZMod 5615128221457) ^ 334687 = 2922476204197 := by
        calc
          (5 : ZMod 5615128221457) ^ 334687 = (5 : ZMod 5615128221457) ^ (167343 + 167343 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 167343 * (5 : ZMod 5615128221457) ^ 167343) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 2922476204197 := by rw [factor_0_17]; decide
      have factor_0_19 : (5 : ZMod 5615128221457) ^ 669375 = 500089060598 := by
        calc
          (5 : ZMod 5615128221457) ^ 669375 = (5 : ZMod 5615128221457) ^ (334687 + 334687 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 334687 * (5 : ZMod 5615128221457) ^ 334687) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 500089060598 := by rw [factor_0_18]; decide
      have factor_0_20 : (5 : ZMod 5615128221457) ^ 1338750 = 3134348929383 := by
        calc
          (5 : ZMod 5615128221457) ^ 1338750 = (5 : ZMod 5615128221457) ^ (669375 + 669375) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 669375 * (5 : ZMod 5615128221457) ^ 669375 := by rw [pow_add]
          _ = 3134348929383 := by rw [factor_0_19]; decide
      have factor_0_21 : (5 : ZMod 5615128221457) ^ 2677501 = 1958451655357 := by
        calc
          (5 : ZMod 5615128221457) ^ 2677501 = (5 : ZMod 5615128221457) ^ (1338750 + 1338750 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 1338750 * (5 : ZMod 5615128221457) ^ 1338750) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 1958451655357 := by rw [factor_0_20]; decide
      have factor_0_22 : (5 : ZMod 5615128221457) ^ 5355003 = 4104573768942 := by
        calc
          (5 : ZMod 5615128221457) ^ 5355003 = (5 : ZMod 5615128221457) ^ (2677501 + 2677501 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 2677501 * (5 : ZMod 5615128221457) ^ 2677501) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 4104573768942 := by rw [factor_0_21]; decide
      have factor_0_23 : (5 : ZMod 5615128221457) ^ 10710007 = 3942313427829 := by
        calc
          (5 : ZMod 5615128221457) ^ 10710007 = (5 : ZMod 5615128221457) ^ (5355003 + 5355003 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 5355003 * (5 : ZMod 5615128221457) ^ 5355003) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 3942313427829 := by rw [factor_0_22]; decide
      have factor_0_24 : (5 : ZMod 5615128221457) ^ 21420014 = 4711636903467 := by
        calc
          (5 : ZMod 5615128221457) ^ 21420014 = (5 : ZMod 5615128221457) ^ (10710007 + 10710007) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 10710007 * (5 : ZMod 5615128221457) ^ 10710007 := by rw [pow_add]
          _ = 4711636903467 := by rw [factor_0_23]; decide
      have factor_0_25 : (5 : ZMod 5615128221457) ^ 42840028 = 4780707541890 := by
        calc
          (5 : ZMod 5615128221457) ^ 42840028 = (5 : ZMod 5615128221457) ^ (21420014 + 21420014) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 21420014 * (5 : ZMod 5615128221457) ^ 21420014 := by rw [pow_add]
          _ = 4780707541890 := by rw [factor_0_24]; decide
      have factor_0_26 : (5 : ZMod 5615128221457) ^ 85680057 = 493367049084 := by
        calc
          (5 : ZMod 5615128221457) ^ 85680057 = (5 : ZMod 5615128221457) ^ (42840028 + 42840028 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 42840028 * (5 : ZMod 5615128221457) ^ 42840028) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 493367049084 := by rw [factor_0_25]; decide
      have factor_0_27 : (5 : ZMod 5615128221457) ^ 171360114 = 1272607883414 := by
        calc
          (5 : ZMod 5615128221457) ^ 171360114 = (5 : ZMod 5615128221457) ^ (85680057 + 85680057) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 85680057 * (5 : ZMod 5615128221457) ^ 85680057 := by rw [pow_add]
          _ = 1272607883414 := by rw [factor_0_26]; decide
      have factor_0_28 : (5 : ZMod 5615128221457) ^ 342720228 = 2251978959126 := by
        calc
          (5 : ZMod 5615128221457) ^ 342720228 = (5 : ZMod 5615128221457) ^ (171360114 + 171360114) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 171360114 * (5 : ZMod 5615128221457) ^ 171360114 := by rw [pow_add]
          _ = 2251978959126 := by rw [factor_0_27]; decide
      have factor_0_29 : (5 : ZMod 5615128221457) ^ 685440456 = 4992264857344 := by
        calc
          (5 : ZMod 5615128221457) ^ 685440456 = (5 : ZMod 5615128221457) ^ (342720228 + 342720228) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 342720228 * (5 : ZMod 5615128221457) ^ 342720228 := by rw [pow_add]
          _ = 4992264857344 := by rw [factor_0_28]; decide
      have factor_0_30 : (5 : ZMod 5615128221457) ^ 1370880913 = 764304104914 := by
        calc
          (5 : ZMod 5615128221457) ^ 1370880913 = (5 : ZMod 5615128221457) ^ (685440456 + 685440456 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 685440456 * (5 : ZMod 5615128221457) ^ 685440456) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 764304104914 := by rw [factor_0_29]; decide
      have factor_0_31 : (5 : ZMod 5615128221457) ^ 2741761826 = 5529211625171 := by
        calc
          (5 : ZMod 5615128221457) ^ 2741761826 = (5 : ZMod 5615128221457) ^ (1370880913 + 1370880913) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 1370880913 * (5 : ZMod 5615128221457) ^ 1370880913 := by rw [pow_add]
          _ = 5529211625171 := by rw [factor_0_30]; decide
      have factor_0_32 : (5 : ZMod 5615128221457) ^ 5483523653 = 2407147701384 := by
        calc
          (5 : ZMod 5615128221457) ^ 5483523653 = (5 : ZMod 5615128221457) ^ (2741761826 + 2741761826 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 2741761826 * (5 : ZMod 5615128221457) ^ 2741761826) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 2407147701384 := by rw [factor_0_31]; decide
      have factor_0_33 : (5 : ZMod 5615128221457) ^ 10967047307 = 905030759936 := by
        calc
          (5 : ZMod 5615128221457) ^ 10967047307 = (5 : ZMod 5615128221457) ^ (5483523653 + 5483523653 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 5483523653 * (5 : ZMod 5615128221457) ^ 5483523653) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 905030759936 := by rw [factor_0_32]; decide
      have factor_0_34 : (5 : ZMod 5615128221457) ^ 21934094615 = 2523560447070 := by
        calc
          (5 : ZMod 5615128221457) ^ 21934094615 = (5 : ZMod 5615128221457) ^ (10967047307 + 10967047307 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 10967047307 * (5 : ZMod 5615128221457) ^ 10967047307) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 2523560447070 := by rw [factor_0_33]; decide
      have factor_0_35 : (5 : ZMod 5615128221457) ^ 43868189230 = 5444421782331 := by
        calc
          (5 : ZMod 5615128221457) ^ 43868189230 = (5 : ZMod 5615128221457) ^ (21934094615 + 21934094615) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 21934094615 * (5 : ZMod 5615128221457) ^ 21934094615 := by rw [pow_add]
          _ = 5444421782331 := by rw [factor_0_34]; decide
      have factor_0_36 : (5 : ZMod 5615128221457) ^ 87736378460 = 1904021758563 := by
        calc
          (5 : ZMod 5615128221457) ^ 87736378460 = (5 : ZMod 5615128221457) ^ (43868189230 + 43868189230) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 43868189230 * (5 : ZMod 5615128221457) ^ 43868189230 := by rw [pow_add]
          _ = 1904021758563 := by rw [factor_0_35]; decide
      have factor_0_37 : (5 : ZMod 5615128221457) ^ 175472756920 = 2969462958498 := by
        calc
          (5 : ZMod 5615128221457) ^ 175472756920 = (5 : ZMod 5615128221457) ^ (87736378460 + 87736378460) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 87736378460 * (5 : ZMod 5615128221457) ^ 87736378460 := by rw [pow_add]
          _ = 2969462958498 := by rw [factor_0_36]; decide
      have factor_0_38 : (5 : ZMod 5615128221457) ^ 350945513841 = 1166026253811 := by
        calc
          (5 : ZMod 5615128221457) ^ 350945513841 = (5 : ZMod 5615128221457) ^ (175472756920 + 175472756920 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 175472756920 * (5 : ZMod 5615128221457) ^ 175472756920) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 1166026253811 := by rw [factor_0_37]; decide
      have factor_0_39 : (5 : ZMod 5615128221457) ^ 701891027682 = 672602383608 := by
        calc
          (5 : ZMod 5615128221457) ^ 701891027682 = (5 : ZMod 5615128221457) ^ (350945513841 + 350945513841) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 350945513841 * (5 : ZMod 5615128221457) ^ 350945513841 := by rw [pow_add]
          _ = 672602383608 := by rw [factor_0_38]; decide
      have factor_0_40 : (5 : ZMod 5615128221457) ^ 1403782055364 = 4502396918366 := by
        calc
          (5 : ZMod 5615128221457) ^ 1403782055364 = (5 : ZMod 5615128221457) ^ (701891027682 + 701891027682) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 701891027682 * (5 : ZMod 5615128221457) ^ 701891027682 := by rw [pow_add]
          _ = 4502396918366 := by rw [factor_0_39]; decide
      have factor_0_41 : (5 : ZMod 5615128221457) ^ 2807564110728 = 5615128221456 := by
        calc
          (5 : ZMod 5615128221457) ^ 2807564110728 = (5 : ZMod 5615128221457) ^ (1403782055364 + 1403782055364) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 1403782055364 * (5 : ZMod 5615128221457) ^ 1403782055364 := by rw [pow_add]
          _ = 5615128221456 := by rw [factor_0_40]; decide
      change (5 : ZMod 5615128221457) ^ 2807564110728 ≠ 1
      rw [factor_0_41]
      decide
    ·
      have factor_1_0 : (5 : ZMod 5615128221457) ^ 1 = 5 := by norm_num
      have factor_1_1 : (5 : ZMod 5615128221457) ^ 3 = 125 := by
        calc
          (5 : ZMod 5615128221457) ^ 3 = (5 : ZMod 5615128221457) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 1 * (5 : ZMod 5615128221457) ^ 1) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_1_0]; decide
      have factor_1_2 : (5 : ZMod 5615128221457) ^ 6 = 15625 := by
        calc
          (5 : ZMod 5615128221457) ^ 6 = (5 : ZMod 5615128221457) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 3 * (5 : ZMod 5615128221457) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_1_1]; decide
      have factor_1_3 : (5 : ZMod 5615128221457) ^ 13 = 1220703125 := by
        calc
          (5 : ZMod 5615128221457) ^ 13 = (5 : ZMod 5615128221457) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 6 * (5 : ZMod 5615128221457) ^ 6) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 1220703125 := by rw [factor_1_2]; decide
      have factor_1_4 : (5 : ZMod 5615128221457) ^ 27 = 1722949849793 := by
        calc
          (5 : ZMod 5615128221457) ^ 27 = (5 : ZMod 5615128221457) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 13 * (5 : ZMod 5615128221457) ^ 13) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 1722949849793 := by rw [factor_1_3]; decide
      have factor_1_5 : (5 : ZMod 5615128221457) ^ 54 = 4371124803553 := by
        calc
          (5 : ZMod 5615128221457) ^ 54 = (5 : ZMod 5615128221457) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 27 * (5 : ZMod 5615128221457) ^ 27 := by rw [pow_add]
          _ = 4371124803553 := by rw [factor_1_4]; decide
      have factor_1_6 : (5 : ZMod 5615128221457) ^ 108 = 1011021656088 := by
        calc
          (5 : ZMod 5615128221457) ^ 108 = (5 : ZMod 5615128221457) ^ (54 + 54) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 54 * (5 : ZMod 5615128221457) ^ 54 := by rw [pow_add]
          _ = 1011021656088 := by rw [factor_1_5]; decide
      have factor_1_7 : (5 : ZMod 5615128221457) ^ 217 = 759546946672 := by
        calc
          (5 : ZMod 5615128221457) ^ 217 = (5 : ZMod 5615128221457) ^ (108 + 108 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 108 * (5 : ZMod 5615128221457) ^ 108) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 759546946672 := by rw [factor_1_6]; decide
      have factor_1_8 : (5 : ZMod 5615128221457) ^ 435 = 3840527590084 := by
        calc
          (5 : ZMod 5615128221457) ^ 435 = (5 : ZMod 5615128221457) ^ (217 + 217 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 217 * (5 : ZMod 5615128221457) ^ 217) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 3840527590084 := by rw [factor_1_7]; decide
      have factor_1_9 : (5 : ZMod 5615128221457) ^ 871 = 5198393153598 := by
        calc
          (5 : ZMod 5615128221457) ^ 871 = (5 : ZMod 5615128221457) ^ (435 + 435 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 435 * (5 : ZMod 5615128221457) ^ 435) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 5198393153598 := by rw [factor_1_8]; decide
      have factor_1_10 : (5 : ZMod 5615128221457) ^ 1743 = 1469638626644 := by
        calc
          (5 : ZMod 5615128221457) ^ 1743 = (5 : ZMod 5615128221457) ^ (871 + 871 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 871 * (5 : ZMod 5615128221457) ^ 871) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 1469638626644 := by rw [factor_1_9]; decide
      have factor_1_11 : (5 : ZMod 5615128221457) ^ 3486 = 1966721855119 := by
        calc
          (5 : ZMod 5615128221457) ^ 3486 = (5 : ZMod 5615128221457) ^ (1743 + 1743) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 1743 * (5 : ZMod 5615128221457) ^ 1743 := by rw [pow_add]
          _ = 1966721855119 := by rw [factor_1_10]; decide
      have factor_1_12 : (5 : ZMod 5615128221457) ^ 6972 = 5203996430660 := by
        calc
          (5 : ZMod 5615128221457) ^ 6972 = (5 : ZMod 5615128221457) ^ (3486 + 3486) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 3486 * (5 : ZMod 5615128221457) ^ 3486 := by rw [pow_add]
          _ = 5203996430660 := by rw [factor_1_11]; decide
      have factor_1_13 : (5 : ZMod 5615128221457) ^ 13945 = 5531263459611 := by
        calc
          (5 : ZMod 5615128221457) ^ 13945 = (5 : ZMod 5615128221457) ^ (6972 + 6972 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 6972 * (5 : ZMod 5615128221457) ^ 6972) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 5531263459611 := by rw [factor_1_12]; decide
      have factor_1_14 : (5 : ZMod 5615128221457) ^ 27890 = 255001883368 := by
        calc
          (5 : ZMod 5615128221457) ^ 27890 = (5 : ZMod 5615128221457) ^ (13945 + 13945) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 13945 * (5 : ZMod 5615128221457) ^ 13945 := by rw [pow_add]
          _ = 255001883368 := by rw [factor_1_13]; decide
      have factor_1_15 : (5 : ZMod 5615128221457) ^ 55781 = 2642664916183 := by
        calc
          (5 : ZMod 5615128221457) ^ 55781 = (5 : ZMod 5615128221457) ^ (27890 + 27890 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 27890 * (5 : ZMod 5615128221457) ^ 27890) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 2642664916183 := by rw [factor_1_14]; decide
      have factor_1_16 : (5 : ZMod 5615128221457) ^ 111562 = 3518811064512 := by
        calc
          (5 : ZMod 5615128221457) ^ 111562 = (5 : ZMod 5615128221457) ^ (55781 + 55781) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 55781 * (5 : ZMod 5615128221457) ^ 55781 := by rw [pow_add]
          _ = 3518811064512 := by rw [factor_1_15]; decide
      have factor_1_17 : (5 : ZMod 5615128221457) ^ 223125 = 3585565092646 := by
        calc
          (5 : ZMod 5615128221457) ^ 223125 = (5 : ZMod 5615128221457) ^ (111562 + 111562 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 111562 * (5 : ZMod 5615128221457) ^ 111562) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 3585565092646 := by rw [factor_1_16]; decide
      have factor_1_18 : (5 : ZMod 5615128221457) ^ 446250 = 2073695054772 := by
        calc
          (5 : ZMod 5615128221457) ^ 446250 = (5 : ZMod 5615128221457) ^ (223125 + 223125) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 223125 * (5 : ZMod 5615128221457) ^ 223125 := by rw [pow_add]
          _ = 2073695054772 := by rw [factor_1_17]; decide
      have factor_1_19 : (5 : ZMod 5615128221457) ^ 892500 = 3777048826596 := by
        calc
          (5 : ZMod 5615128221457) ^ 892500 = (5 : ZMod 5615128221457) ^ (446250 + 446250) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 446250 * (5 : ZMod 5615128221457) ^ 446250 := by rw [pow_add]
          _ = 3777048826596 := by rw [factor_1_18]; decide
      have factor_1_20 : (5 : ZMod 5615128221457) ^ 1785001 = 4254101904685 := by
        calc
          (5 : ZMod 5615128221457) ^ 1785001 = (5 : ZMod 5615128221457) ^ (892500 + 892500 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 892500 * (5 : ZMod 5615128221457) ^ 892500) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 4254101904685 := by rw [factor_1_19]; decide
      have factor_1_21 : (5 : ZMod 5615128221457) ^ 3570002 = 692147603945 := by
        calc
          (5 : ZMod 5615128221457) ^ 3570002 = (5 : ZMod 5615128221457) ^ (1785001 + 1785001) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 1785001 * (5 : ZMod 5615128221457) ^ 1785001 := by rw [pow_add]
          _ = 692147603945 := by rw [factor_1_20]; decide
      have factor_1_22 : (5 : ZMod 5615128221457) ^ 7140004 = 1393519377026 := by
        calc
          (5 : ZMod 5615128221457) ^ 7140004 = (5 : ZMod 5615128221457) ^ (3570002 + 3570002) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 3570002 * (5 : ZMod 5615128221457) ^ 3570002 := by rw [pow_add]
          _ = 1393519377026 := by rw [factor_1_21]; decide
      have factor_1_23 : (5 : ZMod 5615128221457) ^ 14280009 = 2277862324267 := by
        calc
          (5 : ZMod 5615128221457) ^ 14280009 = (5 : ZMod 5615128221457) ^ (7140004 + 7140004 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 7140004 * (5 : ZMod 5615128221457) ^ 7140004) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 2277862324267 := by rw [factor_1_22]; decide
      have factor_1_24 : (5 : ZMod 5615128221457) ^ 28560019 = 342718657657 := by
        calc
          (5 : ZMod 5615128221457) ^ 28560019 = (5 : ZMod 5615128221457) ^ (14280009 + 14280009 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 14280009 * (5 : ZMod 5615128221457) ^ 14280009) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 342718657657 := by rw [factor_1_23]; decide
      have factor_1_25 : (5 : ZMod 5615128221457) ^ 57120038 = 1102877872585 := by
        calc
          (5 : ZMod 5615128221457) ^ 57120038 = (5 : ZMod 5615128221457) ^ (28560019 + 28560019) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 28560019 * (5 : ZMod 5615128221457) ^ 28560019 := by rw [pow_add]
          _ = 1102877872585 := by rw [factor_1_24]; decide
      have factor_1_26 : (5 : ZMod 5615128221457) ^ 114240076 = 1797447102291 := by
        calc
          (5 : ZMod 5615128221457) ^ 114240076 = (5 : ZMod 5615128221457) ^ (57120038 + 57120038) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 57120038 * (5 : ZMod 5615128221457) ^ 57120038 := by rw [pow_add]
          _ = 1797447102291 := by rw [factor_1_25]; decide
      have factor_1_27 : (5 : ZMod 5615128221457) ^ 228480152 = 3586749324396 := by
        calc
          (5 : ZMod 5615128221457) ^ 228480152 = (5 : ZMod 5615128221457) ^ (114240076 + 114240076) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 114240076 * (5 : ZMod 5615128221457) ^ 114240076 := by rw [pow_add]
          _ = 3586749324396 := by rw [factor_1_26]; decide
      have factor_1_28 : (5 : ZMod 5615128221457) ^ 456960304 = 262556311394 := by
        calc
          (5 : ZMod 5615128221457) ^ 456960304 = (5 : ZMod 5615128221457) ^ (228480152 + 228480152) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 228480152 * (5 : ZMod 5615128221457) ^ 228480152 := by rw [pow_add]
          _ = 262556311394 := by rw [factor_1_27]; decide
      have factor_1_29 : (5 : ZMod 5615128221457) ^ 913920608 = 3350022498646 := by
        calc
          (5 : ZMod 5615128221457) ^ 913920608 = (5 : ZMod 5615128221457) ^ (456960304 + 456960304) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 456960304 * (5 : ZMod 5615128221457) ^ 456960304 := by rw [pow_add]
          _ = 3350022498646 := by rw [factor_1_28]; decide
      have factor_1_30 : (5 : ZMod 5615128221457) ^ 1827841217 = 564323534555 := by
        calc
          (5 : ZMod 5615128221457) ^ 1827841217 = (5 : ZMod 5615128221457) ^ (913920608 + 913920608 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 913920608 * (5 : ZMod 5615128221457) ^ 913920608) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 564323534555 := by rw [factor_1_29]; decide
      have factor_1_31 : (5 : ZMod 5615128221457) ^ 3655682435 = 4186879587231 := by
        calc
          (5 : ZMod 5615128221457) ^ 3655682435 = (5 : ZMod 5615128221457) ^ (1827841217 + 1827841217 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 1827841217 * (5 : ZMod 5615128221457) ^ 1827841217) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 4186879587231 := by rw [factor_1_30]; decide
      have factor_1_32 : (5 : ZMod 5615128221457) ^ 7311364871 = 2825155090023 := by
        calc
          (5 : ZMod 5615128221457) ^ 7311364871 = (5 : ZMod 5615128221457) ^ (3655682435 + 3655682435 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 3655682435 * (5 : ZMod 5615128221457) ^ 3655682435) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 2825155090023 := by rw [factor_1_31]; decide
      have factor_1_33 : (5 : ZMod 5615128221457) ^ 14622729743 = 4389433078947 := by
        calc
          (5 : ZMod 5615128221457) ^ 14622729743 = (5 : ZMod 5615128221457) ^ (7311364871 + 7311364871 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 7311364871 * (5 : ZMod 5615128221457) ^ 7311364871) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 4389433078947 := by rw [factor_1_32]; decide
      have factor_1_34 : (5 : ZMod 5615128221457) ^ 29245459486 = 1208693909107 := by
        calc
          (5 : ZMod 5615128221457) ^ 29245459486 = (5 : ZMod 5615128221457) ^ (14622729743 + 14622729743) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 14622729743 * (5 : ZMod 5615128221457) ^ 14622729743 := by rw [pow_add]
          _ = 1208693909107 := by rw [factor_1_33]; decide
      have factor_1_35 : (5 : ZMod 5615128221457) ^ 58490918973 = 765277614199 := by
        calc
          (5 : ZMod 5615128221457) ^ 58490918973 = (5 : ZMod 5615128221457) ^ (29245459486 + 29245459486 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 29245459486 * (5 : ZMod 5615128221457) ^ 29245459486) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 765277614199 := by rw [factor_1_34]; decide
      have factor_1_36 : (5 : ZMod 5615128221457) ^ 116981837947 = 3089443975862 := by
        calc
          (5 : ZMod 5615128221457) ^ 116981837947 = (5 : ZMod 5615128221457) ^ (58490918973 + 58490918973 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 58490918973 * (5 : ZMod 5615128221457) ^ 58490918973) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 3089443975862 := by rw [factor_1_35]; decide
      have factor_1_37 : (5 : ZMod 5615128221457) ^ 233963675894 = 5534205916563 := by
        calc
          (5 : ZMod 5615128221457) ^ 233963675894 = (5 : ZMod 5615128221457) ^ (116981837947 + 116981837947) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 116981837947 * (5 : ZMod 5615128221457) ^ 116981837947 := by rw [pow_add]
          _ = 5534205916563 := by rw [factor_1_36]; decide
      have factor_1_38 : (5 : ZMod 5615128221457) ^ 467927351788 = 5015203148912 := by
        calc
          (5 : ZMod 5615128221457) ^ 467927351788 = (5 : ZMod 5615128221457) ^ (233963675894 + 233963675894) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 233963675894 * (5 : ZMod 5615128221457) ^ 233963675894 := by rw [pow_add]
          _ = 5015203148912 := by rw [factor_1_37]; decide
      have factor_1_39 : (5 : ZMod 5615128221457) ^ 935854703576 = 182014349388 := by
        calc
          (5 : ZMod 5615128221457) ^ 935854703576 = (5 : ZMod 5615128221457) ^ (467927351788 + 467927351788) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 467927351788 * (5 : ZMod 5615128221457) ^ 467927351788 := by rw [pow_add]
          _ = 182014349388 := by rw [factor_1_38]; decide
      have factor_1_40 : (5 : ZMod 5615128221457) ^ 1871709407152 = 182014349387 := by
        calc
          (5 : ZMod 5615128221457) ^ 1871709407152 = (5 : ZMod 5615128221457) ^ (935854703576 + 935854703576) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 935854703576 * (5 : ZMod 5615128221457) ^ 935854703576 := by rw [pow_add]
          _ = 182014349387 := by rw [factor_1_39]; decide
      change (5 : ZMod 5615128221457) ^ 1871709407152 ≠ 1
      rw [factor_1_40]
      decide
    ·
      have factor_2_0 : (5 : ZMod 5615128221457) ^ 1 = 5 := by norm_num
      have factor_2_1 : (5 : ZMod 5615128221457) ^ 3 = 125 := by
        calc
          (5 : ZMod 5615128221457) ^ 3 = (5 : ZMod 5615128221457) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 1 * (5 : ZMod 5615128221457) ^ 1) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 125 := by rw [factor_2_0]; decide
      have factor_2_2 : (5 : ZMod 5615128221457) ^ 6 = 15625 := by
        calc
          (5 : ZMod 5615128221457) ^ 6 = (5 : ZMod 5615128221457) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 3 * (5 : ZMod 5615128221457) ^ 3 := by rw [pow_add]
          _ = 15625 := by rw [factor_2_1]; decide
      have factor_2_3 : (5 : ZMod 5615128221457) ^ 12 = 244140625 := by
        calc
          (5 : ZMod 5615128221457) ^ 12 = (5 : ZMod 5615128221457) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 6 * (5 : ZMod 5615128221457) ^ 6 := by rw [pow_add]
          _ = 244140625 := by rw [factor_2_2]; decide
      have factor_2_4 : (5 : ZMod 5615128221457) ^ 25 = 293523122850 := by
        calc
          (5 : ZMod 5615128221457) ^ 25 = (5 : ZMod 5615128221457) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 12 * (5 : ZMod 5615128221457) ^ 12) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 293523122850 := by rw [factor_2_3]; decide
      have factor_2_5 : (5 : ZMod 5615128221457) ^ 50 = 2890923654226 := by
        calc
          (5 : ZMod 5615128221457) ^ 50 = (5 : ZMod 5615128221457) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 25 * (5 : ZMod 5615128221457) ^ 25 := by rw [pow_add]
          _ = 2890923654226 := by rw [factor_2_4]; decide
      have factor_2_6 : (5 : ZMod 5615128221457) ^ 100 = 3946814224062 := by
        calc
          (5 : ZMod 5615128221457) ^ 100 = (5 : ZMod 5615128221457) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 50 * (5 : ZMod 5615128221457) ^ 50 := by rw [pow_add]
          _ = 3946814224062 := by rw [factor_2_5]; decide
      have factor_2_7 : (5 : ZMod 5615128221457) ^ 201 = 5551777046258 := by
        calc
          (5 : ZMod 5615128221457) ^ 201 = (5 : ZMod 5615128221457) ^ (100 + 100 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 100 * (5 : ZMod 5615128221457) ^ 100) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 5551777046258 := by rw [factor_2_6]; decide
      have factor_2_8 : (5 : ZMod 5615128221457) ^ 402 = 4220686728288 := by
        calc
          (5 : ZMod 5615128221457) ^ 402 = (5 : ZMod 5615128221457) ^ (201 + 201) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 201 * (5 : ZMod 5615128221457) ^ 201 := by rw [pow_add]
          _ = 4220686728288 := by rw [factor_2_7]; decide
      have factor_2_9 : (5 : ZMod 5615128221457) ^ 804 = 5425214767508 := by
        calc
          (5 : ZMod 5615128221457) ^ 804 = (5 : ZMod 5615128221457) ^ (402 + 402) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 402 * (5 : ZMod 5615128221457) ^ 402 := by rw [pow_add]
          _ = 5425214767508 := by rw [factor_2_8]; decide
      have factor_2_10 : (5 : ZMod 5615128221457) ^ 1609 = 4134370489846 := by
        calc
          (5 : ZMod 5615128221457) ^ 1609 = (5 : ZMod 5615128221457) ^ (804 + 804 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 804 * (5 : ZMod 5615128221457) ^ 804) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 4134370489846 := by rw [factor_2_9]; decide
      have factor_2_11 : (5 : ZMod 5615128221457) ^ 3218 = 1339935060106 := by
        calc
          (5 : ZMod 5615128221457) ^ 3218 = (5 : ZMod 5615128221457) ^ (1609 + 1609) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 1609 * (5 : ZMod 5615128221457) ^ 1609 := by rw [pow_add]
          _ = 1339935060106 := by rw [factor_2_10]; decide
      have factor_2_12 : (5 : ZMod 5615128221457) ^ 6436 = 713049029424 := by
        calc
          (5 : ZMod 5615128221457) ^ 6436 = (5 : ZMod 5615128221457) ^ (3218 + 3218) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 3218 * (5 : ZMod 5615128221457) ^ 3218 := by rw [pow_add]
          _ = 713049029424 := by rw [factor_2_11]; decide
      have factor_2_13 : (5 : ZMod 5615128221457) ^ 12872 = 3254784819993 := by
        calc
          (5 : ZMod 5615128221457) ^ 12872 = (5 : ZMod 5615128221457) ^ (6436 + 6436) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 6436 * (5 : ZMod 5615128221457) ^ 6436 := by rw [pow_add]
          _ = 3254784819993 := by rw [factor_2_12]; decide
      have factor_2_14 : (5 : ZMod 5615128221457) ^ 25745 = 382706183523 := by
        calc
          (5 : ZMod 5615128221457) ^ 25745 = (5 : ZMod 5615128221457) ^ (12872 + 12872 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 12872 * (5 : ZMod 5615128221457) ^ 12872) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 382706183523 := by rw [factor_2_13]; decide
      have factor_2_15 : (5 : ZMod 5615128221457) ^ 51490 = 3741187361355 := by
        calc
          (5 : ZMod 5615128221457) ^ 51490 = (5 : ZMod 5615128221457) ^ (25745 + 25745) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 25745 * (5 : ZMod 5615128221457) ^ 25745 := by rw [pow_add]
          _ = 3741187361355 := by rw [factor_2_14]; decide
      have factor_2_16 : (5 : ZMod 5615128221457) ^ 102980 = 110158700175 := by
        calc
          (5 : ZMod 5615128221457) ^ 102980 = (5 : ZMod 5615128221457) ^ (51490 + 51490) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 51490 * (5 : ZMod 5615128221457) ^ 51490 := by rw [pow_add]
          _ = 110158700175 := by rw [factor_2_15]; decide
      have factor_2_17 : (5 : ZMod 5615128221457) ^ 205961 = 4437994885617 := by
        calc
          (5 : ZMod 5615128221457) ^ 205961 = (5 : ZMod 5615128221457) ^ (102980 + 102980 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 102980 * (5 : ZMod 5615128221457) ^ 102980) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 4437994885617 := by rw [factor_2_16]; decide
      have factor_2_18 : (5 : ZMod 5615128221457) ^ 411923 = 3932839401256 := by
        calc
          (5 : ZMod 5615128221457) ^ 411923 = (5 : ZMod 5615128221457) ^ (205961 + 205961 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 205961 * (5 : ZMod 5615128221457) ^ 205961) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 3932839401256 := by rw [factor_2_17]; decide
      have factor_2_19 : (5 : ZMod 5615128221457) ^ 823846 = 1375838188385 := by
        calc
          (5 : ZMod 5615128221457) ^ 823846 = (5 : ZMod 5615128221457) ^ (411923 + 411923) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 411923 * (5 : ZMod 5615128221457) ^ 411923 := by rw [pow_add]
          _ = 1375838188385 := by rw [factor_2_18]; decide
      have factor_2_20 : (5 : ZMod 5615128221457) ^ 1647693 = 3618714871345 := by
        calc
          (5 : ZMod 5615128221457) ^ 1647693 = (5 : ZMod 5615128221457) ^ (823846 + 823846 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 823846 * (5 : ZMod 5615128221457) ^ 823846) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 3618714871345 := by rw [factor_2_19]; decide
      have factor_2_21 : (5 : ZMod 5615128221457) ^ 3295386 = 1530170922255 := by
        calc
          (5 : ZMod 5615128221457) ^ 3295386 = (5 : ZMod 5615128221457) ^ (1647693 + 1647693) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 1647693 * (5 : ZMod 5615128221457) ^ 1647693 := by rw [pow_add]
          _ = 1530170922255 := by rw [factor_2_20]; decide
      have factor_2_22 : (5 : ZMod 5615128221457) ^ 6590773 = 256312159020 := by
        calc
          (5 : ZMod 5615128221457) ^ 6590773 = (5 : ZMod 5615128221457) ^ (3295386 + 3295386 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 3295386 * (5 : ZMod 5615128221457) ^ 3295386) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 256312159020 := by rw [factor_2_21]; decide
      have factor_2_23 : (5 : ZMod 5615128221457) ^ 13181547 = 888462716670 := by
        calc
          (5 : ZMod 5615128221457) ^ 13181547 = (5 : ZMod 5615128221457) ^ (6590773 + 6590773 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 6590773 * (5 : ZMod 5615128221457) ^ 6590773) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 888462716670 := by rw [factor_2_22]; decide
      have factor_2_24 : (5 : ZMod 5615128221457) ^ 26363094 = 5365473991143 := by
        calc
          (5 : ZMod 5615128221457) ^ 26363094 = (5 : ZMod 5615128221457) ^ (13181547 + 13181547) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 13181547 * (5 : ZMod 5615128221457) ^ 13181547 := by rw [pow_add]
          _ = 5365473991143 := by rw [factor_2_23]; decide
      have factor_2_25 : (5 : ZMod 5615128221457) ^ 52726188 = 4986084481764 := by
        calc
          (5 : ZMod 5615128221457) ^ 52726188 = (5 : ZMod 5615128221457) ^ (26363094 + 26363094) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 26363094 * (5 : ZMod 5615128221457) ^ 26363094 := by rw [pow_add]
          _ = 4986084481764 := by rw [factor_2_24]; decide
      have factor_2_26 : (5 : ZMod 5615128221457) ^ 105452377 = 5397659908570 := by
        calc
          (5 : ZMod 5615128221457) ^ 105452377 = (5 : ZMod 5615128221457) ^ (52726188 + 52726188 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 52726188 * (5 : ZMod 5615128221457) ^ 52726188) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 5397659908570 := by rw [factor_2_25]; decide
      have factor_2_27 : (5 : ZMod 5615128221457) ^ 210904755 = 2207325988041 := by
        calc
          (5 : ZMod 5615128221457) ^ 210904755 = (5 : ZMod 5615128221457) ^ (105452377 + 105452377 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 105452377 * (5 : ZMod 5615128221457) ^ 105452377) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 2207325988041 := by rw [factor_2_26]; decide
      have factor_2_28 : (5 : ZMod 5615128221457) ^ 421809511 = 5470984300203 := by
        calc
          (5 : ZMod 5615128221457) ^ 421809511 = (5 : ZMod 5615128221457) ^ (210904755 + 210904755 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 210904755 * (5 : ZMod 5615128221457) ^ 210904755) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 5470984300203 := by rw [factor_2_27]; decide
      have factor_2_29 : (5 : ZMod 5615128221457) ^ 843619023 = 4900518430776 := by
        calc
          (5 : ZMod 5615128221457) ^ 843619023 = (5 : ZMod 5615128221457) ^ (421809511 + 421809511 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 421809511 * (5 : ZMod 5615128221457) ^ 421809511) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 4900518430776 := by rw [factor_2_28]; decide
      have factor_2_30 : (5 : ZMod 5615128221457) ^ 1687238047 = 939036826873 := by
        calc
          (5 : ZMod 5615128221457) ^ 1687238047 = (5 : ZMod 5615128221457) ^ (843619023 + 843619023 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 843619023 * (5 : ZMod 5615128221457) ^ 843619023) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 939036826873 := by rw [factor_2_29]; decide
      have factor_2_31 : (5 : ZMod 5615128221457) ^ 3374476094 = 1805186492532 := by
        calc
          (5 : ZMod 5615128221457) ^ 3374476094 = (5 : ZMod 5615128221457) ^ (1687238047 + 1687238047) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 1687238047 * (5 : ZMod 5615128221457) ^ 1687238047 := by rw [pow_add]
          _ = 1805186492532 := by rw [factor_2_30]; decide
      have factor_2_32 : (5 : ZMod 5615128221457) ^ 6748952189 = 433501196800 := by
        calc
          (5 : ZMod 5615128221457) ^ 6748952189 = (5 : ZMod 5615128221457) ^ (3374476094 + 3374476094 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 3374476094 * (5 : ZMod 5615128221457) ^ 3374476094) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 433501196800 := by rw [factor_2_31]; decide
      have factor_2_33 : (5 : ZMod 5615128221457) ^ 13497904378 = 253394041634 := by
        calc
          (5 : ZMod 5615128221457) ^ 13497904378 = (5 : ZMod 5615128221457) ^ (6748952189 + 6748952189) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 6748952189 * (5 : ZMod 5615128221457) ^ 6748952189 := by rw [pow_add]
          _ = 253394041634 := by rw [factor_2_32]; decide
      have factor_2_34 : (5 : ZMod 5615128221457) ^ 26995808757 = 401515391968 := by
        calc
          (5 : ZMod 5615128221457) ^ 26995808757 = (5 : ZMod 5615128221457) ^ (13497904378 + 13497904378 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 13497904378 * (5 : ZMod 5615128221457) ^ 13497904378) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 401515391968 := by rw [factor_2_33]; decide
      have factor_2_35 : (5 : ZMod 5615128221457) ^ 53991617514 = 4636074014653 := by
        calc
          (5 : ZMod 5615128221457) ^ 53991617514 = (5 : ZMod 5615128221457) ^ (26995808757 + 26995808757) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 26995808757 * (5 : ZMod 5615128221457) ^ 26995808757 := by rw [pow_add]
          _ = 4636074014653 := by rw [factor_2_34]; decide
      have factor_2_36 : (5 : ZMod 5615128221457) ^ 107983235028 = 3892380255013 := by
        calc
          (5 : ZMod 5615128221457) ^ 107983235028 = (5 : ZMod 5615128221457) ^ (53991617514 + 53991617514) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 53991617514 * (5 : ZMod 5615128221457) ^ 53991617514 := by rw [pow_add]
          _ = 3892380255013 := by rw [factor_2_35]; decide
      have factor_2_37 : (5 : ZMod 5615128221457) ^ 215966470056 = 3816255933612 := by
        calc
          (5 : ZMod 5615128221457) ^ 215966470056 = (5 : ZMod 5615128221457) ^ (107983235028 + 107983235028) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 107983235028 * (5 : ZMod 5615128221457) ^ 107983235028 := by rw [pow_add]
          _ = 3816255933612 := by rw [factor_2_36]; decide
      have factor_2_38 : (5 : ZMod 5615128221457) ^ 431932940112 = 853423499760 := by
        calc
          (5 : ZMod 5615128221457) ^ 431932940112 = (5 : ZMod 5615128221457) ^ (215966470056 + 215966470056) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 215966470056 * (5 : ZMod 5615128221457) ^ 215966470056 := by rw [pow_add]
          _ = 853423499760 := by rw [factor_2_37]; decide
      change (5 : ZMod 5615128221457) ^ 431932940112 ≠ 1
      rw [factor_2_38]
      decide
    ·
      have factor_3_0 : (5 : ZMod 5615128221457) ^ 1 = 5 := by norm_num
      have factor_3_1 : (5 : ZMod 5615128221457) ^ 2 = 25 := by
        calc
          (5 : ZMod 5615128221457) ^ 2 = (5 : ZMod 5615128221457) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 1 * (5 : ZMod 5615128221457) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_3_0]; decide
      have factor_3_2 : (5 : ZMod 5615128221457) ^ 5 = 3125 := by
        calc
          (5 : ZMod 5615128221457) ^ 5 = (5 : ZMod 5615128221457) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 2 * (5 : ZMod 5615128221457) ^ 2) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 3125 := by rw [factor_3_1]; decide
      have factor_3_3 : (5 : ZMod 5615128221457) ^ 11 = 48828125 := by
        calc
          (5 : ZMod 5615128221457) ^ 11 = (5 : ZMod 5615128221457) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 5 * (5 : ZMod 5615128221457) ^ 5) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 48828125 := by rw [factor_3_2]; decide
      have factor_3_4 : (5 : ZMod 5615128221457) ^ 22 = 3371425117857 := by
        calc
          (5 : ZMod 5615128221457) ^ 22 = (5 : ZMod 5615128221457) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 11 * (5 : ZMod 5615128221457) ^ 11 := by rw [pow_add]
          _ = 3371425117857 := by rw [factor_3_3]; decide
      have factor_3_5 : (5 : ZMod 5615128221457) ^ 44 = 353084597576 := by
        calc
          (5 : ZMod 5615128221457) ^ 44 = (5 : ZMod 5615128221457) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 22 * (5 : ZMod 5615128221457) ^ 22 := by rw [pow_add]
          _ = 353084597576 := by rw [factor_3_4]; decide
      have factor_3_6 : (5 : ZMod 5615128221457) ^ 89 = 3532903951570 := by
        calc
          (5 : ZMod 5615128221457) ^ 89 = (5 : ZMod 5615128221457) ^ (44 + 44 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 44 * (5 : ZMod 5615128221457) ^ 44) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 3532903951570 := by rw [factor_3_5]; decide
      have factor_3_7 : (5 : ZMod 5615128221457) ^ 179 = 2128608023755 := by
        calc
          (5 : ZMod 5615128221457) ^ 179 = (5 : ZMod 5615128221457) ^ (89 + 89 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 89 * (5 : ZMod 5615128221457) ^ 89) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 2128608023755 := by rw [factor_3_6]; decide
      have factor_3_8 : (5 : ZMod 5615128221457) ^ 358 = 4875541849001 := by
        calc
          (5 : ZMod 5615128221457) ^ 358 = (5 : ZMod 5615128221457) ^ (179 + 179) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 179 * (5 : ZMod 5615128221457) ^ 179 := by rw [pow_add]
          _ = 4875541849001 := by rw [factor_3_7]; decide
      have factor_3_9 : (5 : ZMod 5615128221457) ^ 716 = 3866413635042 := by
        calc
          (5 : ZMod 5615128221457) ^ 716 = (5 : ZMod 5615128221457) ^ (358 + 358) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 358 * (5 : ZMod 5615128221457) ^ 358 := by rw [pow_add]
          _ = 3866413635042 := by rw [factor_3_8]; decide
      have factor_3_10 : (5 : ZMod 5615128221457) ^ 1433 = 2275165388439 := by
        calc
          (5 : ZMod 5615128221457) ^ 1433 = (5 : ZMod 5615128221457) ^ (716 + 716 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 716 * (5 : ZMod 5615128221457) ^ 716) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 2275165388439 := by rw [factor_3_9]; decide
      have factor_3_11 : (5 : ZMod 5615128221457) ^ 2866 = 560828009230 := by
        calc
          (5 : ZMod 5615128221457) ^ 2866 = (5 : ZMod 5615128221457) ^ (1433 + 1433) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 1433 * (5 : ZMod 5615128221457) ^ 1433 := by rw [pow_add]
          _ = 560828009230 := by rw [factor_3_10]; decide
      have factor_3_12 : (5 : ZMod 5615128221457) ^ 5733 = 635305795293 := by
        calc
          (5 : ZMod 5615128221457) ^ 5733 = (5 : ZMod 5615128221457) ^ (2866 + 2866 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 2866 * (5 : ZMod 5615128221457) ^ 2866) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 635305795293 := by rw [factor_3_11]; decide
      have factor_3_13 : (5 : ZMod 5615128221457) ^ 11466 = 907769437221 := by
        calc
          (5 : ZMod 5615128221457) ^ 11466 = (5 : ZMod 5615128221457) ^ (5733 + 5733) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 5733 * (5 : ZMod 5615128221457) ^ 5733 := by rw [pow_add]
          _ = 907769437221 := by rw [factor_3_12]; decide
      have factor_3_14 : (5 : ZMod 5615128221457) ^ 22933 = 4306219808885 := by
        calc
          (5 : ZMod 5615128221457) ^ 22933 = (5 : ZMod 5615128221457) ^ (11466 + 11466 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 11466 * (5 : ZMod 5615128221457) ^ 11466) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 4306219808885 := by rw [factor_3_13]; decide
      have factor_3_15 : (5 : ZMod 5615128221457) ^ 45867 = 4780671059953 := by
        calc
          (5 : ZMod 5615128221457) ^ 45867 = (5 : ZMod 5615128221457) ^ (22933 + 22933 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 22933 * (5 : ZMod 5615128221457) ^ 22933) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 4780671059953 := by rw [factor_3_14]; decide
      have factor_3_16 : (5 : ZMod 5615128221457) ^ 91734 = 2147553309537 := by
        calc
          (5 : ZMod 5615128221457) ^ 91734 = (5 : ZMod 5615128221457) ^ (45867 + 45867) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 45867 * (5 : ZMod 5615128221457) ^ 45867 := by rw [pow_add]
          _ = 2147553309537 := by rw [factor_3_15]; decide
      have factor_3_17 : (5 : ZMod 5615128221457) ^ 183469 = 3762310172940 := by
        calc
          (5 : ZMod 5615128221457) ^ 183469 = (5 : ZMod 5615128221457) ^ (91734 + 91734 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 91734 * (5 : ZMod 5615128221457) ^ 91734) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 3762310172940 := by rw [factor_3_16]; decide
      have factor_3_18 : (5 : ZMod 5615128221457) ^ 366938 = 4628259618105 := by
        calc
          (5 : ZMod 5615128221457) ^ 366938 = (5 : ZMod 5615128221457) ^ (183469 + 183469) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 183469 * (5 : ZMod 5615128221457) ^ 183469 := by rw [pow_add]
          _ = 4628259618105 := by rw [factor_3_17]; decide
      have factor_3_19 : (5 : ZMod 5615128221457) ^ 733876 = 2911626722139 := by
        calc
          (5 : ZMod 5615128221457) ^ 733876 = (5 : ZMod 5615128221457) ^ (366938 + 366938) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 366938 * (5 : ZMod 5615128221457) ^ 366938 := by rw [pow_add]
          _ = 2911626722139 := by rw [factor_3_18]; decide
      have factor_3_20 : (5 : ZMod 5615128221457) ^ 1467752 = 1302487073851 := by
        calc
          (5 : ZMod 5615128221457) ^ 1467752 = (5 : ZMod 5615128221457) ^ (733876 + 733876) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 733876 * (5 : ZMod 5615128221457) ^ 733876 := by rw [pow_add]
          _ = 1302487073851 := by rw [factor_3_19]; decide
      have factor_3_21 : (5 : ZMod 5615128221457) ^ 2935505 = 2917335307166 := by
        calc
          (5 : ZMod 5615128221457) ^ 2935505 = (5 : ZMod 5615128221457) ^ (1467752 + 1467752 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 1467752 * (5 : ZMod 5615128221457) ^ 1467752) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 2917335307166 := by rw [factor_3_20]; decide
      have factor_3_22 : (5 : ZMod 5615128221457) ^ 5871010 = 552776548862 := by
        calc
          (5 : ZMod 5615128221457) ^ 5871010 = (5 : ZMod 5615128221457) ^ (2935505 + 2935505) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 2935505 * (5 : ZMod 5615128221457) ^ 2935505 := by rw [pow_add]
          _ = 552776548862 := by rw [factor_3_21]; decide
      have factor_3_23 : (5 : ZMod 5615128221457) ^ 11742020 = 1914306152137 := by
        calc
          (5 : ZMod 5615128221457) ^ 11742020 = (5 : ZMod 5615128221457) ^ (5871010 + 5871010) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 5871010 * (5 : ZMod 5615128221457) ^ 5871010 := by rw [pow_add]
          _ = 1914306152137 := by rw [factor_3_22]; decide
      have factor_3_24 : (5 : ZMod 5615128221457) ^ 23484041 = 130586808527 := by
        calc
          (5 : ZMod 5615128221457) ^ 23484041 = (5 : ZMod 5615128221457) ^ (11742020 + 11742020 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 11742020 * (5 : ZMod 5615128221457) ^ 11742020) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 130586808527 := by rw [factor_3_23]; decide
      have factor_3_25 : (5 : ZMod 5615128221457) ^ 46968082 = 2361068030567 := by
        calc
          (5 : ZMod 5615128221457) ^ 46968082 = (5 : ZMod 5615128221457) ^ (23484041 + 23484041) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 23484041 * (5 : ZMod 5615128221457) ^ 23484041 := by rw [pow_add]
          _ = 2361068030567 := by rw [factor_3_24]; decide
      have factor_3_26 : (5 : ZMod 5615128221457) ^ 93936165 = 2787684191302 := by
        calc
          (5 : ZMod 5615128221457) ^ 93936165 = (5 : ZMod 5615128221457) ^ (46968082 + 46968082 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 46968082 * (5 : ZMod 5615128221457) ^ 46968082) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 2787684191302 := by rw [factor_3_25]; decide
      have factor_3_27 : (5 : ZMod 5615128221457) ^ 187872330 = 2617486001465 := by
        calc
          (5 : ZMod 5615128221457) ^ 187872330 = (5 : ZMod 5615128221457) ^ (93936165 + 93936165) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 93936165 * (5 : ZMod 5615128221457) ^ 93936165 := by rw [pow_add]
          _ = 2617486001465 := by rw [factor_3_26]; decide
      have factor_3_28 : (5 : ZMod 5615128221457) ^ 375744661 = 291615469902 := by
        calc
          (5 : ZMod 5615128221457) ^ 375744661 = (5 : ZMod 5615128221457) ^ (187872330 + 187872330 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 187872330 * (5 : ZMod 5615128221457) ^ 187872330) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 291615469902 := by rw [factor_3_27]; decide
      have factor_3_29 : (5 : ZMod 5615128221457) ^ 751489323 = 1086174096004 := by
        calc
          (5 : ZMod 5615128221457) ^ 751489323 = (5 : ZMod 5615128221457) ^ (375744661 + 375744661 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 375744661 * (5 : ZMod 5615128221457) ^ 375744661) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 1086174096004 := by rw [factor_3_28]; decide
      have factor_3_30 : (5 : ZMod 5615128221457) ^ 1502978646 = 2123423442062 := by
        calc
          (5 : ZMod 5615128221457) ^ 1502978646 = (5 : ZMod 5615128221457) ^ (751489323 + 751489323) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 751489323 * (5 : ZMod 5615128221457) ^ 751489323 := by rw [pow_add]
          _ = 2123423442062 := by rw [factor_3_29]; decide
      have factor_3_31 : (5 : ZMod 5615128221457) ^ 3005957292 = 2074315959852 := by
        calc
          (5 : ZMod 5615128221457) ^ 3005957292 = (5 : ZMod 5615128221457) ^ (1502978646 + 1502978646) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 1502978646 * (5 : ZMod 5615128221457) ^ 1502978646 := by rw [pow_add]
          _ = 2074315959852 := by rw [factor_3_30]; decide
      have factor_3_32 : (5 : ZMod 5615128221457) ^ 6011914584 = 4621633537657 := by
        calc
          (5 : ZMod 5615128221457) ^ 6011914584 = (5 : ZMod 5615128221457) ^ (3005957292 + 3005957292) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 3005957292 * (5 : ZMod 5615128221457) ^ 3005957292 := by rw [pow_add]
          _ = 4621633537657 := by rw [factor_3_31]; decide
      have factor_3_33 : (5 : ZMod 5615128221457) ^ 12023829168 = 3481177492020 := by
        calc
          (5 : ZMod 5615128221457) ^ 12023829168 = (5 : ZMod 5615128221457) ^ (6011914584 + 6011914584) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 6011914584 * (5 : ZMod 5615128221457) ^ 6011914584 := by rw [pow_add]
          _ = 3481177492020 := by rw [factor_3_32]; decide
      change (5 : ZMod 5615128221457) ^ 12023829168 ≠ 1
      rw [factor_3_33]
      decide
    ·
      have factor_4_0 : (5 : ZMod 5615128221457) ^ 1 = 5 := by norm_num
      have factor_4_1 : (5 : ZMod 5615128221457) ^ 2 = 25 := by
        calc
          (5 : ZMod 5615128221457) ^ 2 = (5 : ZMod 5615128221457) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 1 * (5 : ZMod 5615128221457) ^ 1 := by rw [pow_add]
          _ = 25 := by rw [factor_4_0]; decide
      have factor_4_2 : (5 : ZMod 5615128221457) ^ 4 = 625 := by
        calc
          (5 : ZMod 5615128221457) ^ 4 = (5 : ZMod 5615128221457) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 2 * (5 : ZMod 5615128221457) ^ 2 := by rw [pow_add]
          _ = 625 := by rw [factor_4_1]; decide
      have factor_4_3 : (5 : ZMod 5615128221457) ^ 8 = 390625 := by
        calc
          (5 : ZMod 5615128221457) ^ 8 = (5 : ZMod 5615128221457) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 4 * (5 : ZMod 5615128221457) ^ 4 := by rw [pow_add]
          _ = 390625 := by rw [factor_4_2]; decide
      have factor_4_4 : (5 : ZMod 5615128221457) ^ 17 = 762939453125 := by
        calc
          (5 : ZMod 5615128221457) ^ 17 = (5 : ZMod 5615128221457) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 8 * (5 : ZMod 5615128221457) ^ 8) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 762939453125 := by rw [factor_4_3]; decide
      have factor_4_5 : (5 : ZMod 5615128221457) ^ 35 = 3631579776062 := by
        calc
          (5 : ZMod 5615128221457) ^ 35 = (5 : ZMod 5615128221457) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 17 * (5 : ZMod 5615128221457) ^ 17) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 3631579776062 := by rw [factor_4_4]; decide
      have factor_4_6 : (5 : ZMod 5615128221457) ^ 71 = 2269652025047 := by
        calc
          (5 : ZMod 5615128221457) ^ 71 = (5 : ZMod 5615128221457) ^ (35 + 35 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 35 * (5 : ZMod 5615128221457) ^ 35) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 2269652025047 := by rw [factor_4_5]; decide
      have factor_4_7 : (5 : ZMod 5615128221457) ^ 142 = 3517114459892 := by
        calc
          (5 : ZMod 5615128221457) ^ 142 = (5 : ZMod 5615128221457) ^ (71 + 71) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 71 * (5 : ZMod 5615128221457) ^ 71 := by rw [pow_add]
          _ = 3517114459892 := by rw [factor_4_6]; decide
      have factor_4_8 : (5 : ZMod 5615128221457) ^ 284 = 4378031822873 := by
        calc
          (5 : ZMod 5615128221457) ^ 284 = (5 : ZMod 5615128221457) ^ (142 + 142) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 142 * (5 : ZMod 5615128221457) ^ 142 := by rw [pow_add]
          _ = 4378031822873 := by rw [factor_4_7]; decide
      have factor_4_9 : (5 : ZMod 5615128221457) ^ 569 = 460291143035 := by
        calc
          (5 : ZMod 5615128221457) ^ 569 = (5 : ZMod 5615128221457) ^ (284 + 284 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 284 * (5 : ZMod 5615128221457) ^ 284) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 460291143035 := by rw [factor_4_8]; decide
      have factor_4_10 : (5 : ZMod 5615128221457) ^ 1138 = 936845764835 := by
        calc
          (5 : ZMod 5615128221457) ^ 1138 = (5 : ZMod 5615128221457) ^ (569 + 569) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 569 * (5 : ZMod 5615128221457) ^ 569 := by rw [pow_add]
          _ = 936845764835 := by rw [factor_4_9]; decide
      have factor_4_11 : (5 : ZMod 5615128221457) ^ 2276 = 290868454654 := by
        calc
          (5 : ZMod 5615128221457) ^ 2276 = (5 : ZMod 5615128221457) ^ (1138 + 1138) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 1138 * (5 : ZMod 5615128221457) ^ 1138 := by rw [pow_add]
          _ = 290868454654 := by rw [factor_4_10]; decide
      have factor_4_12 : (5 : ZMod 5615128221457) ^ 4553 = 3852071529878 := by
        calc
          (5 : ZMod 5615128221457) ^ 4553 = (5 : ZMod 5615128221457) ^ (2276 + 2276 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 2276 * (5 : ZMod 5615128221457) ^ 2276) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 3852071529878 := by rw [factor_4_11]; decide
      have factor_4_13 : (5 : ZMod 5615128221457) ^ 9106 = 440496466405 := by
        calc
          (5 : ZMod 5615128221457) ^ 9106 = (5 : ZMod 5615128221457) ^ (4553 + 4553) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 4553 * (5 : ZMod 5615128221457) ^ 4553 := by rw [pow_add]
          _ = 440496466405 := by rw [factor_4_12]; decide
      have factor_4_14 : (5 : ZMod 5615128221457) ^ 18213 = 1097176798435 := by
        calc
          (5 : ZMod 5615128221457) ^ 18213 = (5 : ZMod 5615128221457) ^ (9106 + 9106 + 1) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = ((5 : ZMod 5615128221457) ^ 9106 * (5 : ZMod 5615128221457) ^ 9106) * (5 : ZMod 5615128221457) := by rw [pow_succ, pow_add]
          _ = 1097176798435 := by rw [factor_4_13]; decide
      have factor_4_15 : (5 : ZMod 5615128221457) ^ 36426 = 2627032779775 := by
        calc
          (5 : ZMod 5615128221457) ^ 36426 = (5 : ZMod 5615128221457) ^ (18213 + 18213) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 18213 * (5 : ZMod 5615128221457) ^ 18213 := by rw [pow_add]
          _ = 2627032779775 := by rw [factor_4_14]; decide
      have factor_4_16 : (5 : ZMod 5615128221457) ^ 72852 = 1999015906500 := by
        calc
          (5 : ZMod 5615128221457) ^ 72852 = (5 : ZMod 5615128221457) ^ (36426 + 36426) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 36426 * (5 : ZMod 5615128221457) ^ 36426 := by rw [pow_add]
          _ = 1999015906500 := by rw [factor_4_15]; decide
      have factor_4_17 : (5 : ZMod 5615128221457) ^ 145704 = 2771270474588 := by
        calc
          (5 : ZMod 5615128221457) ^ 145704 = (5 : ZMod 5615128221457) ^ (72852 + 72852) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 72852 * (5 : ZMod 5615128221457) ^ 72852 := by rw [pow_add]
          _ = 2771270474588 := by rw [factor_4_16]; decide
      have factor_4_18 : (5 : ZMod 5615128221457) ^ 291408 = 2132418433628 := by
        calc
          (5 : ZMod 5615128221457) ^ 291408 = (5 : ZMod 5615128221457) ^ (145704 + 145704) :=
            congrArg (fun n : ℕ => (5 : ZMod 5615128221457) ^ n) (by norm_num)
          _ = (5 : ZMod 5615128221457) ^ 145704 * (5 : ZMod 5615128221457) ^ 145704 := by rw [pow_add]
          _ = 2132418433628 := by rw [factor_4_17]; decide
      change (5 : ZMod 5615128221457) ^ 291408 ≠ 1
      rw [factor_4_18]
      decide

#print axioms prime_lucas_5615128221457

end TotientTailPeriodKiller
end Erdos249257
