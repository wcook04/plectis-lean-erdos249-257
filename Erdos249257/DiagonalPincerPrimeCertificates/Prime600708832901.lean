import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_600708832901 : Nat.Prime 600708832901 := by
  apply lucas_primality 600708832901 (3 : ZMod 600708832901)
  ·
      have fermat_0 : (3 : ZMod 600708832901) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 600708832901) ^ 2 = 9 := by
        calc
          (3 : ZMod 600708832901) ^ 2 = (3 : ZMod 600708832901) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 1 * (3 : ZMod 600708832901) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 600708832901) ^ 4 = 81 := by
        calc
          (3 : ZMod 600708832901) ^ 4 = (3 : ZMod 600708832901) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 2 * (3 : ZMod 600708832901) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 600708832901) ^ 8 = 6561 := by
        calc
          (3 : ZMod 600708832901) ^ 8 = (3 : ZMod 600708832901) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 4 * (3 : ZMod 600708832901) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 600708832901) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 600708832901) ^ 17 = (3 : ZMod 600708832901) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 8 * (3 : ZMod 600708832901) ^ 8) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 600708832901) ^ 34 = 303080669007 := by
        calc
          (3 : ZMod 600708832901) ^ 34 = (3 : ZMod 600708832901) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 17 * (3 : ZMod 600708832901) ^ 17 := by rw [pow_add]
          _ = 303080669007 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 600708832901) ^ 69 = 2569426288 := by
        calc
          (3 : ZMod 600708832901) ^ 69 = (3 : ZMod 600708832901) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 34 * (3 : ZMod 600708832901) ^ 34) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 2569426288 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 600708832901) ^ 139 = 557039921527 := by
        calc
          (3 : ZMod 600708832901) ^ 139 = (3 : ZMod 600708832901) ^ (69 + 69 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 69 * (3 : ZMod 600708832901) ^ 69) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 557039921527 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 600708832901) ^ 279 = 186629057915 := by
        calc
          (3 : ZMod 600708832901) ^ 279 = (3 : ZMod 600708832901) ^ (139 + 139 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 139 * (3 : ZMod 600708832901) ^ 139) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 186629057915 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 600708832901) ^ 559 = 116152512854 := by
        calc
          (3 : ZMod 600708832901) ^ 559 = (3 : ZMod 600708832901) ^ (279 + 279 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 279 * (3 : ZMod 600708832901) ^ 279) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 116152512854 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 600708832901) ^ 1118 = 230128692513 := by
        calc
          (3 : ZMod 600708832901) ^ 1118 = (3 : ZMod 600708832901) ^ (559 + 559) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 559 * (3 : ZMod 600708832901) ^ 559 := by rw [pow_add]
          _ = 230128692513 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 600708832901) ^ 2237 = 577113681836 := by
        calc
          (3 : ZMod 600708832901) ^ 2237 = (3 : ZMod 600708832901) ^ (1118 + 1118 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 1118 * (3 : ZMod 600708832901) ^ 1118) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 577113681836 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 600708832901) ^ 4475 = 248398495704 := by
        calc
          (3 : ZMod 600708832901) ^ 4475 = (3 : ZMod 600708832901) ^ (2237 + 2237 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 2237 * (3 : ZMod 600708832901) ^ 2237) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 248398495704 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 600708832901) ^ 8951 = 17874605794 := by
        calc
          (3 : ZMod 600708832901) ^ 8951 = (3 : ZMod 600708832901) ^ (4475 + 4475 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 4475 * (3 : ZMod 600708832901) ^ 4475) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 17874605794 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 600708832901) ^ 17902 = 556618817533 := by
        calc
          (3 : ZMod 600708832901) ^ 17902 = (3 : ZMod 600708832901) ^ (8951 + 8951) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 8951 * (3 : ZMod 600708832901) ^ 8951 := by rw [pow_add]
          _ = 556618817533 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 600708832901) ^ 35805 = 571356878924 := by
        calc
          (3 : ZMod 600708832901) ^ 35805 = (3 : ZMod 600708832901) ^ (17902 + 17902 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 17902 * (3 : ZMod 600708832901) ^ 17902) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 571356878924 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 600708832901) ^ 71610 = 20276177440 := by
        calc
          (3 : ZMod 600708832901) ^ 71610 = (3 : ZMod 600708832901) ^ (35805 + 35805) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 35805 * (3 : ZMod 600708832901) ^ 35805 := by rw [pow_add]
          _ = 20276177440 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 600708832901) ^ 143220 = 410712624520 := by
        calc
          (3 : ZMod 600708832901) ^ 143220 = (3 : ZMod 600708832901) ^ (71610 + 71610) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 71610 * (3 : ZMod 600708832901) ^ 71610 := by rw [pow_add]
          _ = 410712624520 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 600708832901) ^ 286440 = 339648671410 := by
        calc
          (3 : ZMod 600708832901) ^ 286440 = (3 : ZMod 600708832901) ^ (143220 + 143220) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 143220 * (3 : ZMod 600708832901) ^ 143220 := by rw [pow_add]
          _ = 339648671410 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 600708832901) ^ 572880 = 327002483555 := by
        calc
          (3 : ZMod 600708832901) ^ 572880 = (3 : ZMod 600708832901) ^ (286440 + 286440) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 286440 * (3 : ZMod 600708832901) ^ 286440 := by rw [pow_add]
          _ = 327002483555 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 600708832901) ^ 1145761 = 97103520068 := by
        calc
          (3 : ZMod 600708832901) ^ 1145761 = (3 : ZMod 600708832901) ^ (572880 + 572880 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 572880 * (3 : ZMod 600708832901) ^ 572880) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 97103520068 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 600708832901) ^ 2291522 = 17868742800 := by
        calc
          (3 : ZMod 600708832901) ^ 2291522 = (3 : ZMod 600708832901) ^ (1145761 + 1145761) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 1145761 * (3 : ZMod 600708832901) ^ 1145761 := by rw [pow_add]
          _ = 17868742800 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 600708832901) ^ 4583044 = 201009297056 := by
        calc
          (3 : ZMod 600708832901) ^ 4583044 = (3 : ZMod 600708832901) ^ (2291522 + 2291522) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 2291522 * (3 : ZMod 600708832901) ^ 2291522 := by rw [pow_add]
          _ = 201009297056 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 600708832901) ^ 9166089 = 534097324361 := by
        calc
          (3 : ZMod 600708832901) ^ 9166089 = (3 : ZMod 600708832901) ^ (4583044 + 4583044 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 4583044 * (3 : ZMod 600708832901) ^ 4583044) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 534097324361 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 600708832901) ^ 18332178 = 566287682324 := by
        calc
          (3 : ZMod 600708832901) ^ 18332178 = (3 : ZMod 600708832901) ^ (9166089 + 9166089) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 9166089 * (3 : ZMod 600708832901) ^ 9166089 := by rw [pow_add]
          _ = 566287682324 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 600708832901) ^ 36664357 = 524139695830 := by
        calc
          (3 : ZMod 600708832901) ^ 36664357 = (3 : ZMod 600708832901) ^ (18332178 + 18332178 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 18332178 * (3 : ZMod 600708832901) ^ 18332178) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 524139695830 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 600708832901) ^ 73328714 = 123103788202 := by
        calc
          (3 : ZMod 600708832901) ^ 73328714 = (3 : ZMod 600708832901) ^ (36664357 + 36664357) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 36664357 * (3 : ZMod 600708832901) ^ 36664357 := by rw [pow_add]
          _ = 123103788202 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 600708832901) ^ 146657429 = 541792405422 := by
        calc
          (3 : ZMod 600708832901) ^ 146657429 = (3 : ZMod 600708832901) ^ (73328714 + 73328714 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 73328714 * (3 : ZMod 600708832901) ^ 73328714) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 541792405422 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 600708832901) ^ 293314859 = 105415212645 := by
        calc
          (3 : ZMod 600708832901) ^ 293314859 = (3 : ZMod 600708832901) ^ (146657429 + 146657429 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 146657429 * (3 : ZMod 600708832901) ^ 146657429) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 105415212645 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 600708832901) ^ 586629719 = 38061394930 := by
        calc
          (3 : ZMod 600708832901) ^ 586629719 = (3 : ZMod 600708832901) ^ (293314859 + 293314859 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 293314859 * (3 : ZMod 600708832901) ^ 293314859) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 38061394930 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 600708832901) ^ 1173259439 = 497146763890 := by
        calc
          (3 : ZMod 600708832901) ^ 1173259439 = (3 : ZMod 600708832901) ^ (586629719 + 586629719 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 586629719 * (3 : ZMod 600708832901) ^ 586629719) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 497146763890 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 600708832901) ^ 2346518878 = 395847914788 := by
        calc
          (3 : ZMod 600708832901) ^ 2346518878 = (3 : ZMod 600708832901) ^ (1173259439 + 1173259439) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 1173259439 * (3 : ZMod 600708832901) ^ 1173259439 := by rw [pow_add]
          _ = 395847914788 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 600708832901) ^ 4693037757 = 425481098902 := by
        calc
          (3 : ZMod 600708832901) ^ 4693037757 = (3 : ZMod 600708832901) ^ (2346518878 + 2346518878 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 2346518878 * (3 : ZMod 600708832901) ^ 2346518878) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 425481098902 := by rw [fermat_31]; decide
      have fermat_33 : (3 : ZMod 600708832901) ^ 9386075514 = 500447777890 := by
        calc
          (3 : ZMod 600708832901) ^ 9386075514 = (3 : ZMod 600708832901) ^ (4693037757 + 4693037757) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 4693037757 * (3 : ZMod 600708832901) ^ 4693037757 := by rw [pow_add]
          _ = 500447777890 := by rw [fermat_32]; decide
      have fermat_34 : (3 : ZMod 600708832901) ^ 18772151028 = 254095835119 := by
        calc
          (3 : ZMod 600708832901) ^ 18772151028 = (3 : ZMod 600708832901) ^ (9386075514 + 9386075514) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 9386075514 * (3 : ZMod 600708832901) ^ 9386075514 := by rw [pow_add]
          _ = 254095835119 := by rw [fermat_33]; decide
      have fermat_35 : (3 : ZMod 600708832901) ^ 37544302056 = 109406900886 := by
        calc
          (3 : ZMod 600708832901) ^ 37544302056 = (3 : ZMod 600708832901) ^ (18772151028 + 18772151028) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 18772151028 * (3 : ZMod 600708832901) ^ 18772151028 := by rw [pow_add]
          _ = 109406900886 := by rw [fermat_34]; decide
      have fermat_36 : (3 : ZMod 600708832901) ^ 75088604112 = 501777653455 := by
        calc
          (3 : ZMod 600708832901) ^ 75088604112 = (3 : ZMod 600708832901) ^ (37544302056 + 37544302056) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 37544302056 * (3 : ZMod 600708832901) ^ 37544302056 := by rw [pow_add]
          _ = 501777653455 := by rw [fermat_35]; decide
      have fermat_37 : (3 : ZMod 600708832901) ^ 150177208225 = 9998759460 := by
        calc
          (3 : ZMod 600708832901) ^ 150177208225 = (3 : ZMod 600708832901) ^ (75088604112 + 75088604112 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 75088604112 * (3 : ZMod 600708832901) ^ 75088604112) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 9998759460 := by rw [fermat_36]; decide
      have fermat_38 : (3 : ZMod 600708832901) ^ 300354416450 = 600708832900 := by
        calc
          (3 : ZMod 600708832901) ^ 300354416450 = (3 : ZMod 600708832901) ^ (150177208225 + 150177208225) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 150177208225 * (3 : ZMod 600708832901) ^ 150177208225 := by rw [pow_add]
          _ = 600708832900 := by rw [fermat_37]; decide
      have fermat_39 : (3 : ZMod 600708832901) ^ 600708832900 = 1 := by
        calc
          (3 : ZMod 600708832901) ^ 600708832900 = (3 : ZMod 600708832901) ^ (300354416450 + 300354416450) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 300354416450 * (3 : ZMod 600708832901) ^ 300354416450 := by rw [pow_add]
          _ = 1 := by rw [fermat_38]; decide
      simpa using fermat_39
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 2), (11, 1), (17, 1), (32123467, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 2), (11, 1), (17, 1), (32123467, 1)] : List FactorBlock).map factorBlockValue).prod = 600708832901 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 600708832901) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 600708832901) ^ 2 = 9 := by
        calc
          (3 : ZMod 600708832901) ^ 2 = (3 : ZMod 600708832901) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 1 * (3 : ZMod 600708832901) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 600708832901) ^ 4 = 81 := by
        calc
          (3 : ZMod 600708832901) ^ 4 = (3 : ZMod 600708832901) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 2 * (3 : ZMod 600708832901) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 600708832901) ^ 8 = 6561 := by
        calc
          (3 : ZMod 600708832901) ^ 8 = (3 : ZMod 600708832901) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 4 * (3 : ZMod 600708832901) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 600708832901) ^ 17 = 129140163 := by
        calc
          (3 : ZMod 600708832901) ^ 17 = (3 : ZMod 600708832901) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 8 * (3 : ZMod 600708832901) ^ 8) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 129140163 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 600708832901) ^ 34 = 303080669007 := by
        calc
          (3 : ZMod 600708832901) ^ 34 = (3 : ZMod 600708832901) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 17 * (3 : ZMod 600708832901) ^ 17 := by rw [pow_add]
          _ = 303080669007 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 600708832901) ^ 69 = 2569426288 := by
        calc
          (3 : ZMod 600708832901) ^ 69 = (3 : ZMod 600708832901) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 34 * (3 : ZMod 600708832901) ^ 34) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 2569426288 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 600708832901) ^ 139 = 557039921527 := by
        calc
          (3 : ZMod 600708832901) ^ 139 = (3 : ZMod 600708832901) ^ (69 + 69 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 69 * (3 : ZMod 600708832901) ^ 69) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 557039921527 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 600708832901) ^ 279 = 186629057915 := by
        calc
          (3 : ZMod 600708832901) ^ 279 = (3 : ZMod 600708832901) ^ (139 + 139 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 139 * (3 : ZMod 600708832901) ^ 139) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 186629057915 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 600708832901) ^ 559 = 116152512854 := by
        calc
          (3 : ZMod 600708832901) ^ 559 = (3 : ZMod 600708832901) ^ (279 + 279 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 279 * (3 : ZMod 600708832901) ^ 279) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 116152512854 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 600708832901) ^ 1118 = 230128692513 := by
        calc
          (3 : ZMod 600708832901) ^ 1118 = (3 : ZMod 600708832901) ^ (559 + 559) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 559 * (3 : ZMod 600708832901) ^ 559 := by rw [pow_add]
          _ = 230128692513 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 600708832901) ^ 2237 = 577113681836 := by
        calc
          (3 : ZMod 600708832901) ^ 2237 = (3 : ZMod 600708832901) ^ (1118 + 1118 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 1118 * (3 : ZMod 600708832901) ^ 1118) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 577113681836 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 600708832901) ^ 4475 = 248398495704 := by
        calc
          (3 : ZMod 600708832901) ^ 4475 = (3 : ZMod 600708832901) ^ (2237 + 2237 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 2237 * (3 : ZMod 600708832901) ^ 2237) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 248398495704 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 600708832901) ^ 8951 = 17874605794 := by
        calc
          (3 : ZMod 600708832901) ^ 8951 = (3 : ZMod 600708832901) ^ (4475 + 4475 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 4475 * (3 : ZMod 600708832901) ^ 4475) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 17874605794 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 600708832901) ^ 17902 = 556618817533 := by
        calc
          (3 : ZMod 600708832901) ^ 17902 = (3 : ZMod 600708832901) ^ (8951 + 8951) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 8951 * (3 : ZMod 600708832901) ^ 8951 := by rw [pow_add]
          _ = 556618817533 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 600708832901) ^ 35805 = 571356878924 := by
        calc
          (3 : ZMod 600708832901) ^ 35805 = (3 : ZMod 600708832901) ^ (17902 + 17902 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 17902 * (3 : ZMod 600708832901) ^ 17902) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 571356878924 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 600708832901) ^ 71610 = 20276177440 := by
        calc
          (3 : ZMod 600708832901) ^ 71610 = (3 : ZMod 600708832901) ^ (35805 + 35805) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 35805 * (3 : ZMod 600708832901) ^ 35805 := by rw [pow_add]
          _ = 20276177440 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 600708832901) ^ 143220 = 410712624520 := by
        calc
          (3 : ZMod 600708832901) ^ 143220 = (3 : ZMod 600708832901) ^ (71610 + 71610) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 71610 * (3 : ZMod 600708832901) ^ 71610 := by rw [pow_add]
          _ = 410712624520 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 600708832901) ^ 286440 = 339648671410 := by
        calc
          (3 : ZMod 600708832901) ^ 286440 = (3 : ZMod 600708832901) ^ (143220 + 143220) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 143220 * (3 : ZMod 600708832901) ^ 143220 := by rw [pow_add]
          _ = 339648671410 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 600708832901) ^ 572880 = 327002483555 := by
        calc
          (3 : ZMod 600708832901) ^ 572880 = (3 : ZMod 600708832901) ^ (286440 + 286440) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 286440 * (3 : ZMod 600708832901) ^ 286440 := by rw [pow_add]
          _ = 327002483555 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 600708832901) ^ 1145761 = 97103520068 := by
        calc
          (3 : ZMod 600708832901) ^ 1145761 = (3 : ZMod 600708832901) ^ (572880 + 572880 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 572880 * (3 : ZMod 600708832901) ^ 572880) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 97103520068 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 600708832901) ^ 2291522 = 17868742800 := by
        calc
          (3 : ZMod 600708832901) ^ 2291522 = (3 : ZMod 600708832901) ^ (1145761 + 1145761) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 1145761 * (3 : ZMod 600708832901) ^ 1145761 := by rw [pow_add]
          _ = 17868742800 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 600708832901) ^ 4583044 = 201009297056 := by
        calc
          (3 : ZMod 600708832901) ^ 4583044 = (3 : ZMod 600708832901) ^ (2291522 + 2291522) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 2291522 * (3 : ZMod 600708832901) ^ 2291522 := by rw [pow_add]
          _ = 201009297056 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 600708832901) ^ 9166089 = 534097324361 := by
        calc
          (3 : ZMod 600708832901) ^ 9166089 = (3 : ZMod 600708832901) ^ (4583044 + 4583044 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 4583044 * (3 : ZMod 600708832901) ^ 4583044) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 534097324361 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 600708832901) ^ 18332178 = 566287682324 := by
        calc
          (3 : ZMod 600708832901) ^ 18332178 = (3 : ZMod 600708832901) ^ (9166089 + 9166089) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 9166089 * (3 : ZMod 600708832901) ^ 9166089 := by rw [pow_add]
          _ = 566287682324 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 600708832901) ^ 36664357 = 524139695830 := by
        calc
          (3 : ZMod 600708832901) ^ 36664357 = (3 : ZMod 600708832901) ^ (18332178 + 18332178 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 18332178 * (3 : ZMod 600708832901) ^ 18332178) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 524139695830 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 600708832901) ^ 73328714 = 123103788202 := by
        calc
          (3 : ZMod 600708832901) ^ 73328714 = (3 : ZMod 600708832901) ^ (36664357 + 36664357) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 36664357 * (3 : ZMod 600708832901) ^ 36664357 := by rw [pow_add]
          _ = 123103788202 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 600708832901) ^ 146657429 = 541792405422 := by
        calc
          (3 : ZMod 600708832901) ^ 146657429 = (3 : ZMod 600708832901) ^ (73328714 + 73328714 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 73328714 * (3 : ZMod 600708832901) ^ 73328714) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 541792405422 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 600708832901) ^ 293314859 = 105415212645 := by
        calc
          (3 : ZMod 600708832901) ^ 293314859 = (3 : ZMod 600708832901) ^ (146657429 + 146657429 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 146657429 * (3 : ZMod 600708832901) ^ 146657429) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 105415212645 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 600708832901) ^ 586629719 = 38061394930 := by
        calc
          (3 : ZMod 600708832901) ^ 586629719 = (3 : ZMod 600708832901) ^ (293314859 + 293314859 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 293314859 * (3 : ZMod 600708832901) ^ 293314859) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 38061394930 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 600708832901) ^ 1173259439 = 497146763890 := by
        calc
          (3 : ZMod 600708832901) ^ 1173259439 = (3 : ZMod 600708832901) ^ (586629719 + 586629719 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 586629719 * (3 : ZMod 600708832901) ^ 586629719) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 497146763890 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 600708832901) ^ 2346518878 = 395847914788 := by
        calc
          (3 : ZMod 600708832901) ^ 2346518878 = (3 : ZMod 600708832901) ^ (1173259439 + 1173259439) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 1173259439 * (3 : ZMod 600708832901) ^ 1173259439 := by rw [pow_add]
          _ = 395847914788 := by rw [factor_0_30]; decide
      have factor_0_32 : (3 : ZMod 600708832901) ^ 4693037757 = 425481098902 := by
        calc
          (3 : ZMod 600708832901) ^ 4693037757 = (3 : ZMod 600708832901) ^ (2346518878 + 2346518878 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 2346518878 * (3 : ZMod 600708832901) ^ 2346518878) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 425481098902 := by rw [factor_0_31]; decide
      have factor_0_33 : (3 : ZMod 600708832901) ^ 9386075514 = 500447777890 := by
        calc
          (3 : ZMod 600708832901) ^ 9386075514 = (3 : ZMod 600708832901) ^ (4693037757 + 4693037757) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 4693037757 * (3 : ZMod 600708832901) ^ 4693037757 := by rw [pow_add]
          _ = 500447777890 := by rw [factor_0_32]; decide
      have factor_0_34 : (3 : ZMod 600708832901) ^ 18772151028 = 254095835119 := by
        calc
          (3 : ZMod 600708832901) ^ 18772151028 = (3 : ZMod 600708832901) ^ (9386075514 + 9386075514) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 9386075514 * (3 : ZMod 600708832901) ^ 9386075514 := by rw [pow_add]
          _ = 254095835119 := by rw [factor_0_33]; decide
      have factor_0_35 : (3 : ZMod 600708832901) ^ 37544302056 = 109406900886 := by
        calc
          (3 : ZMod 600708832901) ^ 37544302056 = (3 : ZMod 600708832901) ^ (18772151028 + 18772151028) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 18772151028 * (3 : ZMod 600708832901) ^ 18772151028 := by rw [pow_add]
          _ = 109406900886 := by rw [factor_0_34]; decide
      have factor_0_36 : (3 : ZMod 600708832901) ^ 75088604112 = 501777653455 := by
        calc
          (3 : ZMod 600708832901) ^ 75088604112 = (3 : ZMod 600708832901) ^ (37544302056 + 37544302056) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 37544302056 * (3 : ZMod 600708832901) ^ 37544302056 := by rw [pow_add]
          _ = 501777653455 := by rw [factor_0_35]; decide
      have factor_0_37 : (3 : ZMod 600708832901) ^ 150177208225 = 9998759460 := by
        calc
          (3 : ZMod 600708832901) ^ 150177208225 = (3 : ZMod 600708832901) ^ (75088604112 + 75088604112 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 75088604112 * (3 : ZMod 600708832901) ^ 75088604112) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 9998759460 := by rw [factor_0_36]; decide
      have factor_0_38 : (3 : ZMod 600708832901) ^ 300354416450 = 600708832900 := by
        calc
          (3 : ZMod 600708832901) ^ 300354416450 = (3 : ZMod 600708832901) ^ (150177208225 + 150177208225) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 150177208225 * (3 : ZMod 600708832901) ^ 150177208225 := by rw [pow_add]
          _ = 600708832900 := by rw [factor_0_37]; decide
      change (3 : ZMod 600708832901) ^ 300354416450 ≠ 1
      rw [factor_0_38]
      decide
    ·
      have factor_1_0 : (3 : ZMod 600708832901) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 600708832901) ^ 3 = 27 := by
        calc
          (3 : ZMod 600708832901) ^ 3 = (3 : ZMod 600708832901) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 1 * (3 : ZMod 600708832901) ^ 1) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 600708832901) ^ 6 = 729 := by
        calc
          (3 : ZMod 600708832901) ^ 6 = (3 : ZMod 600708832901) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 3 * (3 : ZMod 600708832901) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 600708832901) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 600708832901) ^ 13 = (3 : ZMod 600708832901) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 6 * (3 : ZMod 600708832901) ^ 6) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 600708832901) ^ 27 = 417091490175 := by
        calc
          (3 : ZMod 600708832901) ^ 27 = (3 : ZMod 600708832901) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 13 * (3 : ZMod 600708832901) ^ 13) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 417091490175 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 600708832901) ^ 55 = 402938705730 := by
        calc
          (3 : ZMod 600708832901) ^ 55 = (3 : ZMod 600708832901) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 27 * (3 : ZMod 600708832901) ^ 27) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 402938705730 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 600708832901) ^ 111 = 501805675908 := by
        calc
          (3 : ZMod 600708832901) ^ 111 = (3 : ZMod 600708832901) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 55 * (3 : ZMod 600708832901) ^ 55) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 501805675908 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 600708832901) ^ 223 = 192781017268 := by
        calc
          (3 : ZMod 600708832901) ^ 223 = (3 : ZMod 600708832901) ^ (111 + 111 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 111 * (3 : ZMod 600708832901) ^ 111) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 192781017268 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 600708832901) ^ 447 = 126161073160 := by
        calc
          (3 : ZMod 600708832901) ^ 447 = (3 : ZMod 600708832901) ^ (223 + 223 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 223 * (3 : ZMod 600708832901) ^ 223) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 126161073160 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 600708832901) ^ 895 = 207353193866 := by
        calc
          (3 : ZMod 600708832901) ^ 895 = (3 : ZMod 600708832901) ^ (447 + 447 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 447 * (3 : ZMod 600708832901) ^ 447) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 207353193866 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 600708832901) ^ 1790 = 436127156475 := by
        calc
          (3 : ZMod 600708832901) ^ 1790 = (3 : ZMod 600708832901) ^ (895 + 895) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 895 * (3 : ZMod 600708832901) ^ 895 := by rw [pow_add]
          _ = 436127156475 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 600708832901) ^ 3580 = 304845319272 := by
        calc
          (3 : ZMod 600708832901) ^ 3580 = (3 : ZMod 600708832901) ^ (1790 + 1790) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 1790 * (3 : ZMod 600708832901) ^ 1790 := by rw [pow_add]
          _ = 304845319272 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 600708832901) ^ 7161 = 104459856663 := by
        calc
          (3 : ZMod 600708832901) ^ 7161 = (3 : ZMod 600708832901) ^ (3580 + 3580 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 3580 * (3 : ZMod 600708832901) ^ 3580) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 104459856663 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 600708832901) ^ 14322 = 76645873567 := by
        calc
          (3 : ZMod 600708832901) ^ 14322 = (3 : ZMod 600708832901) ^ (7161 + 7161) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 7161 * (3 : ZMod 600708832901) ^ 7161 := by rw [pow_add]
          _ = 76645873567 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 600708832901) ^ 28644 = 567520672668 := by
        calc
          (3 : ZMod 600708832901) ^ 28644 = (3 : ZMod 600708832901) ^ (14322 + 14322) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 14322 * (3 : ZMod 600708832901) ^ 14322 := by rw [pow_add]
          _ = 567520672668 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 600708832901) ^ 57288 = 413363218839 := by
        calc
          (3 : ZMod 600708832901) ^ 57288 = (3 : ZMod 600708832901) ^ (28644 + 28644) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 28644 * (3 : ZMod 600708832901) ^ 28644 := by rw [pow_add]
          _ = 413363218839 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 600708832901) ^ 114576 = 294486420200 := by
        calc
          (3 : ZMod 600708832901) ^ 114576 = (3 : ZMod 600708832901) ^ (57288 + 57288) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 57288 * (3 : ZMod 600708832901) ^ 57288 := by rw [pow_add]
          _ = 294486420200 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 600708832901) ^ 229152 = 459904902978 := by
        calc
          (3 : ZMod 600708832901) ^ 229152 = (3 : ZMod 600708832901) ^ (114576 + 114576) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 114576 * (3 : ZMod 600708832901) ^ 114576 := by rw [pow_add]
          _ = 459904902978 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 600708832901) ^ 458304 = 511192832635 := by
        calc
          (3 : ZMod 600708832901) ^ 458304 = (3 : ZMod 600708832901) ^ (229152 + 229152) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 229152 * (3 : ZMod 600708832901) ^ 229152 := by rw [pow_add]
          _ = 511192832635 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 600708832901) ^ 916608 = 323738438197 := by
        calc
          (3 : ZMod 600708832901) ^ 916608 = (3 : ZMod 600708832901) ^ (458304 + 458304) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 458304 * (3 : ZMod 600708832901) ^ 458304 := by rw [pow_add]
          _ = 323738438197 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 600708832901) ^ 1833217 = 535944950525 := by
        calc
          (3 : ZMod 600708832901) ^ 1833217 = (3 : ZMod 600708832901) ^ (916608 + 916608 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 916608 * (3 : ZMod 600708832901) ^ 916608) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 535944950525 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 600708832901) ^ 3666435 = 179268296230 := by
        calc
          (3 : ZMod 600708832901) ^ 3666435 = (3 : ZMod 600708832901) ^ (1833217 + 1833217 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 1833217 * (3 : ZMod 600708832901) ^ 1833217) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 179268296230 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 600708832901) ^ 7332871 = 62157541412 := by
        calc
          (3 : ZMod 600708832901) ^ 7332871 = (3 : ZMod 600708832901) ^ (3666435 + 3666435 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 3666435 * (3 : ZMod 600708832901) ^ 3666435) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 62157541412 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 600708832901) ^ 14665742 = 490098045751 := by
        calc
          (3 : ZMod 600708832901) ^ 14665742 = (3 : ZMod 600708832901) ^ (7332871 + 7332871) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 7332871 * (3 : ZMod 600708832901) ^ 7332871 := by rw [pow_add]
          _ = 490098045751 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 600708832901) ^ 29331485 = 348913148475 := by
        calc
          (3 : ZMod 600708832901) ^ 29331485 = (3 : ZMod 600708832901) ^ (14665742 + 14665742 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 14665742 * (3 : ZMod 600708832901) ^ 14665742) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 348913148475 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 600708832901) ^ 58662971 = 490984497586 := by
        calc
          (3 : ZMod 600708832901) ^ 58662971 = (3 : ZMod 600708832901) ^ (29331485 + 29331485 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 29331485 * (3 : ZMod 600708832901) ^ 29331485) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 490984497586 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 600708832901) ^ 117325943 = 558350488957 := by
        calc
          (3 : ZMod 600708832901) ^ 117325943 = (3 : ZMod 600708832901) ^ (58662971 + 58662971 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 58662971 * (3 : ZMod 600708832901) ^ 58662971) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 558350488957 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 600708832901) ^ 234651887 = 64249461600 := by
        calc
          (3 : ZMod 600708832901) ^ 234651887 = (3 : ZMod 600708832901) ^ (117325943 + 117325943 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 117325943 * (3 : ZMod 600708832901) ^ 117325943) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 64249461600 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 600708832901) ^ 469303775 = 536545235361 := by
        calc
          (3 : ZMod 600708832901) ^ 469303775 = (3 : ZMod 600708832901) ^ (234651887 + 234651887 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 234651887 * (3 : ZMod 600708832901) ^ 234651887) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 536545235361 := by rw [factor_1_27]; decide
      have factor_1_29 : (3 : ZMod 600708832901) ^ 938607551 = 173661654540 := by
        calc
          (3 : ZMod 600708832901) ^ 938607551 = (3 : ZMod 600708832901) ^ (469303775 + 469303775 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 469303775 * (3 : ZMod 600708832901) ^ 469303775) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 173661654540 := by rw [factor_1_28]; decide
      have factor_1_30 : (3 : ZMod 600708832901) ^ 1877215102 = 278560652538 := by
        calc
          (3 : ZMod 600708832901) ^ 1877215102 = (3 : ZMod 600708832901) ^ (938607551 + 938607551) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 938607551 * (3 : ZMod 600708832901) ^ 938607551 := by rw [pow_add]
          _ = 278560652538 := by rw [factor_1_29]; decide
      have factor_1_31 : (3 : ZMod 600708832901) ^ 3754430205 = 290627578665 := by
        calc
          (3 : ZMod 600708832901) ^ 3754430205 = (3 : ZMod 600708832901) ^ (1877215102 + 1877215102 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 1877215102 * (3 : ZMod 600708832901) ^ 1877215102) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 290627578665 := by rw [factor_1_30]; decide
      have factor_1_32 : (3 : ZMod 600708832901) ^ 7508860411 = 269164761794 := by
        calc
          (3 : ZMod 600708832901) ^ 7508860411 = (3 : ZMod 600708832901) ^ (3754430205 + 3754430205 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 3754430205 * (3 : ZMod 600708832901) ^ 3754430205) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 269164761794 := by rw [factor_1_31]; decide
      have factor_1_33 : (3 : ZMod 600708832901) ^ 15017720822 = 167250827558 := by
        calc
          (3 : ZMod 600708832901) ^ 15017720822 = (3 : ZMod 600708832901) ^ (7508860411 + 7508860411) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 7508860411 * (3 : ZMod 600708832901) ^ 7508860411 := by rw [pow_add]
          _ = 167250827558 := by rw [factor_1_32]; decide
      have factor_1_34 : (3 : ZMod 600708832901) ^ 30035441645 = 114744892630 := by
        calc
          (3 : ZMod 600708832901) ^ 30035441645 = (3 : ZMod 600708832901) ^ (15017720822 + 15017720822 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 15017720822 * (3 : ZMod 600708832901) ^ 15017720822) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 114744892630 := by rw [factor_1_33]; decide
      have factor_1_35 : (3 : ZMod 600708832901) ^ 60070883290 = 7964980898 := by
        calc
          (3 : ZMod 600708832901) ^ 60070883290 = (3 : ZMod 600708832901) ^ (30035441645 + 30035441645) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 30035441645 * (3 : ZMod 600708832901) ^ 30035441645 := by rw [pow_add]
          _ = 7964980898 := by rw [factor_1_34]; decide
      have factor_1_36 : (3 : ZMod 600708832901) ^ 120141766580 = 191238153403 := by
        calc
          (3 : ZMod 600708832901) ^ 120141766580 = (3 : ZMod 600708832901) ^ (60070883290 + 60070883290) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 60070883290 * (3 : ZMod 600708832901) ^ 60070883290 := by rw [pow_add]
          _ = 191238153403 := by rw [factor_1_35]; decide
      change (3 : ZMod 600708832901) ^ 120141766580 ≠ 1
      rw [factor_1_36]
      decide
    ·
      have factor_2_0 : (3 : ZMod 600708832901) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 600708832901) ^ 3 = 27 := by
        calc
          (3 : ZMod 600708832901) ^ 3 = (3 : ZMod 600708832901) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 1 * (3 : ZMod 600708832901) ^ 1) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 600708832901) ^ 6 = 729 := by
        calc
          (3 : ZMod 600708832901) ^ 6 = (3 : ZMod 600708832901) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 3 * (3 : ZMod 600708832901) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 600708832901) ^ 12 = 531441 := by
        calc
          (3 : ZMod 600708832901) ^ 12 = (3 : ZMod 600708832901) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 6 * (3 : ZMod 600708832901) ^ 6 := by rw [pow_add]
          _ = 531441 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 600708832901) ^ 25 = 246579776542 := by
        calc
          (3 : ZMod 600708832901) ^ 25 = (3 : ZMod 600708832901) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 12 * (3 : ZMod 600708832901) ^ 12) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 246579776542 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 600708832901) ^ 50 = 253807570624 := by
        calc
          (3 : ZMod 600708832901) ^ 50 = (3 : ZMod 600708832901) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 25 * (3 : ZMod 600708832901) ^ 25 := by rw [pow_add]
          _ = 253807570624 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 600708832901) ^ 101 = 293633437479 := by
        calc
          (3 : ZMod 600708832901) ^ 101 = (3 : ZMod 600708832901) ^ (50 + 50 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 50 * (3 : ZMod 600708832901) ^ 50) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 293633437479 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 600708832901) ^ 203 = 34061265481 := by
        calc
          (3 : ZMod 600708832901) ^ 203 = (3 : ZMod 600708832901) ^ (101 + 101 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 101 * (3 : ZMod 600708832901) ^ 101) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 34061265481 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 600708832901) ^ 406 = 398174024374 := by
        calc
          (3 : ZMod 600708832901) ^ 406 = (3 : ZMod 600708832901) ^ (203 + 203) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 203 * (3 : ZMod 600708832901) ^ 203 := by rw [pow_add]
          _ = 398174024374 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 600708832901) ^ 813 = 411524941717 := by
        calc
          (3 : ZMod 600708832901) ^ 813 = (3 : ZMod 600708832901) ^ (406 + 406 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 406 * (3 : ZMod 600708832901) ^ 406) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 411524941717 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 600708832901) ^ 1627 = 75258481615 := by
        calc
          (3 : ZMod 600708832901) ^ 1627 = (3 : ZMod 600708832901) ^ (813 + 813 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 813 * (3 : ZMod 600708832901) ^ 813) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 75258481615 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 600708832901) ^ 3255 = 349119054885 := by
        calc
          (3 : ZMod 600708832901) ^ 3255 = (3 : ZMod 600708832901) ^ (1627 + 1627 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 1627 * (3 : ZMod 600708832901) ^ 1627) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 349119054885 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 600708832901) ^ 6510 = 84500057853 := by
        calc
          (3 : ZMod 600708832901) ^ 6510 = (3 : ZMod 600708832901) ^ (3255 + 3255) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 3255 * (3 : ZMod 600708832901) ^ 3255 := by rw [pow_add]
          _ = 84500057853 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 600708832901) ^ 13020 = 485636471089 := by
        calc
          (3 : ZMod 600708832901) ^ 13020 = (3 : ZMod 600708832901) ^ (6510 + 6510) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 6510 * (3 : ZMod 600708832901) ^ 6510 := by rw [pow_add]
          _ = 485636471089 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 600708832901) ^ 26040 = 50224384935 := by
        calc
          (3 : ZMod 600708832901) ^ 26040 = (3 : ZMod 600708832901) ^ (13020 + 13020) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 13020 * (3 : ZMod 600708832901) ^ 13020 := by rw [pow_add]
          _ = 50224384935 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 600708832901) ^ 52080 = 54236887025 := by
        calc
          (3 : ZMod 600708832901) ^ 52080 = (3 : ZMod 600708832901) ^ (26040 + 26040) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 26040 * (3 : ZMod 600708832901) ^ 26040 := by rw [pow_add]
          _ = 54236887025 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 600708832901) ^ 104160 = 510689032932 := by
        calc
          (3 : ZMod 600708832901) ^ 104160 = (3 : ZMod 600708832901) ^ (52080 + 52080) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 52080 * (3 : ZMod 600708832901) ^ 52080 := by rw [pow_add]
          _ = 510689032932 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 600708832901) ^ 208320 = 192385839548 := by
        calc
          (3 : ZMod 600708832901) ^ 208320 = (3 : ZMod 600708832901) ^ (104160 + 104160) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 104160 * (3 : ZMod 600708832901) ^ 104160 := by rw [pow_add]
          _ = 192385839548 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 600708832901) ^ 416640 = 499259411691 := by
        calc
          (3 : ZMod 600708832901) ^ 416640 = (3 : ZMod 600708832901) ^ (208320 + 208320) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 208320 * (3 : ZMod 600708832901) ^ 208320 := by rw [pow_add]
          _ = 499259411691 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 600708832901) ^ 833280 = 208542772064 := by
        calc
          (3 : ZMod 600708832901) ^ 833280 = (3 : ZMod 600708832901) ^ (416640 + 416640) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 416640 * (3 : ZMod 600708832901) ^ 416640 := by rw [pow_add]
          _ = 208542772064 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 600708832901) ^ 1666561 = 389480196331 := by
        calc
          (3 : ZMod 600708832901) ^ 1666561 = (3 : ZMod 600708832901) ^ (833280 + 833280 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 833280 * (3 : ZMod 600708832901) ^ 833280) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 389480196331 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 600708832901) ^ 3333123 = 160336681924 := by
        calc
          (3 : ZMod 600708832901) ^ 3333123 = (3 : ZMod 600708832901) ^ (1666561 + 1666561 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 1666561 * (3 : ZMod 600708832901) ^ 1666561) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 160336681924 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 600708832901) ^ 6666246 = 264645477016 := by
        calc
          (3 : ZMod 600708832901) ^ 6666246 = (3 : ZMod 600708832901) ^ (3333123 + 3333123) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 3333123 * (3 : ZMod 600708832901) ^ 3333123 := by rw [pow_add]
          _ = 264645477016 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 600708832901) ^ 13332493 = 9165670838 := by
        calc
          (3 : ZMod 600708832901) ^ 13332493 = (3 : ZMod 600708832901) ^ (6666246 + 6666246 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 6666246 * (3 : ZMod 600708832901) ^ 6666246) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 9165670838 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 600708832901) ^ 26664987 = 502307995277 := by
        calc
          (3 : ZMod 600708832901) ^ 26664987 = (3 : ZMod 600708832901) ^ (13332493 + 13332493 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 13332493 * (3 : ZMod 600708832901) ^ 13332493) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 502307995277 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 600708832901) ^ 53329974 = 155450395632 := by
        calc
          (3 : ZMod 600708832901) ^ 53329974 = (3 : ZMod 600708832901) ^ (26664987 + 26664987) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 26664987 * (3 : ZMod 600708832901) ^ 26664987 := by rw [pow_add]
          _ = 155450395632 := by rw [factor_2_24]; decide
      have factor_2_26 : (3 : ZMod 600708832901) ^ 106659949 = 377925973324 := by
        calc
          (3 : ZMod 600708832901) ^ 106659949 = (3 : ZMod 600708832901) ^ (53329974 + 53329974 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 53329974 * (3 : ZMod 600708832901) ^ 53329974) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 377925973324 := by rw [factor_2_25]; decide
      have factor_2_27 : (3 : ZMod 600708832901) ^ 213319898 = 112932367107 := by
        calc
          (3 : ZMod 600708832901) ^ 213319898 = (3 : ZMod 600708832901) ^ (106659949 + 106659949) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 106659949 * (3 : ZMod 600708832901) ^ 106659949 := by rw [pow_add]
          _ = 112932367107 := by rw [factor_2_26]; decide
      have factor_2_28 : (3 : ZMod 600708832901) ^ 426639796 = 305155317706 := by
        calc
          (3 : ZMod 600708832901) ^ 426639796 = (3 : ZMod 600708832901) ^ (213319898 + 213319898) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 213319898 * (3 : ZMod 600708832901) ^ 213319898 := by rw [pow_add]
          _ = 305155317706 := by rw [factor_2_27]; decide
      have factor_2_29 : (3 : ZMod 600708832901) ^ 853279592 = 240093172163 := by
        calc
          (3 : ZMod 600708832901) ^ 853279592 = (3 : ZMod 600708832901) ^ (426639796 + 426639796) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 426639796 * (3 : ZMod 600708832901) ^ 426639796 := by rw [pow_add]
          _ = 240093172163 := by rw [factor_2_28]; decide
      have factor_2_30 : (3 : ZMod 600708832901) ^ 1706559184 = 293865322779 := by
        calc
          (3 : ZMod 600708832901) ^ 1706559184 = (3 : ZMod 600708832901) ^ (853279592 + 853279592) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 853279592 * (3 : ZMod 600708832901) ^ 853279592 := by rw [pow_add]
          _ = 293865322779 := by rw [factor_2_29]; decide
      have factor_2_31 : (3 : ZMod 600708832901) ^ 3413118368 = 137255734739 := by
        calc
          (3 : ZMod 600708832901) ^ 3413118368 = (3 : ZMod 600708832901) ^ (1706559184 + 1706559184) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 1706559184 * (3 : ZMod 600708832901) ^ 1706559184 := by rw [pow_add]
          _ = 137255734739 := by rw [factor_2_30]; decide
      have factor_2_32 : (3 : ZMod 600708832901) ^ 6826236737 = 193162898024 := by
        calc
          (3 : ZMod 600708832901) ^ 6826236737 = (3 : ZMod 600708832901) ^ (3413118368 + 3413118368 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 3413118368 * (3 : ZMod 600708832901) ^ 3413118368) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 193162898024 := by rw [factor_2_31]; decide
      have factor_2_33 : (3 : ZMod 600708832901) ^ 13652473475 = 232788504810 := by
        calc
          (3 : ZMod 600708832901) ^ 13652473475 = (3 : ZMod 600708832901) ^ (6826236737 + 6826236737 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 6826236737 * (3 : ZMod 600708832901) ^ 6826236737) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 232788504810 := by rw [factor_2_32]; decide
      have factor_2_34 : (3 : ZMod 600708832901) ^ 27304946950 = 576355600745 := by
        calc
          (3 : ZMod 600708832901) ^ 27304946950 = (3 : ZMod 600708832901) ^ (13652473475 + 13652473475) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 13652473475 * (3 : ZMod 600708832901) ^ 13652473475 := by rw [pow_add]
          _ = 576355600745 := by rw [factor_2_33]; decide
      have factor_2_35 : (3 : ZMod 600708832901) ^ 54609893900 = 420220836394 := by
        calc
          (3 : ZMod 600708832901) ^ 54609893900 = (3 : ZMod 600708832901) ^ (27304946950 + 27304946950) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 27304946950 * (3 : ZMod 600708832901) ^ 27304946950 := by rw [pow_add]
          _ = 420220836394 := by rw [factor_2_34]; decide
      change (3 : ZMod 600708832901) ^ 54609893900 ≠ 1
      rw [factor_2_35]
      decide
    ·
      have factor_3_0 : (3 : ZMod 600708832901) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 600708832901) ^ 2 = 9 := by
        calc
          (3 : ZMod 600708832901) ^ 2 = (3 : ZMod 600708832901) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 1 * (3 : ZMod 600708832901) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 600708832901) ^ 4 = 81 := by
        calc
          (3 : ZMod 600708832901) ^ 4 = (3 : ZMod 600708832901) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 2 * (3 : ZMod 600708832901) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 600708832901) ^ 8 = 6561 := by
        calc
          (3 : ZMod 600708832901) ^ 8 = (3 : ZMod 600708832901) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 4 * (3 : ZMod 600708832901) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 600708832901) ^ 16 = 43046721 := by
        calc
          (3 : ZMod 600708832901) ^ 16 = (3 : ZMod 600708832901) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 8 * (3 : ZMod 600708832901) ^ 8 := by rw [pow_add]
          _ = 43046721 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 600708832901) ^ 32 = 434148185157 := by
        calc
          (3 : ZMod 600708832901) ^ 32 = (3 : ZMod 600708832901) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 16 * (3 : ZMod 600708832901) ^ 16 := by rw [pow_add]
          _ = 434148185157 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 600708832901) ^ 65 = 252181107962 := by
        calc
          (3 : ZMod 600708832901) ^ 65 = (3 : ZMod 600708832901) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 32 * (3 : ZMod 600708832901) ^ 32) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 252181107962 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 600708832901) ^ 131 = 468218457940 := by
        calc
          (3 : ZMod 600708832901) ^ 131 = (3 : ZMod 600708832901) ^ (65 + 65 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 65 * (3 : ZMod 600708832901) ^ 65) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 468218457940 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 600708832901) ^ 263 = 180862078989 := by
        calc
          (3 : ZMod 600708832901) ^ 263 = (3 : ZMod 600708832901) ^ (131 + 131 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 131 * (3 : ZMod 600708832901) ^ 131) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 180862078989 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 600708832901) ^ 526 = 94146571888 := by
        calc
          (3 : ZMod 600708832901) ^ 526 = (3 : ZMod 600708832901) ^ (263 + 263) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 263 * (3 : ZMod 600708832901) ^ 263 := by rw [pow_add]
          _ = 94146571888 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 600708832901) ^ 1053 = 509389460086 := by
        calc
          (3 : ZMod 600708832901) ^ 1053 = (3 : ZMod 600708832901) ^ (526 + 526 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 526 * (3 : ZMod 600708832901) ^ 526) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 509389460086 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 600708832901) ^ 2106 = 351863375040 := by
        calc
          (3 : ZMod 600708832901) ^ 2106 = (3 : ZMod 600708832901) ^ (1053 + 1053) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 1053 * (3 : ZMod 600708832901) ^ 1053 := by rw [pow_add]
          _ = 351863375040 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 600708832901) ^ 4212 = 458662835475 := by
        calc
          (3 : ZMod 600708832901) ^ 4212 = (3 : ZMod 600708832901) ^ (2106 + 2106) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 2106 * (3 : ZMod 600708832901) ^ 2106 := by rw [pow_add]
          _ = 458662835475 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 600708832901) ^ 8424 = 86976439833 := by
        calc
          (3 : ZMod 600708832901) ^ 8424 = (3 : ZMod 600708832901) ^ (4212 + 4212) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 4212 * (3 : ZMod 600708832901) ^ 4212 := by rw [pow_add]
          _ = 86976439833 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 600708832901) ^ 16849 = 280246349432 := by
        calc
          (3 : ZMod 600708832901) ^ 16849 = (3 : ZMod 600708832901) ^ (8424 + 8424 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 8424 * (3 : ZMod 600708832901) ^ 8424) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 280246349432 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 600708832901) ^ 33698 = 297481353806 := by
        calc
          (3 : ZMod 600708832901) ^ 33698 = (3 : ZMod 600708832901) ^ (16849 + 16849) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 16849 * (3 : ZMod 600708832901) ^ 16849 := by rw [pow_add]
          _ = 297481353806 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 600708832901) ^ 67397 = 482500439923 := by
        calc
          (3 : ZMod 600708832901) ^ 67397 = (3 : ZMod 600708832901) ^ (33698 + 33698 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 33698 * (3 : ZMod 600708832901) ^ 33698) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 482500439923 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 600708832901) ^ 134795 = 126405283113 := by
        calc
          (3 : ZMod 600708832901) ^ 134795 = (3 : ZMod 600708832901) ^ (67397 + 67397 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 67397 * (3 : ZMod 600708832901) ^ 67397) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 126405283113 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 600708832901) ^ 269590 = 348635898830 := by
        calc
          (3 : ZMod 600708832901) ^ 269590 = (3 : ZMod 600708832901) ^ (134795 + 134795) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 134795 * (3 : ZMod 600708832901) ^ 134795 := by rw [pow_add]
          _ = 348635898830 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 600708832901) ^ 539181 = 182024418313 := by
        calc
          (3 : ZMod 600708832901) ^ 539181 = (3 : ZMod 600708832901) ^ (269590 + 269590 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 269590 * (3 : ZMod 600708832901) ^ 269590) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 182024418313 := by rw [factor_3_18]; decide
      have factor_3_20 : (3 : ZMod 600708832901) ^ 1078363 = 538950039370 := by
        calc
          (3 : ZMod 600708832901) ^ 1078363 = (3 : ZMod 600708832901) ^ (539181 + 539181 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 539181 * (3 : ZMod 600708832901) ^ 539181) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 538950039370 := by rw [factor_3_19]; decide
      have factor_3_21 : (3 : ZMod 600708832901) ^ 2156726 = 444204577286 := by
        calc
          (3 : ZMod 600708832901) ^ 2156726 = (3 : ZMod 600708832901) ^ (1078363 + 1078363) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 1078363 * (3 : ZMod 600708832901) ^ 1078363 := by rw [pow_add]
          _ = 444204577286 := by rw [factor_3_20]; decide
      have factor_3_22 : (3 : ZMod 600708832901) ^ 4313453 = 46570461163 := by
        calc
          (3 : ZMod 600708832901) ^ 4313453 = (3 : ZMod 600708832901) ^ (2156726 + 2156726 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 2156726 * (3 : ZMod 600708832901) ^ 2156726) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 46570461163 := by rw [factor_3_21]; decide
      have factor_3_23 : (3 : ZMod 600708832901) ^ 8626907 = 550459317446 := by
        calc
          (3 : ZMod 600708832901) ^ 8626907 = (3 : ZMod 600708832901) ^ (4313453 + 4313453 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 4313453 * (3 : ZMod 600708832901) ^ 4313453) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 550459317446 := by rw [factor_3_22]; decide
      have factor_3_24 : (3 : ZMod 600708832901) ^ 17253815 = 534019553466 := by
        calc
          (3 : ZMod 600708832901) ^ 17253815 = (3 : ZMod 600708832901) ^ (8626907 + 8626907 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 8626907 * (3 : ZMod 600708832901) ^ 8626907) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 534019553466 := by rw [factor_3_23]; decide
      have factor_3_25 : (3 : ZMod 600708832901) ^ 34507630 = 244237298634 := by
        calc
          (3 : ZMod 600708832901) ^ 34507630 = (3 : ZMod 600708832901) ^ (17253815 + 17253815) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 17253815 * (3 : ZMod 600708832901) ^ 17253815 := by rw [pow_add]
          _ = 244237298634 := by rw [factor_3_24]; decide
      have factor_3_26 : (3 : ZMod 600708832901) ^ 69015261 = 202451054462 := by
        calc
          (3 : ZMod 600708832901) ^ 69015261 = (3 : ZMod 600708832901) ^ (34507630 + 34507630 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 34507630 * (3 : ZMod 600708832901) ^ 34507630) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 202451054462 := by rw [factor_3_25]; decide
      have factor_3_27 : (3 : ZMod 600708832901) ^ 138030522 = 316169120934 := by
        calc
          (3 : ZMod 600708832901) ^ 138030522 = (3 : ZMod 600708832901) ^ (69015261 + 69015261) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 69015261 * (3 : ZMod 600708832901) ^ 69015261 := by rw [pow_add]
          _ = 316169120934 := by rw [factor_3_26]; decide
      have factor_3_28 : (3 : ZMod 600708832901) ^ 276061044 = 261130267155 := by
        calc
          (3 : ZMod 600708832901) ^ 276061044 = (3 : ZMod 600708832901) ^ (138030522 + 138030522) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 138030522 * (3 : ZMod 600708832901) ^ 138030522 := by rw [pow_add]
          _ = 261130267155 := by rw [factor_3_27]; decide
      have factor_3_29 : (3 : ZMod 600708832901) ^ 552122089 = 114043813551 := by
        calc
          (3 : ZMod 600708832901) ^ 552122089 = (3 : ZMod 600708832901) ^ (276061044 + 276061044 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 276061044 * (3 : ZMod 600708832901) ^ 276061044) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 114043813551 := by rw [factor_3_28]; decide
      have factor_3_30 : (3 : ZMod 600708832901) ^ 1104244178 = 43635900175 := by
        calc
          (3 : ZMod 600708832901) ^ 1104244178 = (3 : ZMod 600708832901) ^ (552122089 + 552122089) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 552122089 * (3 : ZMod 600708832901) ^ 552122089 := by rw [pow_add]
          _ = 43635900175 := by rw [factor_3_29]; decide
      have factor_3_31 : (3 : ZMod 600708832901) ^ 2208488356 = 341019487114 := by
        calc
          (3 : ZMod 600708832901) ^ 2208488356 = (3 : ZMod 600708832901) ^ (1104244178 + 1104244178) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 1104244178 * (3 : ZMod 600708832901) ^ 1104244178 := by rw [pow_add]
          _ = 341019487114 := by rw [factor_3_30]; decide
      have factor_3_32 : (3 : ZMod 600708832901) ^ 4416976712 = 5387838712 := by
        calc
          (3 : ZMod 600708832901) ^ 4416976712 = (3 : ZMod 600708832901) ^ (2208488356 + 2208488356) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 2208488356 * (3 : ZMod 600708832901) ^ 2208488356 := by rw [pow_add]
          _ = 5387838712 := by rw [factor_3_31]; decide
      have factor_3_33 : (3 : ZMod 600708832901) ^ 8833953425 = 497540680072 := by
        calc
          (3 : ZMod 600708832901) ^ 8833953425 = (3 : ZMod 600708832901) ^ (4416976712 + 4416976712 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 4416976712 * (3 : ZMod 600708832901) ^ 4416976712) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 497540680072 := by rw [factor_3_32]; decide
      have factor_3_34 : (3 : ZMod 600708832901) ^ 17667906850 = 595461511421 := by
        calc
          (3 : ZMod 600708832901) ^ 17667906850 = (3 : ZMod 600708832901) ^ (8833953425 + 8833953425) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 8833953425 * (3 : ZMod 600708832901) ^ 8833953425 := by rw [pow_add]
          _ = 595461511421 := by rw [factor_3_33]; decide
      have factor_3_35 : (3 : ZMod 600708832901) ^ 35335813700 = 104417531613 := by
        calc
          (3 : ZMod 600708832901) ^ 35335813700 = (3 : ZMod 600708832901) ^ (17667906850 + 17667906850) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 17667906850 * (3 : ZMod 600708832901) ^ 17667906850 := by rw [pow_add]
          _ = 104417531613 := by rw [factor_3_34]; decide
      change (3 : ZMod 600708832901) ^ 35335813700 ≠ 1
      rw [factor_3_35]
      decide
    ·
      have factor_4_0 : (3 : ZMod 600708832901) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 600708832901) ^ 2 = 9 := by
        calc
          (3 : ZMod 600708832901) ^ 2 = (3 : ZMod 600708832901) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 1 * (3 : ZMod 600708832901) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 600708832901) ^ 4 = 81 := by
        calc
          (3 : ZMod 600708832901) ^ 4 = (3 : ZMod 600708832901) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 2 * (3 : ZMod 600708832901) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 600708832901) ^ 9 = 19683 := by
        calc
          (3 : ZMod 600708832901) ^ 9 = (3 : ZMod 600708832901) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 4 * (3 : ZMod 600708832901) ^ 4) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 600708832901) ^ 18 = 387420489 := by
        calc
          (3 : ZMod 600708832901) ^ 18 = (3 : ZMod 600708832901) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 9 * (3 : ZMod 600708832901) ^ 9 := by rw [pow_add]
          _ = 387420489 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 600708832901) ^ 36 = 324890689459 := by
        calc
          (3 : ZMod 600708832901) ^ 36 = (3 : ZMod 600708832901) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 18 * (3 : ZMod 600708832901) ^ 18 := by rw [pow_add]
          _ = 324890689459 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 600708832901) ^ 73 = 208123529328 := by
        calc
          (3 : ZMod 600708832901) ^ 73 = (3 : ZMod 600708832901) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 36 * (3 : ZMod 600708832901) ^ 36) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 208123529328 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 600708832901) ^ 146 = 8795256321 := by
        calc
          (3 : ZMod 600708832901) ^ 146 = (3 : ZMod 600708832901) ^ (73 + 73) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 73 * (3 : ZMod 600708832901) ^ 73 := by rw [pow_add]
          _ = 8795256321 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 600708832901) ^ 292 = 296136695819 := by
        calc
          (3 : ZMod 600708832901) ^ 292 = (3 : ZMod 600708832901) ^ (146 + 146) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 146 * (3 : ZMod 600708832901) ^ 146 := by rw [pow_add]
          _ = 296136695819 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 600708832901) ^ 584 = 462776841541 := by
        calc
          (3 : ZMod 600708832901) ^ 584 = (3 : ZMod 600708832901) ^ (292 + 292) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 292 * (3 : ZMod 600708832901) ^ 292 := by rw [pow_add]
          _ = 462776841541 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 600708832901) ^ 1168 = 72113646574 := by
        calc
          (3 : ZMod 600708832901) ^ 1168 = (3 : ZMod 600708832901) ^ (584 + 584) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 584 * (3 : ZMod 600708832901) ^ 584 := by rw [pow_add]
          _ = 72113646574 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 600708832901) ^ 2337 = 66839918695 := by
        calc
          (3 : ZMod 600708832901) ^ 2337 = (3 : ZMod 600708832901) ^ (1168 + 1168 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 1168 * (3 : ZMod 600708832901) ^ 1168) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 66839918695 := by rw [factor_4_10]; decide
      have factor_4_12 : (3 : ZMod 600708832901) ^ 4675 = 492137368480 := by
        calc
          (3 : ZMod 600708832901) ^ 4675 = (3 : ZMod 600708832901) ^ (2337 + 2337 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = ((3 : ZMod 600708832901) ^ 2337 * (3 : ZMod 600708832901) ^ 2337) * (3 : ZMod 600708832901) := by rw [pow_succ, pow_add]
          _ = 492137368480 := by rw [factor_4_11]; decide
      have factor_4_13 : (3 : ZMod 600708832901) ^ 9350 = 223688339449 := by
        calc
          (3 : ZMod 600708832901) ^ 9350 = (3 : ZMod 600708832901) ^ (4675 + 4675) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 4675 * (3 : ZMod 600708832901) ^ 4675 := by rw [pow_add]
          _ = 223688339449 := by rw [factor_4_12]; decide
      have factor_4_14 : (3 : ZMod 600708832901) ^ 18700 = 21431127567 := by
        calc
          (3 : ZMod 600708832901) ^ 18700 = (3 : ZMod 600708832901) ^ (9350 + 9350) :=
            congrArg (fun n : ℕ => (3 : ZMod 600708832901) ^ n) (by norm_num)
          _ = (3 : ZMod 600708832901) ^ 9350 * (3 : ZMod 600708832901) ^ 9350 := by rw [pow_add]
          _ = 21431127567 := by rw [factor_4_13]; decide
      change (3 : ZMod 600708832901) ^ 18700 ≠ 1
      rw [factor_4_14]
      decide

#print axioms prime_lucas_600708832901

end TotientTailPeriodKiller
end Erdos249257
