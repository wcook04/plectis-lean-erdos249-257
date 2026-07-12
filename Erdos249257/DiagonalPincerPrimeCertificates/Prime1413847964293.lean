import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime43913777

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1413847964293 : Nat.Prime 1413847964293 := by
  apply lucas_primality 1413847964293 (2 : ZMod 1413847964293)
  ·
      have fermat_0 : (2 : ZMod 1413847964293) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 1413847964293) ^ 2 = 4 := by
        calc
          (2 : ZMod 1413847964293) ^ 2 = (2 : ZMod 1413847964293) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 1 * (2 : ZMod 1413847964293) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 1413847964293) ^ 5 = 32 := by
        calc
          (2 : ZMod 1413847964293) ^ 5 = (2 : ZMod 1413847964293) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 2 * (2 : ZMod 1413847964293) ^ 2) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 1413847964293) ^ 10 = 1024 := by
        calc
          (2 : ZMod 1413847964293) ^ 10 = (2 : ZMod 1413847964293) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 5 * (2 : ZMod 1413847964293) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 1413847964293) ^ 20 = 1048576 := by
        calc
          (2 : ZMod 1413847964293) ^ 20 = (2 : ZMod 1413847964293) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 10 * (2 : ZMod 1413847964293) ^ 10 := by rw [pow_add]
          _ = 1048576 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 1413847964293) ^ 41 = 785175291259 := by
        calc
          (2 : ZMod 1413847964293) ^ 41 = (2 : ZMod 1413847964293) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 20 * (2 : ZMod 1413847964293) ^ 20) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 785175291259 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 1413847964293) ^ 82 = 655153032497 := by
        calc
          (2 : ZMod 1413847964293) ^ 82 = (2 : ZMod 1413847964293) ^ (41 + 41) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 41 * (2 : ZMod 1413847964293) ^ 41 := by rw [pow_add]
          _ = 655153032497 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 1413847964293) ^ 164 = 464745012199 := by
        calc
          (2 : ZMod 1413847964293) ^ 164 = (2 : ZMod 1413847964293) ^ (82 + 82) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 82 * (2 : ZMod 1413847964293) ^ 82 := by rw [pow_add]
          _ = 464745012199 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 1413847964293) ^ 329 = 1136092554336 := by
        calc
          (2 : ZMod 1413847964293) ^ 329 = (2 : ZMod 1413847964293) ^ (164 + 164 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 164 * (2 : ZMod 1413847964293) ^ 164) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 1136092554336 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 1413847964293) ^ 658 = 330716394205 := by
        calc
          (2 : ZMod 1413847964293) ^ 658 = (2 : ZMod 1413847964293) ^ (329 + 329) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 329 * (2 : ZMod 1413847964293) ^ 329 := by rw [pow_add]
          _ = 330716394205 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 1413847964293) ^ 1316 = 795073141170 := by
        calc
          (2 : ZMod 1413847964293) ^ 1316 = (2 : ZMod 1413847964293) ^ (658 + 658) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 658 * (2 : ZMod 1413847964293) ^ 658 := by rw [pow_add]
          _ = 795073141170 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 1413847964293) ^ 2633 = 161654664138 := by
        calc
          (2 : ZMod 1413847964293) ^ 2633 = (2 : ZMod 1413847964293) ^ (1316 + 1316 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 1316 * (2 : ZMod 1413847964293) ^ 1316) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 161654664138 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 1413847964293) ^ 5266 = 1150759128461 := by
        calc
          (2 : ZMod 1413847964293) ^ 5266 = (2 : ZMod 1413847964293) ^ (2633 + 2633) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 2633 * (2 : ZMod 1413847964293) ^ 2633 := by rw [pow_add]
          _ = 1150759128461 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 1413847964293) ^ 10533 = 34475253839 := by
        calc
          (2 : ZMod 1413847964293) ^ 10533 = (2 : ZMod 1413847964293) ^ (5266 + 5266 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 5266 * (2 : ZMod 1413847964293) ^ 5266) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 34475253839 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 1413847964293) ^ 21067 = 691287195699 := by
        calc
          (2 : ZMod 1413847964293) ^ 21067 = (2 : ZMod 1413847964293) ^ (10533 + 10533 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 10533 * (2 : ZMod 1413847964293) ^ 10533) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 691287195699 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 1413847964293) ^ 42135 = 626634750968 := by
        calc
          (2 : ZMod 1413847964293) ^ 42135 = (2 : ZMod 1413847964293) ^ (21067 + 21067 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 21067 * (2 : ZMod 1413847964293) ^ 21067) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 626634750968 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 1413847964293) ^ 84271 = 861764081323 := by
        calc
          (2 : ZMod 1413847964293) ^ 84271 = (2 : ZMod 1413847964293) ^ (42135 + 42135 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 42135 * (2 : ZMod 1413847964293) ^ 42135) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 861764081323 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 1413847964293) ^ 168543 = 1122687925654 := by
        calc
          (2 : ZMod 1413847964293) ^ 168543 = (2 : ZMod 1413847964293) ^ (84271 + 84271 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 84271 * (2 : ZMod 1413847964293) ^ 84271) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 1122687925654 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 1413847964293) ^ 337087 = 1053570443613 := by
        calc
          (2 : ZMod 1413847964293) ^ 337087 = (2 : ZMod 1413847964293) ^ (168543 + 168543 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 168543 * (2 : ZMod 1413847964293) ^ 168543) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 1053570443613 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 1413847964293) ^ 674175 = 237292759944 := by
        calc
          (2 : ZMod 1413847964293) ^ 674175 = (2 : ZMod 1413847964293) ^ (337087 + 337087 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 337087 * (2 : ZMod 1413847964293) ^ 337087) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 237292759944 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 1413847964293) ^ 1348350 = 632201202811 := by
        calc
          (2 : ZMod 1413847964293) ^ 1348350 = (2 : ZMod 1413847964293) ^ (674175 + 674175) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 674175 * (2 : ZMod 1413847964293) ^ 674175 := by rw [pow_add]
          _ = 632201202811 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 1413847964293) ^ 2696700 = 647243436492 := by
        calc
          (2 : ZMod 1413847964293) ^ 2696700 = (2 : ZMod 1413847964293) ^ (1348350 + 1348350) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 1348350 * (2 : ZMod 1413847964293) ^ 1348350 := by rw [pow_add]
          _ = 647243436492 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 1413847964293) ^ 5393401 = 1412494216693 := by
        calc
          (2 : ZMod 1413847964293) ^ 5393401 = (2 : ZMod 1413847964293) ^ (2696700 + 2696700 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 2696700 * (2 : ZMod 1413847964293) ^ 2696700) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 1412494216693 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 1413847964293) ^ 10786803 = 10986489628 := by
        calc
          (2 : ZMod 1413847964293) ^ 10786803 = (2 : ZMod 1413847964293) ^ (5393401 + 5393401 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 5393401 * (2 : ZMod 1413847964293) ^ 5393401) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 10986489628 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 1413847964293) ^ 21573607 = 331095415533 := by
        calc
          (2 : ZMod 1413847964293) ^ 21573607 = (2 : ZMod 1413847964293) ^ (10786803 + 10786803 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 10786803 * (2 : ZMod 1413847964293) ^ 10786803) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 331095415533 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 1413847964293) ^ 43147215 = 561530531728 := by
        calc
          (2 : ZMod 1413847964293) ^ 43147215 = (2 : ZMod 1413847964293) ^ (21573607 + 21573607 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 21573607 * (2 : ZMod 1413847964293) ^ 21573607) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 561530531728 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 1413847964293) ^ 86294431 = 125294880761 := by
        calc
          (2 : ZMod 1413847964293) ^ 86294431 = (2 : ZMod 1413847964293) ^ (43147215 + 43147215 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 43147215 * (2 : ZMod 1413847964293) ^ 43147215) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 125294880761 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 1413847964293) ^ 172588862 = 917040578220 := by
        calc
          (2 : ZMod 1413847964293) ^ 172588862 = (2 : ZMod 1413847964293) ^ (86294431 + 86294431) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 86294431 * (2 : ZMod 1413847964293) ^ 86294431 := by rw [pow_add]
          _ = 917040578220 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 1413847964293) ^ 345177725 = 1061991277277 := by
        calc
          (2 : ZMod 1413847964293) ^ 345177725 = (2 : ZMod 1413847964293) ^ (172588862 + 172588862 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 172588862 * (2 : ZMod 1413847964293) ^ 172588862) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 1061991277277 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 1413847964293) ^ 690355451 = 981348907169 := by
        calc
          (2 : ZMod 1413847964293) ^ 690355451 = (2 : ZMod 1413847964293) ^ (345177725 + 345177725 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 345177725 * (2 : ZMod 1413847964293) ^ 345177725) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 981348907169 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 1413847964293) ^ 1380710902 = 107792144965 := by
        calc
          (2 : ZMod 1413847964293) ^ 1380710902 = (2 : ZMod 1413847964293) ^ (690355451 + 690355451) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 690355451 * (2 : ZMod 1413847964293) ^ 690355451 := by rw [pow_add]
          _ = 107792144965 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 1413847964293) ^ 2761421805 = 641216433204 := by
        calc
          (2 : ZMod 1413847964293) ^ 2761421805 = (2 : ZMod 1413847964293) ^ (1380710902 + 1380710902 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 1380710902 * (2 : ZMod 1413847964293) ^ 1380710902) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 641216433204 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 1413847964293) ^ 5522843610 = 1106753917015 := by
        calc
          (2 : ZMod 1413847964293) ^ 5522843610 = (2 : ZMod 1413847964293) ^ (2761421805 + 2761421805) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 2761421805 * (2 : ZMod 1413847964293) ^ 2761421805 := by rw [pow_add]
          _ = 1106753917015 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 1413847964293) ^ 11045687221 = 145630631513 := by
        calc
          (2 : ZMod 1413847964293) ^ 11045687221 = (2 : ZMod 1413847964293) ^ (5522843610 + 5522843610 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 5522843610 * (2 : ZMod 1413847964293) ^ 5522843610) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 145630631513 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 1413847964293) ^ 22091374442 = 732118169226 := by
        calc
          (2 : ZMod 1413847964293) ^ 22091374442 = (2 : ZMod 1413847964293) ^ (11045687221 + 11045687221) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 11045687221 * (2 : ZMod 1413847964293) ^ 11045687221 := by rw [pow_add]
          _ = 732118169226 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 1413847964293) ^ 44182748884 = 294016862438 := by
        calc
          (2 : ZMod 1413847964293) ^ 44182748884 = (2 : ZMod 1413847964293) ^ (22091374442 + 22091374442) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 22091374442 * (2 : ZMod 1413847964293) ^ 22091374442 := by rw [pow_add]
          _ = 294016862438 := by rw [fermat_34]; decide
      have fermat_36 : (2 : ZMod 1413847964293) ^ 88365497768 = 387496408944 := by
        calc
          (2 : ZMod 1413847964293) ^ 88365497768 = (2 : ZMod 1413847964293) ^ (44182748884 + 44182748884) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 44182748884 * (2 : ZMod 1413847964293) ^ 44182748884 := by rw [pow_add]
          _ = 387496408944 := by rw [fermat_35]; decide
      have fermat_37 : (2 : ZMod 1413847964293) ^ 176730995536 = 456833484450 := by
        calc
          (2 : ZMod 1413847964293) ^ 176730995536 = (2 : ZMod 1413847964293) ^ (88365497768 + 88365497768) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 88365497768 * (2 : ZMod 1413847964293) ^ 88365497768 := by rw [pow_add]
          _ = 456833484450 := by rw [fermat_36]; decide
      have fermat_38 : (2 : ZMod 1413847964293) ^ 353461991073 = 913666968899 := by
        calc
          (2 : ZMod 1413847964293) ^ 353461991073 = (2 : ZMod 1413847964293) ^ (176730995536 + 176730995536 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 176730995536 * (2 : ZMod 1413847964293) ^ 176730995536) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 913666968899 := by rw [fermat_37]; decide
      have fermat_39 : (2 : ZMod 1413847964293) ^ 706923982146 = 1413847964292 := by
        calc
          (2 : ZMod 1413847964293) ^ 706923982146 = (2 : ZMod 1413847964293) ^ (353461991073 + 353461991073) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 353461991073 * (2 : ZMod 1413847964293) ^ 353461991073 := by rw [pow_add]
          _ = 1413847964292 := by rw [fermat_38]; decide
      have fermat_40 : (2 : ZMod 1413847964293) ^ 1413847964292 = 1 := by
        calc
          (2 : ZMod 1413847964293) ^ 1413847964292 = (2 : ZMod 1413847964293) ^ (706923982146 + 706923982146) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 706923982146 * (2 : ZMod 1413847964293) ^ 706923982146 := by rw [pow_add]
          _ = 1 := by rw [fermat_39]; decide
      simpa using fermat_40
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (2683, 1), (43913777, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (2683, 1), (43913777, 1)] : List FactorBlock).map factorBlockValue).prod = 1413847964293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_43913777) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 1413847964293) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 1413847964293) ^ 2 = 4 := by
        calc
          (2 : ZMod 1413847964293) ^ 2 = (2 : ZMod 1413847964293) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 1 * (2 : ZMod 1413847964293) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 1413847964293) ^ 5 = 32 := by
        calc
          (2 : ZMod 1413847964293) ^ 5 = (2 : ZMod 1413847964293) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 2 * (2 : ZMod 1413847964293) ^ 2) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 1413847964293) ^ 10 = 1024 := by
        calc
          (2 : ZMod 1413847964293) ^ 10 = (2 : ZMod 1413847964293) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 5 * (2 : ZMod 1413847964293) ^ 5 := by rw [pow_add]
          _ = 1024 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 1413847964293) ^ 20 = 1048576 := by
        calc
          (2 : ZMod 1413847964293) ^ 20 = (2 : ZMod 1413847964293) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 10 * (2 : ZMod 1413847964293) ^ 10 := by rw [pow_add]
          _ = 1048576 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 1413847964293) ^ 41 = 785175291259 := by
        calc
          (2 : ZMod 1413847964293) ^ 41 = (2 : ZMod 1413847964293) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 20 * (2 : ZMod 1413847964293) ^ 20) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 785175291259 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 1413847964293) ^ 82 = 655153032497 := by
        calc
          (2 : ZMod 1413847964293) ^ 82 = (2 : ZMod 1413847964293) ^ (41 + 41) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 41 * (2 : ZMod 1413847964293) ^ 41 := by rw [pow_add]
          _ = 655153032497 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 1413847964293) ^ 164 = 464745012199 := by
        calc
          (2 : ZMod 1413847964293) ^ 164 = (2 : ZMod 1413847964293) ^ (82 + 82) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 82 * (2 : ZMod 1413847964293) ^ 82 := by rw [pow_add]
          _ = 464745012199 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 1413847964293) ^ 329 = 1136092554336 := by
        calc
          (2 : ZMod 1413847964293) ^ 329 = (2 : ZMod 1413847964293) ^ (164 + 164 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 164 * (2 : ZMod 1413847964293) ^ 164) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 1136092554336 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 1413847964293) ^ 658 = 330716394205 := by
        calc
          (2 : ZMod 1413847964293) ^ 658 = (2 : ZMod 1413847964293) ^ (329 + 329) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 329 * (2 : ZMod 1413847964293) ^ 329 := by rw [pow_add]
          _ = 330716394205 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 1413847964293) ^ 1316 = 795073141170 := by
        calc
          (2 : ZMod 1413847964293) ^ 1316 = (2 : ZMod 1413847964293) ^ (658 + 658) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 658 * (2 : ZMod 1413847964293) ^ 658 := by rw [pow_add]
          _ = 795073141170 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 1413847964293) ^ 2633 = 161654664138 := by
        calc
          (2 : ZMod 1413847964293) ^ 2633 = (2 : ZMod 1413847964293) ^ (1316 + 1316 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 1316 * (2 : ZMod 1413847964293) ^ 1316) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 161654664138 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 1413847964293) ^ 5266 = 1150759128461 := by
        calc
          (2 : ZMod 1413847964293) ^ 5266 = (2 : ZMod 1413847964293) ^ (2633 + 2633) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 2633 * (2 : ZMod 1413847964293) ^ 2633 := by rw [pow_add]
          _ = 1150759128461 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 1413847964293) ^ 10533 = 34475253839 := by
        calc
          (2 : ZMod 1413847964293) ^ 10533 = (2 : ZMod 1413847964293) ^ (5266 + 5266 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 5266 * (2 : ZMod 1413847964293) ^ 5266) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 34475253839 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 1413847964293) ^ 21067 = 691287195699 := by
        calc
          (2 : ZMod 1413847964293) ^ 21067 = (2 : ZMod 1413847964293) ^ (10533 + 10533 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 10533 * (2 : ZMod 1413847964293) ^ 10533) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 691287195699 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 1413847964293) ^ 42135 = 626634750968 := by
        calc
          (2 : ZMod 1413847964293) ^ 42135 = (2 : ZMod 1413847964293) ^ (21067 + 21067 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 21067 * (2 : ZMod 1413847964293) ^ 21067) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 626634750968 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 1413847964293) ^ 84271 = 861764081323 := by
        calc
          (2 : ZMod 1413847964293) ^ 84271 = (2 : ZMod 1413847964293) ^ (42135 + 42135 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 42135 * (2 : ZMod 1413847964293) ^ 42135) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 861764081323 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 1413847964293) ^ 168543 = 1122687925654 := by
        calc
          (2 : ZMod 1413847964293) ^ 168543 = (2 : ZMod 1413847964293) ^ (84271 + 84271 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 84271 * (2 : ZMod 1413847964293) ^ 84271) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 1122687925654 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 1413847964293) ^ 337087 = 1053570443613 := by
        calc
          (2 : ZMod 1413847964293) ^ 337087 = (2 : ZMod 1413847964293) ^ (168543 + 168543 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 168543 * (2 : ZMod 1413847964293) ^ 168543) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 1053570443613 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 1413847964293) ^ 674175 = 237292759944 := by
        calc
          (2 : ZMod 1413847964293) ^ 674175 = (2 : ZMod 1413847964293) ^ (337087 + 337087 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 337087 * (2 : ZMod 1413847964293) ^ 337087) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 237292759944 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 1413847964293) ^ 1348350 = 632201202811 := by
        calc
          (2 : ZMod 1413847964293) ^ 1348350 = (2 : ZMod 1413847964293) ^ (674175 + 674175) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 674175 * (2 : ZMod 1413847964293) ^ 674175 := by rw [pow_add]
          _ = 632201202811 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 1413847964293) ^ 2696700 = 647243436492 := by
        calc
          (2 : ZMod 1413847964293) ^ 2696700 = (2 : ZMod 1413847964293) ^ (1348350 + 1348350) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 1348350 * (2 : ZMod 1413847964293) ^ 1348350 := by rw [pow_add]
          _ = 647243436492 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 1413847964293) ^ 5393401 = 1412494216693 := by
        calc
          (2 : ZMod 1413847964293) ^ 5393401 = (2 : ZMod 1413847964293) ^ (2696700 + 2696700 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 2696700 * (2 : ZMod 1413847964293) ^ 2696700) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 1412494216693 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 1413847964293) ^ 10786803 = 10986489628 := by
        calc
          (2 : ZMod 1413847964293) ^ 10786803 = (2 : ZMod 1413847964293) ^ (5393401 + 5393401 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 5393401 * (2 : ZMod 1413847964293) ^ 5393401) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 10986489628 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 1413847964293) ^ 21573607 = 331095415533 := by
        calc
          (2 : ZMod 1413847964293) ^ 21573607 = (2 : ZMod 1413847964293) ^ (10786803 + 10786803 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 10786803 * (2 : ZMod 1413847964293) ^ 10786803) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 331095415533 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 1413847964293) ^ 43147215 = 561530531728 := by
        calc
          (2 : ZMod 1413847964293) ^ 43147215 = (2 : ZMod 1413847964293) ^ (21573607 + 21573607 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 21573607 * (2 : ZMod 1413847964293) ^ 21573607) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 561530531728 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 1413847964293) ^ 86294431 = 125294880761 := by
        calc
          (2 : ZMod 1413847964293) ^ 86294431 = (2 : ZMod 1413847964293) ^ (43147215 + 43147215 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 43147215 * (2 : ZMod 1413847964293) ^ 43147215) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 125294880761 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 1413847964293) ^ 172588862 = 917040578220 := by
        calc
          (2 : ZMod 1413847964293) ^ 172588862 = (2 : ZMod 1413847964293) ^ (86294431 + 86294431) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 86294431 * (2 : ZMod 1413847964293) ^ 86294431 := by rw [pow_add]
          _ = 917040578220 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 1413847964293) ^ 345177725 = 1061991277277 := by
        calc
          (2 : ZMod 1413847964293) ^ 345177725 = (2 : ZMod 1413847964293) ^ (172588862 + 172588862 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 172588862 * (2 : ZMod 1413847964293) ^ 172588862) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 1061991277277 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 1413847964293) ^ 690355451 = 981348907169 := by
        calc
          (2 : ZMod 1413847964293) ^ 690355451 = (2 : ZMod 1413847964293) ^ (345177725 + 345177725 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 345177725 * (2 : ZMod 1413847964293) ^ 345177725) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 981348907169 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 1413847964293) ^ 1380710902 = 107792144965 := by
        calc
          (2 : ZMod 1413847964293) ^ 1380710902 = (2 : ZMod 1413847964293) ^ (690355451 + 690355451) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 690355451 * (2 : ZMod 1413847964293) ^ 690355451 := by rw [pow_add]
          _ = 107792144965 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 1413847964293) ^ 2761421805 = 641216433204 := by
        calc
          (2 : ZMod 1413847964293) ^ 2761421805 = (2 : ZMod 1413847964293) ^ (1380710902 + 1380710902 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 1380710902 * (2 : ZMod 1413847964293) ^ 1380710902) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 641216433204 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 1413847964293) ^ 5522843610 = 1106753917015 := by
        calc
          (2 : ZMod 1413847964293) ^ 5522843610 = (2 : ZMod 1413847964293) ^ (2761421805 + 2761421805) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 2761421805 * (2 : ZMod 1413847964293) ^ 2761421805 := by rw [pow_add]
          _ = 1106753917015 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 1413847964293) ^ 11045687221 = 145630631513 := by
        calc
          (2 : ZMod 1413847964293) ^ 11045687221 = (2 : ZMod 1413847964293) ^ (5522843610 + 5522843610 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 5522843610 * (2 : ZMod 1413847964293) ^ 5522843610) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 145630631513 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 1413847964293) ^ 22091374442 = 732118169226 := by
        calc
          (2 : ZMod 1413847964293) ^ 22091374442 = (2 : ZMod 1413847964293) ^ (11045687221 + 11045687221) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 11045687221 * (2 : ZMod 1413847964293) ^ 11045687221 := by rw [pow_add]
          _ = 732118169226 := by rw [factor_0_33]; decide
      have factor_0_35 : (2 : ZMod 1413847964293) ^ 44182748884 = 294016862438 := by
        calc
          (2 : ZMod 1413847964293) ^ 44182748884 = (2 : ZMod 1413847964293) ^ (22091374442 + 22091374442) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 22091374442 * (2 : ZMod 1413847964293) ^ 22091374442 := by rw [pow_add]
          _ = 294016862438 := by rw [factor_0_34]; decide
      have factor_0_36 : (2 : ZMod 1413847964293) ^ 88365497768 = 387496408944 := by
        calc
          (2 : ZMod 1413847964293) ^ 88365497768 = (2 : ZMod 1413847964293) ^ (44182748884 + 44182748884) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 44182748884 * (2 : ZMod 1413847964293) ^ 44182748884 := by rw [pow_add]
          _ = 387496408944 := by rw [factor_0_35]; decide
      have factor_0_37 : (2 : ZMod 1413847964293) ^ 176730995536 = 456833484450 := by
        calc
          (2 : ZMod 1413847964293) ^ 176730995536 = (2 : ZMod 1413847964293) ^ (88365497768 + 88365497768) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 88365497768 * (2 : ZMod 1413847964293) ^ 88365497768 := by rw [pow_add]
          _ = 456833484450 := by rw [factor_0_36]; decide
      have factor_0_38 : (2 : ZMod 1413847964293) ^ 353461991073 = 913666968899 := by
        calc
          (2 : ZMod 1413847964293) ^ 353461991073 = (2 : ZMod 1413847964293) ^ (176730995536 + 176730995536 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 176730995536 * (2 : ZMod 1413847964293) ^ 176730995536) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 913666968899 := by rw [factor_0_37]; decide
      have factor_0_39 : (2 : ZMod 1413847964293) ^ 706923982146 = 1413847964292 := by
        calc
          (2 : ZMod 1413847964293) ^ 706923982146 = (2 : ZMod 1413847964293) ^ (353461991073 + 353461991073) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 353461991073 * (2 : ZMod 1413847964293) ^ 353461991073 := by rw [pow_add]
          _ = 1413847964292 := by rw [factor_0_38]; decide
      change (2 : ZMod 1413847964293) ^ 706923982146 ≠ 1
      rw [factor_0_39]
      decide
    ·
      have factor_1_0 : (2 : ZMod 1413847964293) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 1413847964293) ^ 3 = 8 := by
        calc
          (2 : ZMod 1413847964293) ^ 3 = (2 : ZMod 1413847964293) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 1 * (2 : ZMod 1413847964293) ^ 1) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 1413847964293) ^ 6 = 64 := by
        calc
          (2 : ZMod 1413847964293) ^ 6 = (2 : ZMod 1413847964293) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 3 * (2 : ZMod 1413847964293) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 1413847964293) ^ 13 = 8192 := by
        calc
          (2 : ZMod 1413847964293) ^ 13 = (2 : ZMod 1413847964293) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 6 * (2 : ZMod 1413847964293) ^ 6) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 8192 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 1413847964293) ^ 27 = 134217728 := by
        calc
          (2 : ZMod 1413847964293) ^ 27 = (2 : ZMod 1413847964293) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 13 * (2 : ZMod 1413847964293) ^ 13) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 134217728 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 1413847964293) ^ 54 = 561596424871 := by
        calc
          (2 : ZMod 1413847964293) ^ 54 = (2 : ZMod 1413847964293) ^ (27 + 27) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 27 * (2 : ZMod 1413847964293) ^ 27 := by rw [pow_add]
          _ = 561596424871 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 1413847964293) ^ 109 = 1383985984751 := by
        calc
          (2 : ZMod 1413847964293) ^ 109 = (2 : ZMod 1413847964293) ^ (54 + 54 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 54 * (2 : ZMod 1413847964293) ^ 54) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 1383985984751 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 1413847964293) ^ 219 = 180918613096 := by
        calc
          (2 : ZMod 1413847964293) ^ 219 = (2 : ZMod 1413847964293) ^ (109 + 109 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 109 * (2 : ZMod 1413847964293) ^ 109) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 180918613096 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 1413847964293) ^ 438 = 611767522350 := by
        calc
          (2 : ZMod 1413847964293) ^ 438 = (2 : ZMod 1413847964293) ^ (219 + 219) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 219 * (2 : ZMod 1413847964293) ^ 219 := by rw [pow_add]
          _ = 611767522350 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 1413847964293) ^ 877 = 1234911107862 := by
        calc
          (2 : ZMod 1413847964293) ^ 877 = (2 : ZMod 1413847964293) ^ (438 + 438 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 438 * (2 : ZMod 1413847964293) ^ 438) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 1234911107862 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 1413847964293) ^ 1755 = 858282517876 := by
        calc
          (2 : ZMod 1413847964293) ^ 1755 = (2 : ZMod 1413847964293) ^ (877 + 877 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 877 * (2 : ZMod 1413847964293) ^ 877) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 858282517876 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 1413847964293) ^ 3511 = 910833288137 := by
        calc
          (2 : ZMod 1413847964293) ^ 3511 = (2 : ZMod 1413847964293) ^ (1755 + 1755 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 1755 * (2 : ZMod 1413847964293) ^ 1755) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 910833288137 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 1413847964293) ^ 7022 = 10664537966 := by
        calc
          (2 : ZMod 1413847964293) ^ 7022 = (2 : ZMod 1413847964293) ^ (3511 + 3511) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 3511 * (2 : ZMod 1413847964293) ^ 3511 := by rw [pow_add]
          _ = 10664537966 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 1413847964293) ^ 14045 = 371728219169 := by
        calc
          (2 : ZMod 1413847964293) ^ 14045 = (2 : ZMod 1413847964293) ^ (7022 + 7022 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 7022 * (2 : ZMod 1413847964293) ^ 7022) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 371728219169 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 1413847964293) ^ 28090 = 974602053054 := by
        calc
          (2 : ZMod 1413847964293) ^ 28090 = (2 : ZMod 1413847964293) ^ (14045 + 14045) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 14045 * (2 : ZMod 1413847964293) ^ 14045 := by rw [pow_add]
          _ = 974602053054 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 1413847964293) ^ 56181 = 1313904324764 := by
        calc
          (2 : ZMod 1413847964293) ^ 56181 = (2 : ZMod 1413847964293) ^ (28090 + 28090 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 28090 * (2 : ZMod 1413847964293) ^ 28090) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 1313904324764 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 1413847964293) ^ 112362 = 500671953243 := by
        calc
          (2 : ZMod 1413847964293) ^ 112362 = (2 : ZMod 1413847964293) ^ (56181 + 56181) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 56181 * (2 : ZMod 1413847964293) ^ 56181 := by rw [pow_add]
          _ = 500671953243 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 1413847964293) ^ 224725 = 92198053744 := by
        calc
          (2 : ZMod 1413847964293) ^ 224725 = (2 : ZMod 1413847964293) ^ (112362 + 112362 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 112362 * (2 : ZMod 1413847964293) ^ 112362) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 92198053744 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 1413847964293) ^ 449450 = 1105024216376 := by
        calc
          (2 : ZMod 1413847964293) ^ 449450 = (2 : ZMod 1413847964293) ^ (224725 + 224725) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 224725 * (2 : ZMod 1413847964293) ^ 224725 := by rw [pow_add]
          _ = 1105024216376 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 1413847964293) ^ 898900 = 1076329329792 := by
        calc
          (2 : ZMod 1413847964293) ^ 898900 = (2 : ZMod 1413847964293) ^ (449450 + 449450) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 449450 * (2 : ZMod 1413847964293) ^ 449450 := by rw [pow_add]
          _ = 1076329329792 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 1413847964293) ^ 1797800 = 373612319091 := by
        calc
          (2 : ZMod 1413847964293) ^ 1797800 = (2 : ZMod 1413847964293) ^ (898900 + 898900) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 898900 * (2 : ZMod 1413847964293) ^ 898900 := by rw [pow_add]
          _ = 373612319091 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 1413847964293) ^ 3595601 = 810213331675 := by
        calc
          (2 : ZMod 1413847964293) ^ 3595601 = (2 : ZMod 1413847964293) ^ (1797800 + 1797800 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 1797800 * (2 : ZMod 1413847964293) ^ 1797800) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 810213331675 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 1413847964293) ^ 7191202 = 1317286998006 := by
        calc
          (2 : ZMod 1413847964293) ^ 7191202 = (2 : ZMod 1413847964293) ^ (3595601 + 3595601) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 3595601 * (2 : ZMod 1413847964293) ^ 3595601 := by rw [pow_add]
          _ = 1317286998006 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 1413847964293) ^ 14382405 = 815542655072 := by
        calc
          (2 : ZMod 1413847964293) ^ 14382405 = (2 : ZMod 1413847964293) ^ (7191202 + 7191202 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 7191202 * (2 : ZMod 1413847964293) ^ 7191202) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 815542655072 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 1413847964293) ^ 28764810 = 43967761003 := by
        calc
          (2 : ZMod 1413847964293) ^ 28764810 = (2 : ZMod 1413847964293) ^ (14382405 + 14382405) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 14382405 * (2 : ZMod 1413847964293) ^ 14382405 := by rw [pow_add]
          _ = 43967761003 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 1413847964293) ^ 57529620 = 1180553258959 := by
        calc
          (2 : ZMod 1413847964293) ^ 57529620 = (2 : ZMod 1413847964293) ^ (28764810 + 28764810) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 28764810 * (2 : ZMod 1413847964293) ^ 28764810 := by rw [pow_add]
          _ = 1180553258959 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 1413847964293) ^ 115059241 = 422988291112 := by
        calc
          (2 : ZMod 1413847964293) ^ 115059241 = (2 : ZMod 1413847964293) ^ (57529620 + 57529620 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 57529620 * (2 : ZMod 1413847964293) ^ 57529620) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 422988291112 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 1413847964293) ^ 230118483 = 353145542583 := by
        calc
          (2 : ZMod 1413847964293) ^ 230118483 = (2 : ZMod 1413847964293) ^ (115059241 + 115059241 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 115059241 * (2 : ZMod 1413847964293) ^ 115059241) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 353145542583 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 1413847964293) ^ 460236967 = 1190774070385 := by
        calc
          (2 : ZMod 1413847964293) ^ 460236967 = (2 : ZMod 1413847964293) ^ (230118483 + 230118483 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 230118483 * (2 : ZMod 1413847964293) ^ 230118483) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 1190774070385 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 1413847964293) ^ 920473935 = 739888959773 := by
        calc
          (2 : ZMod 1413847964293) ^ 920473935 = (2 : ZMod 1413847964293) ^ (460236967 + 460236967 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 460236967 * (2 : ZMod 1413847964293) ^ 460236967) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 739888959773 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 1413847964293) ^ 1840947870 = 241716464745 := by
        calc
          (2 : ZMod 1413847964293) ^ 1840947870 = (2 : ZMod 1413847964293) ^ (920473935 + 920473935) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 920473935 * (2 : ZMod 1413847964293) ^ 920473935 := by rw [pow_add]
          _ = 241716464745 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 1413847964293) ^ 3681895740 = 727595389404 := by
        calc
          (2 : ZMod 1413847964293) ^ 3681895740 = (2 : ZMod 1413847964293) ^ (1840947870 + 1840947870) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 1840947870 * (2 : ZMod 1413847964293) ^ 1840947870 := by rw [pow_add]
          _ = 727595389404 := by rw [factor_1_30]; decide
      have factor_1_32 : (2 : ZMod 1413847964293) ^ 7363791480 = 1100859398374 := by
        calc
          (2 : ZMod 1413847964293) ^ 7363791480 = (2 : ZMod 1413847964293) ^ (3681895740 + 3681895740) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 3681895740 * (2 : ZMod 1413847964293) ^ 3681895740 := by rw [pow_add]
          _ = 1100859398374 := by rw [factor_1_31]; decide
      have factor_1_33 : (2 : ZMod 1413847964293) ^ 14727582961 = 163612373160 := by
        calc
          (2 : ZMod 1413847964293) ^ 14727582961 = (2 : ZMod 1413847964293) ^ (7363791480 + 7363791480 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 7363791480 * (2 : ZMod 1413847964293) ^ 7363791480) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 163612373160 := by rw [factor_1_32]; decide
      have factor_1_34 : (2 : ZMod 1413847964293) ^ 29455165922 = 313371485599 := by
        calc
          (2 : ZMod 1413847964293) ^ 29455165922 = (2 : ZMod 1413847964293) ^ (14727582961 + 14727582961) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 14727582961 * (2 : ZMod 1413847964293) ^ 14727582961 := by rw [pow_add]
          _ = 313371485599 := by rw [factor_1_33]; decide
      have factor_1_35 : (2 : ZMod 1413847964293) ^ 58910331845 = 1169008763012 := by
        calc
          (2 : ZMod 1413847964293) ^ 58910331845 = (2 : ZMod 1413847964293) ^ (29455165922 + 29455165922 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 29455165922 * (2 : ZMod 1413847964293) ^ 29455165922) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 1169008763012 := by rw [factor_1_34]; decide
      have factor_1_36 : (2 : ZMod 1413847964293) ^ 117820663691 = 1089914805427 := by
        calc
          (2 : ZMod 1413847964293) ^ 117820663691 = (2 : ZMod 1413847964293) ^ (58910331845 + 58910331845 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 58910331845 * (2 : ZMod 1413847964293) ^ 58910331845) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 1089914805427 := by rw [factor_1_35]; decide
      have factor_1_37 : (2 : ZMod 1413847964293) ^ 235641327382 = 747921725203 := by
        calc
          (2 : ZMod 1413847964293) ^ 235641327382 = (2 : ZMod 1413847964293) ^ (117820663691 + 117820663691) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 117820663691 * (2 : ZMod 1413847964293) ^ 117820663691 := by rw [pow_add]
          _ = 747921725203 := by rw [factor_1_36]; decide
      have factor_1_38 : (2 : ZMod 1413847964293) ^ 471282654764 = 747921725202 := by
        calc
          (2 : ZMod 1413847964293) ^ 471282654764 = (2 : ZMod 1413847964293) ^ (235641327382 + 235641327382) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 235641327382 * (2 : ZMod 1413847964293) ^ 235641327382 := by rw [pow_add]
          _ = 747921725202 := by rw [factor_1_37]; decide
      change (2 : ZMod 1413847964293) ^ 471282654764 ≠ 1
      rw [factor_1_38]
      decide
    ·
      have factor_2_0 : (2 : ZMod 1413847964293) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 1413847964293) ^ 3 = 8 := by
        calc
          (2 : ZMod 1413847964293) ^ 3 = (2 : ZMod 1413847964293) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 1 * (2 : ZMod 1413847964293) ^ 1) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 1413847964293) ^ 7 = 128 := by
        calc
          (2 : ZMod 1413847964293) ^ 7 = (2 : ZMod 1413847964293) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 3 * (2 : ZMod 1413847964293) ^ 3) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 1413847964293) ^ 15 = 32768 := by
        calc
          (2 : ZMod 1413847964293) ^ 15 = (2 : ZMod 1413847964293) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 7 * (2 : ZMod 1413847964293) ^ 7) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 1413847964293) ^ 31 = 2147483648 := by
        calc
          (2 : ZMod 1413847964293) ^ 31 = (2 : ZMod 1413847964293) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 15 * (2 : ZMod 1413847964293) ^ 15) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 2147483648 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 1413847964293) ^ 62 = 970040373383 := by
        calc
          (2 : ZMod 1413847964293) ^ 62 = (2 : ZMod 1413847964293) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 31 * (2 : ZMod 1413847964293) ^ 31 := by rw [pow_add]
          _ = 970040373383 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 1413847964293) ^ 125 = 1144739281293 := by
        calc
          (2 : ZMod 1413847964293) ^ 125 = (2 : ZMod 1413847964293) ^ (62 + 62 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 62 * (2 : ZMod 1413847964293) ^ 62) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 1144739281293 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 1413847964293) ^ 251 = 334822745295 := by
        calc
          (2 : ZMod 1413847964293) ^ 251 = (2 : ZMod 1413847964293) ^ (125 + 125 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 125 * (2 : ZMod 1413847964293) ^ 125) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 334822745295 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 1413847964293) ^ 502 = 864174747455 := by
        calc
          (2 : ZMod 1413847964293) ^ 502 = (2 : ZMod 1413847964293) ^ (251 + 251) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 251 * (2 : ZMod 1413847964293) ^ 251 := by rw [pow_add]
          _ = 864174747455 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 1413847964293) ^ 1005 = 1026517924189 := by
        calc
          (2 : ZMod 1413847964293) ^ 1005 = (2 : ZMod 1413847964293) ^ (502 + 502 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 502 * (2 : ZMod 1413847964293) ^ 502) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 1026517924189 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 1413847964293) ^ 2010 = 289492320554 := by
        calc
          (2 : ZMod 1413847964293) ^ 2010 = (2 : ZMod 1413847964293) ^ (1005 + 1005) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 1005 * (2 : ZMod 1413847964293) ^ 1005 := by rw [pow_add]
          _ = 289492320554 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 1413847964293) ^ 4020 = 642550472880 := by
        calc
          (2 : ZMod 1413847964293) ^ 4020 = (2 : ZMod 1413847964293) ^ (2010 + 2010) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 2010 * (2 : ZMod 1413847964293) ^ 2010 := by rw [pow_add]
          _ = 642550472880 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 1413847964293) ^ 8040 = 1127970010045 := by
        calc
          (2 : ZMod 1413847964293) ^ 8040 = (2 : ZMod 1413847964293) ^ (4020 + 4020) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 4020 * (2 : ZMod 1413847964293) ^ 4020 := by rw [pow_add]
          _ = 1127970010045 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 1413847964293) ^ 16081 = 219474257659 := by
        calc
          (2 : ZMod 1413847964293) ^ 16081 = (2 : ZMod 1413847964293) ^ (8040 + 8040 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 8040 * (2 : ZMod 1413847964293) ^ 8040) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 219474257659 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 1413847964293) ^ 32163 = 523339870364 := by
        calc
          (2 : ZMod 1413847964293) ^ 32163 = (2 : ZMod 1413847964293) ^ (16081 + 16081 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 16081 * (2 : ZMod 1413847964293) ^ 16081) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 523339870364 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 1413847964293) ^ 64326 = 1021327093854 := by
        calc
          (2 : ZMod 1413847964293) ^ 64326 = (2 : ZMod 1413847964293) ^ (32163 + 32163) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 32163 * (2 : ZMod 1413847964293) ^ 32163 := by rw [pow_add]
          _ = 1021327093854 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 1413847964293) ^ 128653 = 762222030694 := by
        calc
          (2 : ZMod 1413847964293) ^ 128653 = (2 : ZMod 1413847964293) ^ (64326 + 64326 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 64326 * (2 : ZMod 1413847964293) ^ 64326) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 762222030694 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 1413847964293) ^ 257307 = 320888648249 := by
        calc
          (2 : ZMod 1413847964293) ^ 257307 = (2 : ZMod 1413847964293) ^ (128653 + 128653 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 128653 * (2 : ZMod 1413847964293) ^ 128653) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 320888648249 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 1413847964293) ^ 514614 = 120793178761 := by
        calc
          (2 : ZMod 1413847964293) ^ 514614 = (2 : ZMod 1413847964293) ^ (257307 + 257307) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 257307 * (2 : ZMod 1413847964293) ^ 257307 := by rw [pow_add]
          _ = 120793178761 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 1413847964293) ^ 1029229 = 1007960512136 := by
        calc
          (2 : ZMod 1413847964293) ^ 1029229 = (2 : ZMod 1413847964293) ^ (514614 + 514614 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 514614 * (2 : ZMod 1413847964293) ^ 514614) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 1007960512136 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 1413847964293) ^ 2058458 = 658884046333 := by
        calc
          (2 : ZMod 1413847964293) ^ 2058458 = (2 : ZMod 1413847964293) ^ (1029229 + 1029229) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 1029229 * (2 : ZMod 1413847964293) ^ 1029229 := by rw [pow_add]
          _ = 658884046333 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 1413847964293) ^ 4116916 = 640137921250 := by
        calc
          (2 : ZMod 1413847964293) ^ 4116916 = (2 : ZMod 1413847964293) ^ (2058458 + 2058458) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 2058458 * (2 : ZMod 1413847964293) ^ 2058458 := by rw [pow_add]
          _ = 640137921250 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 1413847964293) ^ 8233833 = 1127855433494 := by
        calc
          (2 : ZMod 1413847964293) ^ 8233833 = (2 : ZMod 1413847964293) ^ (4116916 + 4116916 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 4116916 * (2 : ZMod 1413847964293) ^ 4116916) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 1127855433494 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 1413847964293) ^ 16467666 = 1295389975480 := by
        calc
          (2 : ZMod 1413847964293) ^ 16467666 = (2 : ZMod 1413847964293) ^ (8233833 + 8233833) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 8233833 * (2 : ZMod 1413847964293) ^ 8233833 := by rw [pow_add]
          _ = 1295389975480 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 1413847964293) ^ 32935332 = 1158138579550 := by
        calc
          (2 : ZMod 1413847964293) ^ 32935332 = (2 : ZMod 1413847964293) ^ (16467666 + 16467666) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 16467666 * (2 : ZMod 1413847964293) ^ 16467666 := by rw [pow_add]
          _ = 1158138579550 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 1413847964293) ^ 65870665 = 1262862721721 := by
        calc
          (2 : ZMod 1413847964293) ^ 65870665 = (2 : ZMod 1413847964293) ^ (32935332 + 32935332 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 32935332 * (2 : ZMod 1413847964293) ^ 32935332) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 1262862721721 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 1413847964293) ^ 131741331 = 795037151556 := by
        calc
          (2 : ZMod 1413847964293) ^ 131741331 = (2 : ZMod 1413847964293) ^ (65870665 + 65870665 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 65870665 * (2 : ZMod 1413847964293) ^ 65870665) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 795037151556 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 1413847964293) ^ 263482662 = 376229269403 := by
        calc
          (2 : ZMod 1413847964293) ^ 263482662 = (2 : ZMod 1413847964293) ^ (131741331 + 131741331) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 131741331 * (2 : ZMod 1413847964293) ^ 131741331 := by rw [pow_add]
          _ = 376229269403 := by rw [factor_2_26]; decide
      have factor_2_28 : (2 : ZMod 1413847964293) ^ 526965324 = 1156690333748 := by
        calc
          (2 : ZMod 1413847964293) ^ 526965324 = (2 : ZMod 1413847964293) ^ (263482662 + 263482662) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 263482662 * (2 : ZMod 1413847964293) ^ 263482662 := by rw [pow_add]
          _ = 1156690333748 := by rw [factor_2_27]; decide
      change (2 : ZMod 1413847964293) ^ 526965324 ≠ 1
      rw [factor_2_28]
      decide
    ·
      have factor_3_0 : (2 : ZMod 1413847964293) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 1413847964293) ^ 3 = 8 := by
        calc
          (2 : ZMod 1413847964293) ^ 3 = (2 : ZMod 1413847964293) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 1 * (2 : ZMod 1413847964293) ^ 1) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 1413847964293) ^ 7 = 128 := by
        calc
          (2 : ZMod 1413847964293) ^ 7 = (2 : ZMod 1413847964293) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 3 * (2 : ZMod 1413847964293) ^ 3) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 1413847964293) ^ 15 = 32768 := by
        calc
          (2 : ZMod 1413847964293) ^ 15 = (2 : ZMod 1413847964293) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 7 * (2 : ZMod 1413847964293) ^ 7) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 1413847964293) ^ 31 = 2147483648 := by
        calc
          (2 : ZMod 1413847964293) ^ 31 = (2 : ZMod 1413847964293) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 15 * (2 : ZMod 1413847964293) ^ 15) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 2147483648 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 1413847964293) ^ 62 = 970040373383 := by
        calc
          (2 : ZMod 1413847964293) ^ 62 = (2 : ZMod 1413847964293) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 31 * (2 : ZMod 1413847964293) ^ 31 := by rw [pow_add]
          _ = 970040373383 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 1413847964293) ^ 125 = 1144739281293 := by
        calc
          (2 : ZMod 1413847964293) ^ 125 = (2 : ZMod 1413847964293) ^ (62 + 62 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 62 * (2 : ZMod 1413847964293) ^ 62) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 1144739281293 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 1413847964293) ^ 251 = 334822745295 := by
        calc
          (2 : ZMod 1413847964293) ^ 251 = (2 : ZMod 1413847964293) ^ (125 + 125 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 125 * (2 : ZMod 1413847964293) ^ 125) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 334822745295 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 1413847964293) ^ 503 = 314501530617 := by
        calc
          (2 : ZMod 1413847964293) ^ 503 = (2 : ZMod 1413847964293) ^ (251 + 251 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 251 * (2 : ZMod 1413847964293) ^ 251) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 314501530617 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 1413847964293) ^ 1006 = 639187884085 := by
        calc
          (2 : ZMod 1413847964293) ^ 1006 = (2 : ZMod 1413847964293) ^ (503 + 503) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 503 * (2 : ZMod 1413847964293) ^ 503 := by rw [pow_add]
          _ = 639187884085 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 1413847964293) ^ 2012 = 1157969282216 := by
        calc
          (2 : ZMod 1413847964293) ^ 2012 = (2 : ZMod 1413847964293) ^ (1006 + 1006) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 1006 * (2 : ZMod 1413847964293) ^ 1006 := by rw [pow_add]
          _ = 1157969282216 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 1413847964293) ^ 4024 = 383871816029 := by
        calc
          (2 : ZMod 1413847964293) ^ 4024 = (2 : ZMod 1413847964293) ^ (2012 + 2012) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 2012 * (2 : ZMod 1413847964293) ^ 2012 := by rw [pow_add]
          _ = 383871816029 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 1413847964293) ^ 8049 = 670675711496 := by
        calc
          (2 : ZMod 1413847964293) ^ 8049 = (2 : ZMod 1413847964293) ^ (4024 + 4024 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = ((2 : ZMod 1413847964293) ^ 4024 * (2 : ZMod 1413847964293) ^ 4024) * (2 : ZMod 1413847964293) := by rw [pow_succ, pow_add]
          _ = 670675711496 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 1413847964293) ^ 16098 = 779218375070 := by
        calc
          (2 : ZMod 1413847964293) ^ 16098 = (2 : ZMod 1413847964293) ^ (8049 + 8049) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 8049 * (2 : ZMod 1413847964293) ^ 8049 := by rw [pow_add]
          _ = 779218375070 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 1413847964293) ^ 32196 = 432795119699 := by
        calc
          (2 : ZMod 1413847964293) ^ 32196 = (2 : ZMod 1413847964293) ^ (16098 + 16098) :=
            congrArg (fun n : ℕ => (2 : ZMod 1413847964293) ^ n) (by norm_num)
          _ = (2 : ZMod 1413847964293) ^ 16098 * (2 : ZMod 1413847964293) ^ 16098 := by rw [pow_add]
          _ = 432795119699 := by rw [factor_3_13]; decide
      change (2 : ZMod 1413847964293) ^ 32196 ≠ 1
      rw [factor_3_14]
      decide

#print axioms prime_lucas_1413847964293

end TotientTailPeriodKiller
end Erdos249257
