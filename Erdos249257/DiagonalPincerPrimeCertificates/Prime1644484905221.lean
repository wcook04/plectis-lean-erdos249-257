import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime344034499

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1644484905221 : Nat.Prime 1644484905221 := by
  apply lucas_primality 1644484905221 (2 : ZMod 1644484905221)
  ·
      have fermat_0 : (2 : ZMod 1644484905221) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 1644484905221) ^ 2 = 4 := by
        calc
          (2 : ZMod 1644484905221) ^ 2 = (2 : ZMod 1644484905221) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 1 * (2 : ZMod 1644484905221) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 1644484905221) ^ 5 = 32 := by
        calc
          (2 : ZMod 1644484905221) ^ 5 = (2 : ZMod 1644484905221) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 2 * (2 : ZMod 1644484905221) ^ 2) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 1644484905221) ^ 11 = 2048 := by
        calc
          (2 : ZMod 1644484905221) ^ 11 = (2 : ZMod 1644484905221) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 5 * (2 : ZMod 1644484905221) ^ 5) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 1644484905221) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 1644484905221) ^ 23 = (2 : ZMod 1644484905221) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 11 * (2 : ZMod 1644484905221) ^ 11) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 1644484905221) ^ 47 = 956271411543 := by
        calc
          (2 : ZMod 1644484905221) ^ 47 = (2 : ZMod 1644484905221) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 23 * (2 : ZMod 1644484905221) ^ 23) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 956271411543 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 1644484905221) ^ 95 = 775267237160 := by
        calc
          (2 : ZMod 1644484905221) ^ 95 = (2 : ZMod 1644484905221) ^ (47 + 47 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 47 * (2 : ZMod 1644484905221) ^ 47) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 775267237160 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 1644484905221) ^ 191 = 997499236451 := by
        calc
          (2 : ZMod 1644484905221) ^ 191 = (2 : ZMod 1644484905221) ^ (95 + 95 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 95 * (2 : ZMod 1644484905221) ^ 95) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 997499236451 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 1644484905221) ^ 382 = 365222265402 := by
        calc
          (2 : ZMod 1644484905221) ^ 382 = (2 : ZMod 1644484905221) ^ (191 + 191) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 191 * (2 : ZMod 1644484905221) ^ 191 := by rw [pow_add]
          _ = 365222265402 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 1644484905221) ^ 765 = 1244540293486 := by
        calc
          (2 : ZMod 1644484905221) ^ 765 = (2 : ZMod 1644484905221) ^ (382 + 382 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 382 * (2 : ZMod 1644484905221) ^ 382) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 1244540293486 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 1644484905221) ^ 1531 = 1216455693154 := by
        calc
          (2 : ZMod 1644484905221) ^ 1531 = (2 : ZMod 1644484905221) ^ (765 + 765 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 765 * (2 : ZMod 1644484905221) ^ 765) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 1216455693154 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 1644484905221) ^ 3063 = 696580302148 := by
        calc
          (2 : ZMod 1644484905221) ^ 3063 = (2 : ZMod 1644484905221) ^ (1531 + 1531 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 1531 * (2 : ZMod 1644484905221) ^ 1531) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 696580302148 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 1644484905221) ^ 6126 = 1589445539428 := by
        calc
          (2 : ZMod 1644484905221) ^ 6126 = (2 : ZMod 1644484905221) ^ (3063 + 3063) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 3063 * (2 : ZMod 1644484905221) ^ 3063 := by rw [pow_add]
          _ = 1589445539428 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 1644484905221) ^ 12252 = 611516120612 := by
        calc
          (2 : ZMod 1644484905221) ^ 12252 = (2 : ZMod 1644484905221) ^ (6126 + 6126) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 6126 * (2 : ZMod 1644484905221) ^ 6126 := by rw [pow_add]
          _ = 611516120612 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 1644484905221) ^ 24504 = 1313585020829 := by
        calc
          (2 : ZMod 1644484905221) ^ 24504 = (2 : ZMod 1644484905221) ^ (12252 + 12252) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 12252 * (2 : ZMod 1644484905221) ^ 12252 := by rw [pow_add]
          _ = 1313585020829 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 1644484905221) ^ 49009 = 639798375853 := by
        calc
          (2 : ZMod 1644484905221) ^ 49009 = (2 : ZMod 1644484905221) ^ (24504 + 24504 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 24504 * (2 : ZMod 1644484905221) ^ 24504) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 639798375853 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 1644484905221) ^ 98018 = 1637910655115 := by
        calc
          (2 : ZMod 1644484905221) ^ 98018 = (2 : ZMod 1644484905221) ^ (49009 + 49009) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 49009 * (2 : ZMod 1644484905221) ^ 49009 := by rw [pow_add]
          _ = 1637910655115 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 1644484905221) ^ 196037 = 467507862751 := by
        calc
          (2 : ZMod 1644484905221) ^ 196037 = (2 : ZMod 1644484905221) ^ (98018 + 98018 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 98018 * (2 : ZMod 1644484905221) ^ 98018) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 467507862751 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 1644484905221) ^ 392075 = 960275125248 := by
        calc
          (2 : ZMod 1644484905221) ^ 392075 = (2 : ZMod 1644484905221) ^ (196037 + 196037 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 196037 * (2 : ZMod 1644484905221) ^ 196037) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 960275125248 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 1644484905221) ^ 784151 = 860021737770 := by
        calc
          (2 : ZMod 1644484905221) ^ 784151 = (2 : ZMod 1644484905221) ^ (392075 + 392075 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 392075 * (2 : ZMod 1644484905221) ^ 392075) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 860021737770 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 1644484905221) ^ 1568303 = 1388929337046 := by
        calc
          (2 : ZMod 1644484905221) ^ 1568303 = (2 : ZMod 1644484905221) ^ (784151 + 784151 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 784151 * (2 : ZMod 1644484905221) ^ 784151) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 1388929337046 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 1644484905221) ^ 3136606 = 292763364346 := by
        calc
          (2 : ZMod 1644484905221) ^ 3136606 = (2 : ZMod 1644484905221) ^ (1568303 + 1568303) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 1568303 * (2 : ZMod 1644484905221) ^ 1568303 := by rw [pow_add]
          _ = 292763364346 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 1644484905221) ^ 6273212 = 570730663632 := by
        calc
          (2 : ZMod 1644484905221) ^ 6273212 = (2 : ZMod 1644484905221) ^ (3136606 + 3136606) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 3136606 * (2 : ZMod 1644484905221) ^ 3136606 := by rw [pow_add]
          _ = 570730663632 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 1644484905221) ^ 12546424 = 1585441932678 := by
        calc
          (2 : ZMod 1644484905221) ^ 12546424 = (2 : ZMod 1644484905221) ^ (6273212 + 6273212) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 6273212 * (2 : ZMod 1644484905221) ^ 6273212 := by rw [pow_add]
          _ = 1585441932678 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 1644484905221) ^ 25092848 = 858750126010 := by
        calc
          (2 : ZMod 1644484905221) ^ 25092848 = (2 : ZMod 1644484905221) ^ (12546424 + 12546424) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 12546424 * (2 : ZMod 1644484905221) ^ 12546424 := by rw [pow_add]
          _ = 858750126010 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 1644484905221) ^ 50185696 = 9606190777 := by
        calc
          (2 : ZMod 1644484905221) ^ 50185696 = (2 : ZMod 1644484905221) ^ (25092848 + 25092848) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 25092848 * (2 : ZMod 1644484905221) ^ 25092848 := by rw [pow_add]
          _ = 9606190777 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 1644484905221) ^ 100371393 = 1287138995644 := by
        calc
          (2 : ZMod 1644484905221) ^ 100371393 = (2 : ZMod 1644484905221) ^ (50185696 + 50185696 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 50185696 * (2 : ZMod 1644484905221) ^ 50185696) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 1287138995644 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 1644484905221) ^ 200742786 = 290145100627 := by
        calc
          (2 : ZMod 1644484905221) ^ 200742786 = (2 : ZMod 1644484905221) ^ (100371393 + 100371393) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 100371393 * (2 : ZMod 1644484905221) ^ 100371393 := by rw [pow_add]
          _ = 290145100627 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 1644484905221) ^ 401485572 = 1448108079662 := by
        calc
          (2 : ZMod 1644484905221) ^ 401485572 = (2 : ZMod 1644484905221) ^ (200742786 + 200742786) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 200742786 * (2 : ZMod 1644484905221) ^ 200742786 := by rw [pow_add]
          _ = 1448108079662 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 1644484905221) ^ 802971145 = 609373685542 := by
        calc
          (2 : ZMod 1644484905221) ^ 802971145 = (2 : ZMod 1644484905221) ^ (401485572 + 401485572 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 401485572 * (2 : ZMod 1644484905221) ^ 401485572) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 609373685542 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 1644484905221) ^ 1605942290 = 1250513450189 := by
        calc
          (2 : ZMod 1644484905221) ^ 1605942290 = (2 : ZMod 1644484905221) ^ (802971145 + 802971145) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 802971145 * (2 : ZMod 1644484905221) ^ 802971145 := by rw [pow_add]
          _ = 1250513450189 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 1644484905221) ^ 3211884580 = 726103716079 := by
        calc
          (2 : ZMod 1644484905221) ^ 3211884580 = (2 : ZMod 1644484905221) ^ (1605942290 + 1605942290) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 1605942290 * (2 : ZMod 1644484905221) ^ 1605942290 := by rw [pow_add]
          _ = 726103716079 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 1644484905221) ^ 6423769161 = 359229851676 := by
        calc
          (2 : ZMod 1644484905221) ^ 6423769161 = (2 : ZMod 1644484905221) ^ (3211884580 + 3211884580 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 3211884580 * (2 : ZMod 1644484905221) ^ 3211884580) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 359229851676 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 1644484905221) ^ 12847538322 = 1058280964884 := by
        calc
          (2 : ZMod 1644484905221) ^ 12847538322 = (2 : ZMod 1644484905221) ^ (6423769161 + 6423769161) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 6423769161 * (2 : ZMod 1644484905221) ^ 6423769161 := by rw [pow_add]
          _ = 1058280964884 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 1644484905221) ^ 25695076644 = 659748042190 := by
        calc
          (2 : ZMod 1644484905221) ^ 25695076644 = (2 : ZMod 1644484905221) ^ (12847538322 + 12847538322) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 12847538322 * (2 : ZMod 1644484905221) ^ 12847538322 := by rw [pow_add]
          _ = 659748042190 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 1644484905221) ^ 51390153288 = 280927547283 := by
        calc
          (2 : ZMod 1644484905221) ^ 51390153288 = (2 : ZMod 1644484905221) ^ (25695076644 + 25695076644) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 25695076644 * (2 : ZMod 1644484905221) ^ 25695076644 := by rw [pow_add]
          _ = 280927547283 := by rw [fermat_34]; decide
      have fermat_36 : (2 : ZMod 1644484905221) ^ 102780306576 = 1546594097832 := by
        calc
          (2 : ZMod 1644484905221) ^ 102780306576 = (2 : ZMod 1644484905221) ^ (51390153288 + 51390153288) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 51390153288 * (2 : ZMod 1644484905221) ^ 51390153288 := by rw [pow_add]
          _ = 1546594097832 := by rw [fermat_35]; decide
      have fermat_37 : (2 : ZMod 1644484905221) ^ 205560613152 = 776382532793 := by
        calc
          (2 : ZMod 1644484905221) ^ 205560613152 = (2 : ZMod 1644484905221) ^ (102780306576 + 102780306576) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 102780306576 * (2 : ZMod 1644484905221) ^ 102780306576 := by rw [pow_add]
          _ = 776382532793 := by rw [fermat_36]; decide
      have fermat_38 : (2 : ZMod 1644484905221) ^ 411121226305 = 91719839634 := by
        calc
          (2 : ZMod 1644484905221) ^ 411121226305 = (2 : ZMod 1644484905221) ^ (205560613152 + 205560613152 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 205560613152 * (2 : ZMod 1644484905221) ^ 205560613152) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 91719839634 := by rw [fermat_37]; decide
      have fermat_39 : (2 : ZMod 1644484905221) ^ 822242452610 = 1644484905220 := by
        calc
          (2 : ZMod 1644484905221) ^ 822242452610 = (2 : ZMod 1644484905221) ^ (411121226305 + 411121226305) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 411121226305 * (2 : ZMod 1644484905221) ^ 411121226305 := by rw [pow_add]
          _ = 1644484905220 := by rw [fermat_38]; decide
      have fermat_40 : (2 : ZMod 1644484905221) ^ 1644484905220 = 1 := by
        calc
          (2 : ZMod 1644484905221) ^ 1644484905220 = (2 : ZMod 1644484905221) ^ (822242452610 + 822242452610) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 822242452610 * (2 : ZMod 1644484905221) ^ 822242452610 := by rw [pow_add]
          _ = 1 := by rw [fermat_39]; decide
      simpa using fermat_40
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (239, 1), (344034499, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (239, 1), (344034499, 1)] : List FactorBlock).map factorBlockValue).prod = 1644484905221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_344034499) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 1644484905221) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 1644484905221) ^ 2 = 4 := by
        calc
          (2 : ZMod 1644484905221) ^ 2 = (2 : ZMod 1644484905221) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 1 * (2 : ZMod 1644484905221) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 1644484905221) ^ 5 = 32 := by
        calc
          (2 : ZMod 1644484905221) ^ 5 = (2 : ZMod 1644484905221) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 2 * (2 : ZMod 1644484905221) ^ 2) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 1644484905221) ^ 11 = 2048 := by
        calc
          (2 : ZMod 1644484905221) ^ 11 = (2 : ZMod 1644484905221) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 5 * (2 : ZMod 1644484905221) ^ 5) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 1644484905221) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 1644484905221) ^ 23 = (2 : ZMod 1644484905221) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 11 * (2 : ZMod 1644484905221) ^ 11) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 1644484905221) ^ 47 = 956271411543 := by
        calc
          (2 : ZMod 1644484905221) ^ 47 = (2 : ZMod 1644484905221) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 23 * (2 : ZMod 1644484905221) ^ 23) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 956271411543 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 1644484905221) ^ 95 = 775267237160 := by
        calc
          (2 : ZMod 1644484905221) ^ 95 = (2 : ZMod 1644484905221) ^ (47 + 47 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 47 * (2 : ZMod 1644484905221) ^ 47) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 775267237160 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 1644484905221) ^ 191 = 997499236451 := by
        calc
          (2 : ZMod 1644484905221) ^ 191 = (2 : ZMod 1644484905221) ^ (95 + 95 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 95 * (2 : ZMod 1644484905221) ^ 95) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 997499236451 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 1644484905221) ^ 382 = 365222265402 := by
        calc
          (2 : ZMod 1644484905221) ^ 382 = (2 : ZMod 1644484905221) ^ (191 + 191) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 191 * (2 : ZMod 1644484905221) ^ 191 := by rw [pow_add]
          _ = 365222265402 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 1644484905221) ^ 765 = 1244540293486 := by
        calc
          (2 : ZMod 1644484905221) ^ 765 = (2 : ZMod 1644484905221) ^ (382 + 382 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 382 * (2 : ZMod 1644484905221) ^ 382) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 1244540293486 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 1644484905221) ^ 1531 = 1216455693154 := by
        calc
          (2 : ZMod 1644484905221) ^ 1531 = (2 : ZMod 1644484905221) ^ (765 + 765 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 765 * (2 : ZMod 1644484905221) ^ 765) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 1216455693154 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 1644484905221) ^ 3063 = 696580302148 := by
        calc
          (2 : ZMod 1644484905221) ^ 3063 = (2 : ZMod 1644484905221) ^ (1531 + 1531 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 1531 * (2 : ZMod 1644484905221) ^ 1531) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 696580302148 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 1644484905221) ^ 6126 = 1589445539428 := by
        calc
          (2 : ZMod 1644484905221) ^ 6126 = (2 : ZMod 1644484905221) ^ (3063 + 3063) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 3063 * (2 : ZMod 1644484905221) ^ 3063 := by rw [pow_add]
          _ = 1589445539428 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 1644484905221) ^ 12252 = 611516120612 := by
        calc
          (2 : ZMod 1644484905221) ^ 12252 = (2 : ZMod 1644484905221) ^ (6126 + 6126) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 6126 * (2 : ZMod 1644484905221) ^ 6126 := by rw [pow_add]
          _ = 611516120612 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 1644484905221) ^ 24504 = 1313585020829 := by
        calc
          (2 : ZMod 1644484905221) ^ 24504 = (2 : ZMod 1644484905221) ^ (12252 + 12252) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 12252 * (2 : ZMod 1644484905221) ^ 12252 := by rw [pow_add]
          _ = 1313585020829 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 1644484905221) ^ 49009 = 639798375853 := by
        calc
          (2 : ZMod 1644484905221) ^ 49009 = (2 : ZMod 1644484905221) ^ (24504 + 24504 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 24504 * (2 : ZMod 1644484905221) ^ 24504) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 639798375853 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 1644484905221) ^ 98018 = 1637910655115 := by
        calc
          (2 : ZMod 1644484905221) ^ 98018 = (2 : ZMod 1644484905221) ^ (49009 + 49009) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 49009 * (2 : ZMod 1644484905221) ^ 49009 := by rw [pow_add]
          _ = 1637910655115 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 1644484905221) ^ 196037 = 467507862751 := by
        calc
          (2 : ZMod 1644484905221) ^ 196037 = (2 : ZMod 1644484905221) ^ (98018 + 98018 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 98018 * (2 : ZMod 1644484905221) ^ 98018) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 467507862751 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 1644484905221) ^ 392075 = 960275125248 := by
        calc
          (2 : ZMod 1644484905221) ^ 392075 = (2 : ZMod 1644484905221) ^ (196037 + 196037 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 196037 * (2 : ZMod 1644484905221) ^ 196037) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 960275125248 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 1644484905221) ^ 784151 = 860021737770 := by
        calc
          (2 : ZMod 1644484905221) ^ 784151 = (2 : ZMod 1644484905221) ^ (392075 + 392075 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 392075 * (2 : ZMod 1644484905221) ^ 392075) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 860021737770 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 1644484905221) ^ 1568303 = 1388929337046 := by
        calc
          (2 : ZMod 1644484905221) ^ 1568303 = (2 : ZMod 1644484905221) ^ (784151 + 784151 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 784151 * (2 : ZMod 1644484905221) ^ 784151) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 1388929337046 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 1644484905221) ^ 3136606 = 292763364346 := by
        calc
          (2 : ZMod 1644484905221) ^ 3136606 = (2 : ZMod 1644484905221) ^ (1568303 + 1568303) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 1568303 * (2 : ZMod 1644484905221) ^ 1568303 := by rw [pow_add]
          _ = 292763364346 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 1644484905221) ^ 6273212 = 570730663632 := by
        calc
          (2 : ZMod 1644484905221) ^ 6273212 = (2 : ZMod 1644484905221) ^ (3136606 + 3136606) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 3136606 * (2 : ZMod 1644484905221) ^ 3136606 := by rw [pow_add]
          _ = 570730663632 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 1644484905221) ^ 12546424 = 1585441932678 := by
        calc
          (2 : ZMod 1644484905221) ^ 12546424 = (2 : ZMod 1644484905221) ^ (6273212 + 6273212) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 6273212 * (2 : ZMod 1644484905221) ^ 6273212 := by rw [pow_add]
          _ = 1585441932678 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 1644484905221) ^ 25092848 = 858750126010 := by
        calc
          (2 : ZMod 1644484905221) ^ 25092848 = (2 : ZMod 1644484905221) ^ (12546424 + 12546424) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 12546424 * (2 : ZMod 1644484905221) ^ 12546424 := by rw [pow_add]
          _ = 858750126010 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 1644484905221) ^ 50185696 = 9606190777 := by
        calc
          (2 : ZMod 1644484905221) ^ 50185696 = (2 : ZMod 1644484905221) ^ (25092848 + 25092848) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 25092848 * (2 : ZMod 1644484905221) ^ 25092848 := by rw [pow_add]
          _ = 9606190777 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 1644484905221) ^ 100371393 = 1287138995644 := by
        calc
          (2 : ZMod 1644484905221) ^ 100371393 = (2 : ZMod 1644484905221) ^ (50185696 + 50185696 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 50185696 * (2 : ZMod 1644484905221) ^ 50185696) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 1287138995644 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 1644484905221) ^ 200742786 = 290145100627 := by
        calc
          (2 : ZMod 1644484905221) ^ 200742786 = (2 : ZMod 1644484905221) ^ (100371393 + 100371393) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 100371393 * (2 : ZMod 1644484905221) ^ 100371393 := by rw [pow_add]
          _ = 290145100627 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 1644484905221) ^ 401485572 = 1448108079662 := by
        calc
          (2 : ZMod 1644484905221) ^ 401485572 = (2 : ZMod 1644484905221) ^ (200742786 + 200742786) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 200742786 * (2 : ZMod 1644484905221) ^ 200742786 := by rw [pow_add]
          _ = 1448108079662 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 1644484905221) ^ 802971145 = 609373685542 := by
        calc
          (2 : ZMod 1644484905221) ^ 802971145 = (2 : ZMod 1644484905221) ^ (401485572 + 401485572 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 401485572 * (2 : ZMod 1644484905221) ^ 401485572) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 609373685542 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 1644484905221) ^ 1605942290 = 1250513450189 := by
        calc
          (2 : ZMod 1644484905221) ^ 1605942290 = (2 : ZMod 1644484905221) ^ (802971145 + 802971145) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 802971145 * (2 : ZMod 1644484905221) ^ 802971145 := by rw [pow_add]
          _ = 1250513450189 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 1644484905221) ^ 3211884580 = 726103716079 := by
        calc
          (2 : ZMod 1644484905221) ^ 3211884580 = (2 : ZMod 1644484905221) ^ (1605942290 + 1605942290) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 1605942290 * (2 : ZMod 1644484905221) ^ 1605942290 := by rw [pow_add]
          _ = 726103716079 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 1644484905221) ^ 6423769161 = 359229851676 := by
        calc
          (2 : ZMod 1644484905221) ^ 6423769161 = (2 : ZMod 1644484905221) ^ (3211884580 + 3211884580 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 3211884580 * (2 : ZMod 1644484905221) ^ 3211884580) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 359229851676 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 1644484905221) ^ 12847538322 = 1058280964884 := by
        calc
          (2 : ZMod 1644484905221) ^ 12847538322 = (2 : ZMod 1644484905221) ^ (6423769161 + 6423769161) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 6423769161 * (2 : ZMod 1644484905221) ^ 6423769161 := by rw [pow_add]
          _ = 1058280964884 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 1644484905221) ^ 25695076644 = 659748042190 := by
        calc
          (2 : ZMod 1644484905221) ^ 25695076644 = (2 : ZMod 1644484905221) ^ (12847538322 + 12847538322) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 12847538322 * (2 : ZMod 1644484905221) ^ 12847538322 := by rw [pow_add]
          _ = 659748042190 := by rw [factor_0_33]; decide
      have factor_0_35 : (2 : ZMod 1644484905221) ^ 51390153288 = 280927547283 := by
        calc
          (2 : ZMod 1644484905221) ^ 51390153288 = (2 : ZMod 1644484905221) ^ (25695076644 + 25695076644) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 25695076644 * (2 : ZMod 1644484905221) ^ 25695076644 := by rw [pow_add]
          _ = 280927547283 := by rw [factor_0_34]; decide
      have factor_0_36 : (2 : ZMod 1644484905221) ^ 102780306576 = 1546594097832 := by
        calc
          (2 : ZMod 1644484905221) ^ 102780306576 = (2 : ZMod 1644484905221) ^ (51390153288 + 51390153288) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 51390153288 * (2 : ZMod 1644484905221) ^ 51390153288 := by rw [pow_add]
          _ = 1546594097832 := by rw [factor_0_35]; decide
      have factor_0_37 : (2 : ZMod 1644484905221) ^ 205560613152 = 776382532793 := by
        calc
          (2 : ZMod 1644484905221) ^ 205560613152 = (2 : ZMod 1644484905221) ^ (102780306576 + 102780306576) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 102780306576 * (2 : ZMod 1644484905221) ^ 102780306576 := by rw [pow_add]
          _ = 776382532793 := by rw [factor_0_36]; decide
      have factor_0_38 : (2 : ZMod 1644484905221) ^ 411121226305 = 91719839634 := by
        calc
          (2 : ZMod 1644484905221) ^ 411121226305 = (2 : ZMod 1644484905221) ^ (205560613152 + 205560613152 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 205560613152 * (2 : ZMod 1644484905221) ^ 205560613152) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 91719839634 := by rw [factor_0_37]; decide
      have factor_0_39 : (2 : ZMod 1644484905221) ^ 822242452610 = 1644484905220 := by
        calc
          (2 : ZMod 1644484905221) ^ 822242452610 = (2 : ZMod 1644484905221) ^ (411121226305 + 411121226305) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 411121226305 * (2 : ZMod 1644484905221) ^ 411121226305 := by rw [pow_add]
          _ = 1644484905220 := by rw [factor_0_38]; decide
      change (2 : ZMod 1644484905221) ^ 822242452610 ≠ 1
      rw [factor_0_39]
      decide
    ·
      have factor_1_0 : (2 : ZMod 1644484905221) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 1644484905221) ^ 2 = 4 := by
        calc
          (2 : ZMod 1644484905221) ^ 2 = (2 : ZMod 1644484905221) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 1 * (2 : ZMod 1644484905221) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 1644484905221) ^ 4 = 16 := by
        calc
          (2 : ZMod 1644484905221) ^ 4 = (2 : ZMod 1644484905221) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 2 * (2 : ZMod 1644484905221) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 1644484905221) ^ 9 = 512 := by
        calc
          (2 : ZMod 1644484905221) ^ 9 = (2 : ZMod 1644484905221) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 4 * (2 : ZMod 1644484905221) ^ 4) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 1644484905221) ^ 19 = 524288 := by
        calc
          (2 : ZMod 1644484905221) ^ 19 = (2 : ZMod 1644484905221) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 9 * (2 : ZMod 1644484905221) ^ 9) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 524288 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 1644484905221) ^ 38 = 274877906944 := by
        calc
          (2 : ZMod 1644484905221) ^ 38 = (2 : ZMod 1644484905221) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 19 * (2 : ZMod 1644484905221) ^ 19 := by rw [pow_add]
          _ = 274877906944 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 1644484905221) ^ 76 = 166191412898 := by
        calc
          (2 : ZMod 1644484905221) ^ 76 = (2 : ZMod 1644484905221) ^ (38 + 38) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 38 * (2 : ZMod 1644484905221) ^ 38 := by rw [pow_add]
          _ = 166191412898 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 1644484905221) ^ 153 = 394760517269 := by
        calc
          (2 : ZMod 1644484905221) ^ 153 = (2 : ZMod 1644484905221) ^ (76 + 76 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 76 * (2 : ZMod 1644484905221) ^ 76) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 394760517269 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 1644484905221) ^ 306 = 676775679648 := by
        calc
          (2 : ZMod 1644484905221) ^ 306 = (2 : ZMod 1644484905221) ^ (153 + 153) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 153 * (2 : ZMod 1644484905221) ^ 153 := by rw [pow_add]
          _ = 676775679648 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 1644484905221) ^ 612 = 1447715185875 := by
        calc
          (2 : ZMod 1644484905221) ^ 612 = (2 : ZMod 1644484905221) ^ (306 + 306) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 306 * (2 : ZMod 1644484905221) ^ 306 := by rw [pow_add]
          _ = 1447715185875 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 1644484905221) ^ 1225 = 364475499697 := by
        calc
          (2 : ZMod 1644484905221) ^ 1225 = (2 : ZMod 1644484905221) ^ (612 + 612 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 612 * (2 : ZMod 1644484905221) ^ 612) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 364475499697 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 1644484905221) ^ 2450 = 34079049810 := by
        calc
          (2 : ZMod 1644484905221) ^ 2450 = (2 : ZMod 1644484905221) ^ (1225 + 1225) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 1225 * (2 : ZMod 1644484905221) ^ 1225 := by rw [pow_add]
          _ = 34079049810 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 1644484905221) ^ 4900 = 32759836027 := by
        calc
          (2 : ZMod 1644484905221) ^ 4900 = (2 : ZMod 1644484905221) ^ (2450 + 2450) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 2450 * (2 : ZMod 1644484905221) ^ 2450 := by rw [pow_add]
          _ = 32759836027 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 1644484905221) ^ 9801 = 1549755152251 := by
        calc
          (2 : ZMod 1644484905221) ^ 9801 = (2 : ZMod 1644484905221) ^ (4900 + 4900 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 4900 * (2 : ZMod 1644484905221) ^ 4900) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 1549755152251 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 1644484905221) ^ 19603 = 1642248771288 := by
        calc
          (2 : ZMod 1644484905221) ^ 19603 = (2 : ZMod 1644484905221) ^ (9801 + 9801 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 9801 * (2 : ZMod 1644484905221) ^ 9801) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 1642248771288 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 1644484905221) ^ 39207 = 323356681888 := by
        calc
          (2 : ZMod 1644484905221) ^ 39207 = (2 : ZMod 1644484905221) ^ (19603 + 19603 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 19603 * (2 : ZMod 1644484905221) ^ 19603) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 323356681888 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 1644484905221) ^ 78415 = 456104728321 := by
        calc
          (2 : ZMod 1644484905221) ^ 78415 = (2 : ZMod 1644484905221) ^ (39207 + 39207 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 39207 * (2 : ZMod 1644484905221) ^ 39207) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 456104728321 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 1644484905221) ^ 156830 = 1450716263939 := by
        calc
          (2 : ZMod 1644484905221) ^ 156830 = (2 : ZMod 1644484905221) ^ (78415 + 78415) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 78415 * (2 : ZMod 1644484905221) ^ 78415 := by rw [pow_add]
          _ = 1450716263939 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 1644484905221) ^ 313660 = 1034739632671 := by
        calc
          (2 : ZMod 1644484905221) ^ 313660 = (2 : ZMod 1644484905221) ^ (156830 + 156830) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 156830 * (2 : ZMod 1644484905221) ^ 156830 := by rw [pow_add]
          _ = 1034739632671 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 1644484905221) ^ 627321 = 273120858137 := by
        calc
          (2 : ZMod 1644484905221) ^ 627321 = (2 : ZMod 1644484905221) ^ (313660 + 313660 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 313660 * (2 : ZMod 1644484905221) ^ 313660) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 273120858137 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 1644484905221) ^ 1254642 = 1266427365409 := by
        calc
          (2 : ZMod 1644484905221) ^ 1254642 = (2 : ZMod 1644484905221) ^ (627321 + 627321) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 627321 * (2 : ZMod 1644484905221) ^ 627321 := by rw [pow_add]
          _ = 1266427365409 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 1644484905221) ^ 2509284 = 822512333409 := by
        calc
          (2 : ZMod 1644484905221) ^ 2509284 = (2 : ZMod 1644484905221) ^ (1254642 + 1254642) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 1254642 * (2 : ZMod 1644484905221) ^ 1254642 := by rw [pow_add]
          _ = 822512333409 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 1644484905221) ^ 5018569 = 351166161193 := by
        calc
          (2 : ZMod 1644484905221) ^ 5018569 = (2 : ZMod 1644484905221) ^ (2509284 + 2509284 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 2509284 * (2 : ZMod 1644484905221) ^ 2509284) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 351166161193 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 1644484905221) ^ 10037139 = 1297326464353 := by
        calc
          (2 : ZMod 1644484905221) ^ 10037139 = (2 : ZMod 1644484905221) ^ (5018569 + 5018569 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 5018569 * (2 : ZMod 1644484905221) ^ 5018569) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 1297326464353 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 1644484905221) ^ 20074278 = 194653669487 := by
        calc
          (2 : ZMod 1644484905221) ^ 20074278 = (2 : ZMod 1644484905221) ^ (10037139 + 10037139) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 10037139 * (2 : ZMod 1644484905221) ^ 10037139 := by rw [pow_add]
          _ = 194653669487 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 1644484905221) ^ 40148557 = 1380800755975 := by
        calc
          (2 : ZMod 1644484905221) ^ 40148557 = (2 : ZMod 1644484905221) ^ (20074278 + 20074278 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 20074278 * (2 : ZMod 1644484905221) ^ 20074278) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 1380800755975 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 1644484905221) ^ 80297114 = 102945095536 := by
        calc
          (2 : ZMod 1644484905221) ^ 80297114 = (2 : ZMod 1644484905221) ^ (40148557 + 40148557) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 40148557 * (2 : ZMod 1644484905221) ^ 40148557 := by rw [pow_add]
          _ = 102945095536 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 1644484905221) ^ 160594229 = 1624237161865 := by
        calc
          (2 : ZMod 1644484905221) ^ 160594229 = (2 : ZMod 1644484905221) ^ (80297114 + 80297114 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 80297114 * (2 : ZMod 1644484905221) ^ 80297114) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 1624237161865 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 1644484905221) ^ 321188458 = 1269235795274 := by
        calc
          (2 : ZMod 1644484905221) ^ 321188458 = (2 : ZMod 1644484905221) ^ (160594229 + 160594229) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 160594229 * (2 : ZMod 1644484905221) ^ 160594229 := by rw [pow_add]
          _ = 1269235795274 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 1644484905221) ^ 642376916 = 1121244907102 := by
        calc
          (2 : ZMod 1644484905221) ^ 642376916 = (2 : ZMod 1644484905221) ^ (321188458 + 321188458) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 321188458 * (2 : ZMod 1644484905221) ^ 321188458 := by rw [pow_add]
          _ = 1121244907102 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 1644484905221) ^ 1284753832 = 238733811284 := by
        calc
          (2 : ZMod 1644484905221) ^ 1284753832 = (2 : ZMod 1644484905221) ^ (642376916 + 642376916) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 642376916 * (2 : ZMod 1644484905221) ^ 642376916 := by rw [pow_add]
          _ = 238733811284 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 1644484905221) ^ 2569507664 = 1500006421783 := by
        calc
          (2 : ZMod 1644484905221) ^ 2569507664 = (2 : ZMod 1644484905221) ^ (1284753832 + 1284753832) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 1284753832 * (2 : ZMod 1644484905221) ^ 1284753832 := by rw [pow_add]
          _ = 1500006421783 := by rw [factor_1_30]; decide
      have factor_1_32 : (2 : ZMod 1644484905221) ^ 5139015328 = 752034240723 := by
        calc
          (2 : ZMod 1644484905221) ^ 5139015328 = (2 : ZMod 1644484905221) ^ (2569507664 + 2569507664) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 2569507664 * (2 : ZMod 1644484905221) ^ 2569507664 := by rw [pow_add]
          _ = 752034240723 := by rw [factor_1_31]; decide
      have factor_1_33 : (2 : ZMod 1644484905221) ^ 10278030657 = 529893625343 := by
        calc
          (2 : ZMod 1644484905221) ^ 10278030657 = (2 : ZMod 1644484905221) ^ (5139015328 + 5139015328 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 5139015328 * (2 : ZMod 1644484905221) ^ 5139015328) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 529893625343 := by rw [factor_1_32]; decide
      have factor_1_34 : (2 : ZMod 1644484905221) ^ 20556061315 = 703251657869 := by
        calc
          (2 : ZMod 1644484905221) ^ 20556061315 = (2 : ZMod 1644484905221) ^ (10278030657 + 10278030657 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 10278030657 * (2 : ZMod 1644484905221) ^ 10278030657) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 703251657869 := by rw [factor_1_33]; decide
      have factor_1_35 : (2 : ZMod 1644484905221) ^ 41112122630 = 1202286518004 := by
        calc
          (2 : ZMod 1644484905221) ^ 41112122630 = (2 : ZMod 1644484905221) ^ (20556061315 + 20556061315) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 20556061315 * (2 : ZMod 1644484905221) ^ 20556061315 := by rw [pow_add]
          _ = 1202286518004 := by rw [factor_1_34]; decide
      have factor_1_36 : (2 : ZMod 1644484905221) ^ 82224245261 = 181473862059 := by
        calc
          (2 : ZMod 1644484905221) ^ 82224245261 = (2 : ZMod 1644484905221) ^ (41112122630 + 41112122630 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 41112122630 * (2 : ZMod 1644484905221) ^ 41112122630) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 181473862059 := by rw [factor_1_35]; decide
      have factor_1_37 : (2 : ZMod 1644484905221) ^ 164448490522 = 99924286430 := by
        calc
          (2 : ZMod 1644484905221) ^ 164448490522 = (2 : ZMod 1644484905221) ^ (82224245261 + 82224245261) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 82224245261 * (2 : ZMod 1644484905221) ^ 82224245261 := by rw [pow_add]
          _ = 99924286430 := by rw [factor_1_36]; decide
      have factor_1_38 : (2 : ZMod 1644484905221) ^ 328896981044 = 1586878394393 := by
        calc
          (2 : ZMod 1644484905221) ^ 328896981044 = (2 : ZMod 1644484905221) ^ (164448490522 + 164448490522) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 164448490522 * (2 : ZMod 1644484905221) ^ 164448490522 := by rw [pow_add]
          _ = 1586878394393 := by rw [factor_1_37]; decide
      change (2 : ZMod 1644484905221) ^ 328896981044 ≠ 1
      rw [factor_1_38]
      decide
    ·
      have factor_2_0 : (2 : ZMod 1644484905221) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 1644484905221) ^ 3 = 8 := by
        calc
          (2 : ZMod 1644484905221) ^ 3 = (2 : ZMod 1644484905221) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 1 * (2 : ZMod 1644484905221) ^ 1) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 1644484905221) ^ 6 = 64 := by
        calc
          (2 : ZMod 1644484905221) ^ 6 = (2 : ZMod 1644484905221) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 3 * (2 : ZMod 1644484905221) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 1644484905221) ^ 12 = 4096 := by
        calc
          (2 : ZMod 1644484905221) ^ 12 = (2 : ZMod 1644484905221) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 6 * (2 : ZMod 1644484905221) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 1644484905221) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 1644484905221) ^ 25 = (2 : ZMod 1644484905221) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 12 * (2 : ZMod 1644484905221) ^ 12) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 1644484905221) ^ 51 = 499978437699 := by
        calc
          (2 : ZMod 1644484905221) ^ 51 = (2 : ZMod 1644484905221) ^ (25 + 25 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 25 * (2 : ZMod 1644484905221) ^ 25) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 499978437699 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 1644484905221) ^ 102 = 565112043220 := by
        calc
          (2 : ZMod 1644484905221) ^ 102 = (2 : ZMod 1644484905221) ^ (51 + 51) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 51 * (2 : ZMod 1644484905221) ^ 51 := by rw [pow_add]
          _ = 565112043220 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 1644484905221) ^ 205 = 136501926886 := by
        calc
          (2 : ZMod 1644484905221) ^ 205 = (2 : ZMod 1644484905221) ^ (102 + 102 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 102 * (2 : ZMod 1644484905221) ^ 102) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 136501926886 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 1644484905221) ^ 410 = 1620485909049 := by
        calc
          (2 : ZMod 1644484905221) ^ 410 = (2 : ZMod 1644484905221) ^ (205 + 205) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 205 * (2 : ZMod 1644484905221) ^ 205 := by rw [pow_add]
          _ = 1620485909049 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 1644484905221) ^ 820 = 1079622743792 := by
        calc
          (2 : ZMod 1644484905221) ^ 820 = (2 : ZMod 1644484905221) ^ (410 + 410) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 410 * (2 : ZMod 1644484905221) ^ 410 := by rw [pow_add]
          _ = 1079622743792 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 1644484905221) ^ 1640 = 1011573315212 := by
        calc
          (2 : ZMod 1644484905221) ^ 1640 = (2 : ZMod 1644484905221) ^ (820 + 820) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 820 * (2 : ZMod 1644484905221) ^ 820 := by rw [pow_add]
          _ = 1011573315212 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 1644484905221) ^ 3280 = 682346097416 := by
        calc
          (2 : ZMod 1644484905221) ^ 3280 = (2 : ZMod 1644484905221) ^ (1640 + 1640) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 1640 * (2 : ZMod 1644484905221) ^ 1640 := by rw [pow_add]
          _ = 682346097416 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 1644484905221) ^ 6561 = 1554692106503 := by
        calc
          (2 : ZMod 1644484905221) ^ 6561 = (2 : ZMod 1644484905221) ^ (3280 + 3280 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 3280 * (2 : ZMod 1644484905221) ^ 3280) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 1554692106503 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 1644484905221) ^ 13123 = 1035904351070 := by
        calc
          (2 : ZMod 1644484905221) ^ 13123 = (2 : ZMod 1644484905221) ^ (6561 + 6561 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 6561 * (2 : ZMod 1644484905221) ^ 6561) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 1035904351070 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 1644484905221) ^ 26247 = 249762178641 := by
        calc
          (2 : ZMod 1644484905221) ^ 26247 = (2 : ZMod 1644484905221) ^ (13123 + 13123 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 13123 * (2 : ZMod 1644484905221) ^ 13123) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 249762178641 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 1644484905221) ^ 52495 = 1437895672632 := by
        calc
          (2 : ZMod 1644484905221) ^ 52495 = (2 : ZMod 1644484905221) ^ (26247 + 26247 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 26247 * (2 : ZMod 1644484905221) ^ 26247) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 1437895672632 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 1644484905221) ^ 104990 = 1572969790021 := by
        calc
          (2 : ZMod 1644484905221) ^ 104990 = (2 : ZMod 1644484905221) ^ (52495 + 52495) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 52495 * (2 : ZMod 1644484905221) ^ 52495 := by rw [pow_add]
          _ = 1572969790021 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 1644484905221) ^ 209981 = 665348543274 := by
        calc
          (2 : ZMod 1644484905221) ^ 209981 = (2 : ZMod 1644484905221) ^ (104990 + 104990 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 104990 * (2 : ZMod 1644484905221) ^ 104990) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 665348543274 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 1644484905221) ^ 419963 = 211725689509 := by
        calc
          (2 : ZMod 1644484905221) ^ 419963 = (2 : ZMod 1644484905221) ^ (209981 + 209981 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 209981 * (2 : ZMod 1644484905221) ^ 209981) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 211725689509 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 1644484905221) ^ 839927 = 691985095745 := by
        calc
          (2 : ZMod 1644484905221) ^ 839927 = (2 : ZMod 1644484905221) ^ (419963 + 419963 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 419963 * (2 : ZMod 1644484905221) ^ 419963) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 691985095745 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 1644484905221) ^ 1679855 = 508144972944 := by
        calc
          (2 : ZMod 1644484905221) ^ 1679855 = (2 : ZMod 1644484905221) ^ (839927 + 839927 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 839927 * (2 : ZMod 1644484905221) ^ 839927) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 508144972944 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 1644484905221) ^ 3359711 = 1441706134824 := by
        calc
          (2 : ZMod 1644484905221) ^ 3359711 = (2 : ZMod 1644484905221) ^ (1679855 + 1679855 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 1679855 * (2 : ZMod 1644484905221) ^ 1679855) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 1441706134824 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 1644484905221) ^ 6719423 = 530449005889 := by
        calc
          (2 : ZMod 1644484905221) ^ 6719423 = (2 : ZMod 1644484905221) ^ (3359711 + 3359711 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 3359711 * (2 : ZMod 1644484905221) ^ 3359711) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 530449005889 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 1644484905221) ^ 13438847 = 11433963824 := by
        calc
          (2 : ZMod 1644484905221) ^ 13438847 = (2 : ZMod 1644484905221) ^ (6719423 + 6719423 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 6719423 * (2 : ZMod 1644484905221) ^ 6719423) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 11433963824 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 1644484905221) ^ 26877695 = 1621679595655 := by
        calc
          (2 : ZMod 1644484905221) ^ 26877695 = (2 : ZMod 1644484905221) ^ (13438847 + 13438847 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 13438847 * (2 : ZMod 1644484905221) ^ 13438847) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 1621679595655 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 1644484905221) ^ 53755390 = 830049769829 := by
        calc
          (2 : ZMod 1644484905221) ^ 53755390 = (2 : ZMod 1644484905221) ^ (26877695 + 26877695) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 26877695 * (2 : ZMod 1644484905221) ^ 26877695 := by rw [pow_add]
          _ = 830049769829 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 1644484905221) ^ 107510780 = 515707841565 := by
        calc
          (2 : ZMod 1644484905221) ^ 107510780 = (2 : ZMod 1644484905221) ^ (53755390 + 53755390) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 53755390 * (2 : ZMod 1644484905221) ^ 53755390 := by rw [pow_add]
          _ = 515707841565 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 1644484905221) ^ 215021561 = 638676052472 := by
        calc
          (2 : ZMod 1644484905221) ^ 215021561 = (2 : ZMod 1644484905221) ^ (107510780 + 107510780 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 107510780 * (2 : ZMod 1644484905221) ^ 107510780) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 638676052472 := by rw [factor_2_26]; decide
      have factor_2_28 : (2 : ZMod 1644484905221) ^ 430043123 = 952614765802 := by
        calc
          (2 : ZMod 1644484905221) ^ 430043123 = (2 : ZMod 1644484905221) ^ (215021561 + 215021561 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 215021561 * (2 : ZMod 1644484905221) ^ 215021561) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 952614765802 := by rw [factor_2_27]; decide
      have factor_2_29 : (2 : ZMod 1644484905221) ^ 860086247 = 778805328455 := by
        calc
          (2 : ZMod 1644484905221) ^ 860086247 = (2 : ZMod 1644484905221) ^ (430043123 + 430043123 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 430043123 * (2 : ZMod 1644484905221) ^ 430043123) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 778805328455 := by rw [factor_2_28]; decide
      have factor_2_30 : (2 : ZMod 1644484905221) ^ 1720172495 = 288512529631 := by
        calc
          (2 : ZMod 1644484905221) ^ 1720172495 = (2 : ZMod 1644484905221) ^ (860086247 + 860086247 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 860086247 * (2 : ZMod 1644484905221) ^ 860086247) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 288512529631 := by rw [factor_2_29]; decide
      have factor_2_31 : (2 : ZMod 1644484905221) ^ 3440344990 = 101700083884 := by
        calc
          (2 : ZMod 1644484905221) ^ 3440344990 = (2 : ZMod 1644484905221) ^ (1720172495 + 1720172495) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 1720172495 * (2 : ZMod 1644484905221) ^ 1720172495 := by rw [pow_add]
          _ = 101700083884 := by rw [factor_2_30]; decide
      have factor_2_32 : (2 : ZMod 1644484905221) ^ 6880689980 = 1411942997440 := by
        calc
          (2 : ZMod 1644484905221) ^ 6880689980 = (2 : ZMod 1644484905221) ^ (3440344990 + 3440344990) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 3440344990 * (2 : ZMod 1644484905221) ^ 3440344990 := by rw [pow_add]
          _ = 1411942997440 := by rw [factor_2_31]; decide
      change (2 : ZMod 1644484905221) ^ 6880689980 ≠ 1
      rw [factor_2_32]
      decide
    ·
      have factor_3_0 : (2 : ZMod 1644484905221) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 1644484905221) ^ 2 = 4 := by
        calc
          (2 : ZMod 1644484905221) ^ 2 = (2 : ZMod 1644484905221) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 1 * (2 : ZMod 1644484905221) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 1644484905221) ^ 4 = 16 := by
        calc
          (2 : ZMod 1644484905221) ^ 4 = (2 : ZMod 1644484905221) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 2 * (2 : ZMod 1644484905221) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 1644484905221) ^ 9 = 512 := by
        calc
          (2 : ZMod 1644484905221) ^ 9 = (2 : ZMod 1644484905221) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 4 * (2 : ZMod 1644484905221) ^ 4) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 512 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 1644484905221) ^ 18 = 262144 := by
        calc
          (2 : ZMod 1644484905221) ^ 18 = (2 : ZMod 1644484905221) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 9 * (2 : ZMod 1644484905221) ^ 9 := by rw [pow_add]
          _ = 262144 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 1644484905221) ^ 37 = 137438953472 := by
        calc
          (2 : ZMod 1644484905221) ^ 37 = (2 : ZMod 1644484905221) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 18 * (2 : ZMod 1644484905221) ^ 18) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 137438953472 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 1644484905221) ^ 74 = 863790305835 := by
        calc
          (2 : ZMod 1644484905221) ^ 74 = (2 : ZMod 1644484905221) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 37 * (2 : ZMod 1644484905221) ^ 37 := by rw [pow_add]
          _ = 863790305835 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 1644484905221) ^ 149 = 1566377130974 := by
        calc
          (2 : ZMod 1644484905221) ^ 149 = (2 : ZMod 1644484905221) ^ (74 + 74 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 74 * (2 : ZMod 1644484905221) ^ 74) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 1566377130974 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 1644484905221) ^ 298 = 1441567947067 := by
        calc
          (2 : ZMod 1644484905221) ^ 298 = (2 : ZMod 1644484905221) ^ (149 + 149) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 149 * (2 : ZMod 1644484905221) ^ 149 := by rw [pow_add]
          _ = 1441567947067 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 1644484905221) ^ 597 = 848433381285 := by
        calc
          (2 : ZMod 1644484905221) ^ 597 = (2 : ZMod 1644484905221) ^ (298 + 298 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 298 * (2 : ZMod 1644484905221) ^ 298) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 848433381285 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 1644484905221) ^ 1195 = 531950843191 := by
        calc
          (2 : ZMod 1644484905221) ^ 1195 = (2 : ZMod 1644484905221) ^ (597 + 597 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = ((2 : ZMod 1644484905221) ^ 597 * (2 : ZMod 1644484905221) ^ 597) * (2 : ZMod 1644484905221) := by rw [pow_succ, pow_add]
          _ = 531950843191 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 1644484905221) ^ 2390 = 431498790265 := by
        calc
          (2 : ZMod 1644484905221) ^ 2390 = (2 : ZMod 1644484905221) ^ (1195 + 1195) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 1195 * (2 : ZMod 1644484905221) ^ 1195 := by rw [pow_add]
          _ = 431498790265 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 1644484905221) ^ 4780 = 628575981102 := by
        calc
          (2 : ZMod 1644484905221) ^ 4780 = (2 : ZMod 1644484905221) ^ (2390 + 2390) :=
            congrArg (fun n : ℕ => (2 : ZMod 1644484905221) ^ n) (by norm_num)
          _ = (2 : ZMod 1644484905221) ^ 2390 * (2 : ZMod 1644484905221) ^ 2390 := by rw [pow_add]
          _ = 628575981102 := by rw [factor_3_11]; decide
      change (2 : ZMod 1644484905221) ^ 4780 ≠ 1
      rw [factor_3_12]
      decide

#print axioms prime_lucas_1644484905221

end TotientTailPeriodKiller
end Erdos249257
