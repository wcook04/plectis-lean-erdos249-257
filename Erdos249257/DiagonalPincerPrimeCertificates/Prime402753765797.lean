import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_402753765797 : Nat.Prime 402753765797 := by
  apply lucas_primality 402753765797 (2 : ZMod 402753765797)
  ·
      have fermat_0 : (2 : ZMod 402753765797) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 402753765797) ^ 2 = 4 := by
        calc
          (2 : ZMod 402753765797) ^ 2 = (2 : ZMod 402753765797) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 1 * (2 : ZMod 402753765797) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 402753765797) ^ 5 = 32 := by
        calc
          (2 : ZMod 402753765797) ^ 5 = (2 : ZMod 402753765797) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 2 * (2 : ZMod 402753765797) ^ 2) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 402753765797) ^ 11 = 2048 := by
        calc
          (2 : ZMod 402753765797) ^ 11 = (2 : ZMod 402753765797) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 5 * (2 : ZMod 402753765797) ^ 5) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 402753765797) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 402753765797) ^ 23 = (2 : ZMod 402753765797) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 11 * (2 : ZMod 402753765797) ^ 11) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 402753765797) ^ 46 = 289588928986 := by
        calc
          (2 : ZMod 402753765797) ^ 46 = (2 : ZMod 402753765797) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 23 * (2 : ZMod 402753765797) ^ 23 := by rw [pow_add]
          _ = 289588928986 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 402753765797) ^ 93 = 18824326361 := by
        calc
          (2 : ZMod 402753765797) ^ 93 = (2 : ZMod 402753765797) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 46 * (2 : ZMod 402753765797) ^ 46) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 18824326361 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 402753765797) ^ 187 = 265481019055 := by
        calc
          (2 : ZMod 402753765797) ^ 187 = (2 : ZMod 402753765797) ^ (93 + 93 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 93 * (2 : ZMod 402753765797) ^ 93) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 265481019055 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 402753765797) ^ 375 = 274897125210 := by
        calc
          (2 : ZMod 402753765797) ^ 375 = (2 : ZMod 402753765797) ^ (187 + 187 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 187 * (2 : ZMod 402753765797) ^ 187) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 274897125210 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 402753765797) ^ 750 = 196860795804 := by
        calc
          (2 : ZMod 402753765797) ^ 750 = (2 : ZMod 402753765797) ^ (375 + 375) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 375 * (2 : ZMod 402753765797) ^ 375 := by rw [pow_add]
          _ = 196860795804 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 402753765797) ^ 1500 = 236779448639 := by
        calc
          (2 : ZMod 402753765797) ^ 1500 = (2 : ZMod 402753765797) ^ (750 + 750) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 750 * (2 : ZMod 402753765797) ^ 750 := by rw [pow_add]
          _ = 236779448639 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 402753765797) ^ 3000 = 396073651490 := by
        calc
          (2 : ZMod 402753765797) ^ 3000 = (2 : ZMod 402753765797) ^ (1500 + 1500) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 1500 * (2 : ZMod 402753765797) ^ 1500 := by rw [pow_add]
          _ = 396073651490 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 402753765797) ^ 6001 = 83312840768 := by
        calc
          (2 : ZMod 402753765797) ^ 6001 = (2 : ZMod 402753765797) ^ (3000 + 3000 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 3000 * (2 : ZMod 402753765797) ^ 3000) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 83312840768 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 402753765797) ^ 12002 = 320184589485 := by
        calc
          (2 : ZMod 402753765797) ^ 12002 = (2 : ZMod 402753765797) ^ (6001 + 6001) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 6001 * (2 : ZMod 402753765797) ^ 6001 := by rw [pow_add]
          _ = 320184589485 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 402753765797) ^ 24005 = 70568100292 := by
        calc
          (2 : ZMod 402753765797) ^ 24005 = (2 : ZMod 402753765797) ^ (12002 + 12002 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 12002 * (2 : ZMod 402753765797) ^ 12002) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 70568100292 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 402753765797) ^ 48011 = 17887835348 := by
        calc
          (2 : ZMod 402753765797) ^ 48011 = (2 : ZMod 402753765797) ^ (24005 + 24005 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 24005 * (2 : ZMod 402753765797) ^ 24005) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 17887835348 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 402753765797) ^ 96023 = 113980098160 := by
        calc
          (2 : ZMod 402753765797) ^ 96023 = (2 : ZMod 402753765797) ^ (48011 + 48011 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 48011 * (2 : ZMod 402753765797) ^ 48011) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 113980098160 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 402753765797) ^ 192047 = 132208738866 := by
        calc
          (2 : ZMod 402753765797) ^ 192047 = (2 : ZMod 402753765797) ^ (96023 + 96023 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 96023 * (2 : ZMod 402753765797) ^ 96023) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 132208738866 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 402753765797) ^ 384095 = 317016762473 := by
        calc
          (2 : ZMod 402753765797) ^ 384095 = (2 : ZMod 402753765797) ^ (192047 + 192047 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 192047 * (2 : ZMod 402753765797) ^ 192047) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 317016762473 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 402753765797) ^ 768191 = 258538613818 := by
        calc
          (2 : ZMod 402753765797) ^ 768191 = (2 : ZMod 402753765797) ^ (384095 + 384095 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 384095 * (2 : ZMod 402753765797) ^ 384095) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 258538613818 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 402753765797) ^ 1536383 = 373907872336 := by
        calc
          (2 : ZMod 402753765797) ^ 1536383 = (2 : ZMod 402753765797) ^ (768191 + 768191 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 768191 * (2 : ZMod 402753765797) ^ 768191) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 373907872336 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 402753765797) ^ 3072767 = 397163458361 := by
        calc
          (2 : ZMod 402753765797) ^ 3072767 = (2 : ZMod 402753765797) ^ (1536383 + 1536383 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 1536383 * (2 : ZMod 402753765797) ^ 1536383) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 397163458361 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 402753765797) ^ 6145534 = 138550473843 := by
        calc
          (2 : ZMod 402753765797) ^ 6145534 = (2 : ZMod 402753765797) ^ (3072767 + 3072767) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 3072767 * (2 : ZMod 402753765797) ^ 3072767 := by rw [pow_add]
          _ = 138550473843 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 402753765797) ^ 12291069 = 171760641495 := by
        calc
          (2 : ZMod 402753765797) ^ 12291069 = (2 : ZMod 402753765797) ^ (6145534 + 6145534 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 6145534 * (2 : ZMod 402753765797) ^ 6145534) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 171760641495 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 402753765797) ^ 24582139 = 282899097306 := by
        calc
          (2 : ZMod 402753765797) ^ 24582139 = (2 : ZMod 402753765797) ^ (12291069 + 12291069 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 12291069 * (2 : ZMod 402753765797) ^ 12291069) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 282899097306 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 402753765797) ^ 49164278 = 252648831830 := by
        calc
          (2 : ZMod 402753765797) ^ 49164278 = (2 : ZMod 402753765797) ^ (24582139 + 24582139) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 24582139 * (2 : ZMod 402753765797) ^ 24582139 := by rw [pow_add]
          _ = 252648831830 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 402753765797) ^ 98328556 = 83001351930 := by
        calc
          (2 : ZMod 402753765797) ^ 98328556 = (2 : ZMod 402753765797) ^ (49164278 + 49164278) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 49164278 * (2 : ZMod 402753765797) ^ 49164278 := by rw [pow_add]
          _ = 83001351930 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 402753765797) ^ 196657112 = 368253690516 := by
        calc
          (2 : ZMod 402753765797) ^ 196657112 = (2 : ZMod 402753765797) ^ (98328556 + 98328556) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 98328556 * (2 : ZMod 402753765797) ^ 98328556 := by rw [pow_add]
          _ = 368253690516 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 402753765797) ^ 393314224 = 113684929942 := by
        calc
          (2 : ZMod 402753765797) ^ 393314224 = (2 : ZMod 402753765797) ^ (196657112 + 196657112) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 196657112 * (2 : ZMod 402753765797) ^ 196657112 := by rw [pow_add]
          _ = 113684929942 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 402753765797) ^ 786628448 = 145435891686 := by
        calc
          (2 : ZMod 402753765797) ^ 786628448 = (2 : ZMod 402753765797) ^ (393314224 + 393314224) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 393314224 * (2 : ZMod 402753765797) ^ 393314224 := by rw [pow_add]
          _ = 145435891686 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 402753765797) ^ 1573256897 = 328560052506 := by
        calc
          (2 : ZMod 402753765797) ^ 1573256897 = (2 : ZMod 402753765797) ^ (786628448 + 786628448 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 786628448 * (2 : ZMod 402753765797) ^ 786628448) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 328560052506 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 402753765797) ^ 3146513795 = 155249127350 := by
        calc
          (2 : ZMod 402753765797) ^ 3146513795 = (2 : ZMod 402753765797) ^ (1573256897 + 1573256897 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 1573256897 * (2 : ZMod 402753765797) ^ 1573256897) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 155249127350 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 402753765797) ^ 6293027590 = 53906223344 := by
        calc
          (2 : ZMod 402753765797) ^ 6293027590 = (2 : ZMod 402753765797) ^ (3146513795 + 3146513795) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 3146513795 * (2 : ZMod 402753765797) ^ 3146513795 := by rw [pow_add]
          _ = 53906223344 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 402753765797) ^ 12586055181 = 312804678213 := by
        calc
          (2 : ZMod 402753765797) ^ 12586055181 = (2 : ZMod 402753765797) ^ (6293027590 + 6293027590 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 6293027590 * (2 : ZMod 402753765797) ^ 6293027590) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 312804678213 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 402753765797) ^ 25172110362 = 262292932332 := by
        calc
          (2 : ZMod 402753765797) ^ 25172110362 = (2 : ZMod 402753765797) ^ (12586055181 + 12586055181) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 12586055181 * (2 : ZMod 402753765797) ^ 12586055181 := by rw [pow_add]
          _ = 262292932332 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 402753765797) ^ 50344220724 = 216814702847 := by
        calc
          (2 : ZMod 402753765797) ^ 50344220724 = (2 : ZMod 402753765797) ^ (25172110362 + 25172110362) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 25172110362 * (2 : ZMod 402753765797) ^ 25172110362 := by rw [pow_add]
          _ = 216814702847 := by rw [fermat_34]; decide
      have fermat_36 : (2 : ZMod 402753765797) ^ 100688441449 = 30875639896 := by
        calc
          (2 : ZMod 402753765797) ^ 100688441449 = (2 : ZMod 402753765797) ^ (50344220724 + 50344220724 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 50344220724 * (2 : ZMod 402753765797) ^ 50344220724) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 30875639896 := by rw [fermat_35]; decide
      have fermat_37 : (2 : ZMod 402753765797) ^ 201376882898 = 402753765796 := by
        calc
          (2 : ZMod 402753765797) ^ 201376882898 = (2 : ZMod 402753765797) ^ (100688441449 + 100688441449) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 100688441449 * (2 : ZMod 402753765797) ^ 100688441449 := by rw [pow_add]
          _ = 402753765796 := by rw [fermat_36]; decide
      have fermat_38 : (2 : ZMod 402753765797) ^ 402753765796 = 1 := by
        calc
          (2 : ZMod 402753765797) ^ 402753765796 = (2 : ZMod 402753765797) ^ (201376882898 + 201376882898) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 201376882898 * (2 : ZMod 402753765797) ^ 201376882898 := by rw [pow_add]
          _ = 1 := by rw [fermat_37]; decide
      simpa using fermat_38
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17, 1), (383, 1), (15464359, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17, 1), (383, 1), (15464359, 1)] : List FactorBlock).map factorBlockValue).prod = 402753765797 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 402753765797) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 402753765797) ^ 2 = 4 := by
        calc
          (2 : ZMod 402753765797) ^ 2 = (2 : ZMod 402753765797) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 1 * (2 : ZMod 402753765797) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 402753765797) ^ 5 = 32 := by
        calc
          (2 : ZMod 402753765797) ^ 5 = (2 : ZMod 402753765797) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 2 * (2 : ZMod 402753765797) ^ 2) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 402753765797) ^ 11 = 2048 := by
        calc
          (2 : ZMod 402753765797) ^ 11 = (2 : ZMod 402753765797) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 5 * (2 : ZMod 402753765797) ^ 5) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 402753765797) ^ 23 = 8388608 := by
        calc
          (2 : ZMod 402753765797) ^ 23 = (2 : ZMod 402753765797) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 11 * (2 : ZMod 402753765797) ^ 11) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 8388608 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 402753765797) ^ 46 = 289588928986 := by
        calc
          (2 : ZMod 402753765797) ^ 46 = (2 : ZMod 402753765797) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 23 * (2 : ZMod 402753765797) ^ 23 := by rw [pow_add]
          _ = 289588928986 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 402753765797) ^ 93 = 18824326361 := by
        calc
          (2 : ZMod 402753765797) ^ 93 = (2 : ZMod 402753765797) ^ (46 + 46 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 46 * (2 : ZMod 402753765797) ^ 46) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 18824326361 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 402753765797) ^ 187 = 265481019055 := by
        calc
          (2 : ZMod 402753765797) ^ 187 = (2 : ZMod 402753765797) ^ (93 + 93 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 93 * (2 : ZMod 402753765797) ^ 93) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 265481019055 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 402753765797) ^ 375 = 274897125210 := by
        calc
          (2 : ZMod 402753765797) ^ 375 = (2 : ZMod 402753765797) ^ (187 + 187 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 187 * (2 : ZMod 402753765797) ^ 187) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 274897125210 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 402753765797) ^ 750 = 196860795804 := by
        calc
          (2 : ZMod 402753765797) ^ 750 = (2 : ZMod 402753765797) ^ (375 + 375) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 375 * (2 : ZMod 402753765797) ^ 375 := by rw [pow_add]
          _ = 196860795804 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 402753765797) ^ 1500 = 236779448639 := by
        calc
          (2 : ZMod 402753765797) ^ 1500 = (2 : ZMod 402753765797) ^ (750 + 750) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 750 * (2 : ZMod 402753765797) ^ 750 := by rw [pow_add]
          _ = 236779448639 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 402753765797) ^ 3000 = 396073651490 := by
        calc
          (2 : ZMod 402753765797) ^ 3000 = (2 : ZMod 402753765797) ^ (1500 + 1500) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 1500 * (2 : ZMod 402753765797) ^ 1500 := by rw [pow_add]
          _ = 396073651490 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 402753765797) ^ 6001 = 83312840768 := by
        calc
          (2 : ZMod 402753765797) ^ 6001 = (2 : ZMod 402753765797) ^ (3000 + 3000 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 3000 * (2 : ZMod 402753765797) ^ 3000) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 83312840768 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 402753765797) ^ 12002 = 320184589485 := by
        calc
          (2 : ZMod 402753765797) ^ 12002 = (2 : ZMod 402753765797) ^ (6001 + 6001) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 6001 * (2 : ZMod 402753765797) ^ 6001 := by rw [pow_add]
          _ = 320184589485 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 402753765797) ^ 24005 = 70568100292 := by
        calc
          (2 : ZMod 402753765797) ^ 24005 = (2 : ZMod 402753765797) ^ (12002 + 12002 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 12002 * (2 : ZMod 402753765797) ^ 12002) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 70568100292 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 402753765797) ^ 48011 = 17887835348 := by
        calc
          (2 : ZMod 402753765797) ^ 48011 = (2 : ZMod 402753765797) ^ (24005 + 24005 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 24005 * (2 : ZMod 402753765797) ^ 24005) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 17887835348 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 402753765797) ^ 96023 = 113980098160 := by
        calc
          (2 : ZMod 402753765797) ^ 96023 = (2 : ZMod 402753765797) ^ (48011 + 48011 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 48011 * (2 : ZMod 402753765797) ^ 48011) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 113980098160 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 402753765797) ^ 192047 = 132208738866 := by
        calc
          (2 : ZMod 402753765797) ^ 192047 = (2 : ZMod 402753765797) ^ (96023 + 96023 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 96023 * (2 : ZMod 402753765797) ^ 96023) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 132208738866 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 402753765797) ^ 384095 = 317016762473 := by
        calc
          (2 : ZMod 402753765797) ^ 384095 = (2 : ZMod 402753765797) ^ (192047 + 192047 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 192047 * (2 : ZMod 402753765797) ^ 192047) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 317016762473 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 402753765797) ^ 768191 = 258538613818 := by
        calc
          (2 : ZMod 402753765797) ^ 768191 = (2 : ZMod 402753765797) ^ (384095 + 384095 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 384095 * (2 : ZMod 402753765797) ^ 384095) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 258538613818 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 402753765797) ^ 1536383 = 373907872336 := by
        calc
          (2 : ZMod 402753765797) ^ 1536383 = (2 : ZMod 402753765797) ^ (768191 + 768191 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 768191 * (2 : ZMod 402753765797) ^ 768191) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 373907872336 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 402753765797) ^ 3072767 = 397163458361 := by
        calc
          (2 : ZMod 402753765797) ^ 3072767 = (2 : ZMod 402753765797) ^ (1536383 + 1536383 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 1536383 * (2 : ZMod 402753765797) ^ 1536383) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 397163458361 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 402753765797) ^ 6145534 = 138550473843 := by
        calc
          (2 : ZMod 402753765797) ^ 6145534 = (2 : ZMod 402753765797) ^ (3072767 + 3072767) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 3072767 * (2 : ZMod 402753765797) ^ 3072767 := by rw [pow_add]
          _ = 138550473843 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 402753765797) ^ 12291069 = 171760641495 := by
        calc
          (2 : ZMod 402753765797) ^ 12291069 = (2 : ZMod 402753765797) ^ (6145534 + 6145534 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 6145534 * (2 : ZMod 402753765797) ^ 6145534) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 171760641495 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 402753765797) ^ 24582139 = 282899097306 := by
        calc
          (2 : ZMod 402753765797) ^ 24582139 = (2 : ZMod 402753765797) ^ (12291069 + 12291069 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 12291069 * (2 : ZMod 402753765797) ^ 12291069) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 282899097306 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 402753765797) ^ 49164278 = 252648831830 := by
        calc
          (2 : ZMod 402753765797) ^ 49164278 = (2 : ZMod 402753765797) ^ (24582139 + 24582139) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 24582139 * (2 : ZMod 402753765797) ^ 24582139 := by rw [pow_add]
          _ = 252648831830 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 402753765797) ^ 98328556 = 83001351930 := by
        calc
          (2 : ZMod 402753765797) ^ 98328556 = (2 : ZMod 402753765797) ^ (49164278 + 49164278) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 49164278 * (2 : ZMod 402753765797) ^ 49164278 := by rw [pow_add]
          _ = 83001351930 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 402753765797) ^ 196657112 = 368253690516 := by
        calc
          (2 : ZMod 402753765797) ^ 196657112 = (2 : ZMod 402753765797) ^ (98328556 + 98328556) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 98328556 * (2 : ZMod 402753765797) ^ 98328556 := by rw [pow_add]
          _ = 368253690516 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 402753765797) ^ 393314224 = 113684929942 := by
        calc
          (2 : ZMod 402753765797) ^ 393314224 = (2 : ZMod 402753765797) ^ (196657112 + 196657112) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 196657112 * (2 : ZMod 402753765797) ^ 196657112 := by rw [pow_add]
          _ = 113684929942 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 402753765797) ^ 786628448 = 145435891686 := by
        calc
          (2 : ZMod 402753765797) ^ 786628448 = (2 : ZMod 402753765797) ^ (393314224 + 393314224) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 393314224 * (2 : ZMod 402753765797) ^ 393314224 := by rw [pow_add]
          _ = 145435891686 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 402753765797) ^ 1573256897 = 328560052506 := by
        calc
          (2 : ZMod 402753765797) ^ 1573256897 = (2 : ZMod 402753765797) ^ (786628448 + 786628448 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 786628448 * (2 : ZMod 402753765797) ^ 786628448) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 328560052506 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 402753765797) ^ 3146513795 = 155249127350 := by
        calc
          (2 : ZMod 402753765797) ^ 3146513795 = (2 : ZMod 402753765797) ^ (1573256897 + 1573256897 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 1573256897 * (2 : ZMod 402753765797) ^ 1573256897) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 155249127350 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 402753765797) ^ 6293027590 = 53906223344 := by
        calc
          (2 : ZMod 402753765797) ^ 6293027590 = (2 : ZMod 402753765797) ^ (3146513795 + 3146513795) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 3146513795 * (2 : ZMod 402753765797) ^ 3146513795 := by rw [pow_add]
          _ = 53906223344 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 402753765797) ^ 12586055181 = 312804678213 := by
        calc
          (2 : ZMod 402753765797) ^ 12586055181 = (2 : ZMod 402753765797) ^ (6293027590 + 6293027590 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 6293027590 * (2 : ZMod 402753765797) ^ 6293027590) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 312804678213 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 402753765797) ^ 25172110362 = 262292932332 := by
        calc
          (2 : ZMod 402753765797) ^ 25172110362 = (2 : ZMod 402753765797) ^ (12586055181 + 12586055181) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 12586055181 * (2 : ZMod 402753765797) ^ 12586055181 := by rw [pow_add]
          _ = 262292932332 := by rw [factor_0_33]; decide
      have factor_0_35 : (2 : ZMod 402753765797) ^ 50344220724 = 216814702847 := by
        calc
          (2 : ZMod 402753765797) ^ 50344220724 = (2 : ZMod 402753765797) ^ (25172110362 + 25172110362) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 25172110362 * (2 : ZMod 402753765797) ^ 25172110362 := by rw [pow_add]
          _ = 216814702847 := by rw [factor_0_34]; decide
      have factor_0_36 : (2 : ZMod 402753765797) ^ 100688441449 = 30875639896 := by
        calc
          (2 : ZMod 402753765797) ^ 100688441449 = (2 : ZMod 402753765797) ^ (50344220724 + 50344220724 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 50344220724 * (2 : ZMod 402753765797) ^ 50344220724) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 30875639896 := by rw [factor_0_35]; decide
      have factor_0_37 : (2 : ZMod 402753765797) ^ 201376882898 = 402753765796 := by
        calc
          (2 : ZMod 402753765797) ^ 201376882898 = (2 : ZMod 402753765797) ^ (100688441449 + 100688441449) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 100688441449 * (2 : ZMod 402753765797) ^ 100688441449 := by rw [pow_add]
          _ = 402753765796 := by rw [factor_0_36]; decide
      change (2 : ZMod 402753765797) ^ 201376882898 ≠ 1
      rw [factor_0_37]
      decide
    ·
      have factor_1_0 : (2 : ZMod 402753765797) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 402753765797) ^ 2 = 4 := by
        calc
          (2 : ZMod 402753765797) ^ 2 = (2 : ZMod 402753765797) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 1 * (2 : ZMod 402753765797) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 402753765797) ^ 5 = 32 := by
        calc
          (2 : ZMod 402753765797) ^ 5 = (2 : ZMod 402753765797) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 2 * (2 : ZMod 402753765797) ^ 2) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 32 := by rw [factor_1_1]; decide
      have factor_1_3 : (2 : ZMod 402753765797) ^ 11 = 2048 := by
        calc
          (2 : ZMod 402753765797) ^ 11 = (2 : ZMod 402753765797) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 5 * (2 : ZMod 402753765797) ^ 5) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 2048 := by rw [factor_1_2]; decide
      have factor_1_4 : (2 : ZMod 402753765797) ^ 22 = 4194304 := by
        calc
          (2 : ZMod 402753765797) ^ 22 = (2 : ZMod 402753765797) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 11 * (2 : ZMod 402753765797) ^ 11 := by rw [pow_add]
          _ = 4194304 := by rw [factor_1_3]; decide
      have factor_1_5 : (2 : ZMod 402753765797) ^ 44 = 273774115145 := by
        calc
          (2 : ZMod 402753765797) ^ 44 = (2 : ZMod 402753765797) ^ (22 + 22) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 22 * (2 : ZMod 402753765797) ^ 22 := by rw [pow_add]
          _ = 273774115145 := by rw [factor_1_4]; decide
      have factor_1_6 : (2 : ZMod 402753765797) ^ 88 = 340411750090 := by
        calc
          (2 : ZMod 402753765797) ^ 88 = (2 : ZMod 402753765797) ^ (44 + 44) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 44 * (2 : ZMod 402753765797) ^ 44 := by rw [pow_add]
          _ = 340411750090 := by rw [factor_1_5]; decide
      have factor_1_7 : (2 : ZMod 402753765797) ^ 176 = 62469933973 := by
        calc
          (2 : ZMod 402753765797) ^ 176 = (2 : ZMod 402753765797) ^ (88 + 88) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 88 * (2 : ZMod 402753765797) ^ 88 := by rw [pow_add]
          _ = 62469933973 := by rw [factor_1_6]; decide
      have factor_1_8 : (2 : ZMod 402753765797) ^ 353 = 151455041181 := by
        calc
          (2 : ZMod 402753765797) ^ 353 = (2 : ZMod 402753765797) ^ (176 + 176 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 176 * (2 : ZMod 402753765797) ^ 176) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 151455041181 := by rw [factor_1_7]; decide
      have factor_1_9 : (2 : ZMod 402753765797) ^ 706 = 35064661554 := by
        calc
          (2 : ZMod 402753765797) ^ 706 = (2 : ZMod 402753765797) ^ (353 + 353) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 353 * (2 : ZMod 402753765797) ^ 353 := by rw [pow_add]
          _ = 35064661554 := by rw [factor_1_8]; decide
      have factor_1_10 : (2 : ZMod 402753765797) ^ 1412 = 133764052973 := by
        calc
          (2 : ZMod 402753765797) ^ 1412 = (2 : ZMod 402753765797) ^ (706 + 706) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 706 * (2 : ZMod 402753765797) ^ 706 := by rw [pow_add]
          _ = 133764052973 := by rw [factor_1_9]; decide
      have factor_1_11 : (2 : ZMod 402753765797) ^ 2824 = 99078741682 := by
        calc
          (2 : ZMod 402753765797) ^ 2824 = (2 : ZMod 402753765797) ^ (1412 + 1412) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 1412 * (2 : ZMod 402753765797) ^ 1412 := by rw [pow_add]
          _ = 99078741682 := by rw [factor_1_10]; decide
      have factor_1_12 : (2 : ZMod 402753765797) ^ 5648 = 349664755184 := by
        calc
          (2 : ZMod 402753765797) ^ 5648 = (2 : ZMod 402753765797) ^ (2824 + 2824) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 2824 * (2 : ZMod 402753765797) ^ 2824 := by rw [pow_add]
          _ = 349664755184 := by rw [factor_1_11]; decide
      have factor_1_13 : (2 : ZMod 402753765797) ^ 11296 = 134303729055 := by
        calc
          (2 : ZMod 402753765797) ^ 11296 = (2 : ZMod 402753765797) ^ (5648 + 5648) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 5648 * (2 : ZMod 402753765797) ^ 5648 := by rw [pow_add]
          _ = 134303729055 := by rw [factor_1_12]; decide
      have factor_1_14 : (2 : ZMod 402753765797) ^ 22593 = 234395092557 := by
        calc
          (2 : ZMod 402753765797) ^ 22593 = (2 : ZMod 402753765797) ^ (11296 + 11296 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 11296 * (2 : ZMod 402753765797) ^ 11296) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 234395092557 := by rw [factor_1_13]; decide
      have factor_1_15 : (2 : ZMod 402753765797) ^ 45187 = 326299967779 := by
        calc
          (2 : ZMod 402753765797) ^ 45187 = (2 : ZMod 402753765797) ^ (22593 + 22593 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 22593 * (2 : ZMod 402753765797) ^ 22593) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 326299967779 := by rw [factor_1_14]; decide
      have factor_1_16 : (2 : ZMod 402753765797) ^ 90375 = 134165916644 := by
        calc
          (2 : ZMod 402753765797) ^ 90375 = (2 : ZMod 402753765797) ^ (45187 + 45187 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 45187 * (2 : ZMod 402753765797) ^ 45187) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 134165916644 := by rw [factor_1_15]; decide
      have factor_1_17 : (2 : ZMod 402753765797) ^ 180751 = 128759231809 := by
        calc
          (2 : ZMod 402753765797) ^ 180751 = (2 : ZMod 402753765797) ^ (90375 + 90375 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 90375 * (2 : ZMod 402753765797) ^ 90375) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 128759231809 := by rw [factor_1_16]; decide
      have factor_1_18 : (2 : ZMod 402753765797) ^ 361502 = 210680113318 := by
        calc
          (2 : ZMod 402753765797) ^ 361502 = (2 : ZMod 402753765797) ^ (180751 + 180751) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 180751 * (2 : ZMod 402753765797) ^ 180751 := by rw [pow_add]
          _ = 210680113318 := by rw [factor_1_17]; decide
      have factor_1_19 : (2 : ZMod 402753765797) ^ 723004 = 211632625555 := by
        calc
          (2 : ZMod 402753765797) ^ 723004 = (2 : ZMod 402753765797) ^ (361502 + 361502) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 361502 * (2 : ZMod 402753765797) ^ 361502 := by rw [pow_add]
          _ = 211632625555 := by rw [factor_1_18]; decide
      have factor_1_20 : (2 : ZMod 402753765797) ^ 1446008 = 200138851620 := by
        calc
          (2 : ZMod 402753765797) ^ 1446008 = (2 : ZMod 402753765797) ^ (723004 + 723004) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 723004 * (2 : ZMod 402753765797) ^ 723004 := by rw [pow_add]
          _ = 200138851620 := by rw [factor_1_19]; decide
      have factor_1_21 : (2 : ZMod 402753765797) ^ 2892016 = 3723776725 := by
        calc
          (2 : ZMod 402753765797) ^ 2892016 = (2 : ZMod 402753765797) ^ (1446008 + 1446008) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 1446008 * (2 : ZMod 402753765797) ^ 1446008 := by rw [pow_add]
          _ = 3723776725 := by rw [factor_1_20]; decide
      have factor_1_22 : (2 : ZMod 402753765797) ^ 5784032 = 187309002796 := by
        calc
          (2 : ZMod 402753765797) ^ 5784032 = (2 : ZMod 402753765797) ^ (2892016 + 2892016) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 2892016 * (2 : ZMod 402753765797) ^ 2892016 := by rw [pow_add]
          _ = 187309002796 := by rw [factor_1_21]; decide
      have factor_1_23 : (2 : ZMod 402753765797) ^ 11568065 = 245882237877 := by
        calc
          (2 : ZMod 402753765797) ^ 11568065 = (2 : ZMod 402753765797) ^ (5784032 + 5784032 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 5784032 * (2 : ZMod 402753765797) ^ 5784032) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 245882237877 := by rw [factor_1_22]; decide
      have factor_1_24 : (2 : ZMod 402753765797) ^ 23136130 = 397042250462 := by
        calc
          (2 : ZMod 402753765797) ^ 23136130 = (2 : ZMod 402753765797) ^ (11568065 + 11568065) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 11568065 * (2 : ZMod 402753765797) ^ 11568065 := by rw [pow_add]
          _ = 397042250462 := by rw [factor_1_23]; decide
      have factor_1_25 : (2 : ZMod 402753765797) ^ 46272261 = 116078075504 := by
        calc
          (2 : ZMod 402753765797) ^ 46272261 = (2 : ZMod 402753765797) ^ (23136130 + 23136130 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 23136130 * (2 : ZMod 402753765797) ^ 23136130) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 116078075504 := by rw [factor_1_24]; decide
      have factor_1_26 : (2 : ZMod 402753765797) ^ 92544523 = 177415124482 := by
        calc
          (2 : ZMod 402753765797) ^ 92544523 = (2 : ZMod 402753765797) ^ (46272261 + 46272261 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 46272261 * (2 : ZMod 402753765797) ^ 46272261) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 177415124482 := by rw [factor_1_25]; decide
      have factor_1_27 : (2 : ZMod 402753765797) ^ 185089046 = 323405623149 := by
        calc
          (2 : ZMod 402753765797) ^ 185089046 = (2 : ZMod 402753765797) ^ (92544523 + 92544523) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 92544523 * (2 : ZMod 402753765797) ^ 92544523 := by rw [pow_add]
          _ = 323405623149 := by rw [factor_1_26]; decide
      have factor_1_28 : (2 : ZMod 402753765797) ^ 370178093 = 224630456321 := by
        calc
          (2 : ZMod 402753765797) ^ 370178093 = (2 : ZMod 402753765797) ^ (185089046 + 185089046 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 185089046 * (2 : ZMod 402753765797) ^ 185089046) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 224630456321 := by rw [factor_1_27]; decide
      have factor_1_29 : (2 : ZMod 402753765797) ^ 740356187 = 347465776049 := by
        calc
          (2 : ZMod 402753765797) ^ 740356187 = (2 : ZMod 402753765797) ^ (370178093 + 370178093 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 370178093 * (2 : ZMod 402753765797) ^ 370178093) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 347465776049 := by rw [factor_1_28]; decide
      have factor_1_30 : (2 : ZMod 402753765797) ^ 1480712374 = 227935706104 := by
        calc
          (2 : ZMod 402753765797) ^ 1480712374 = (2 : ZMod 402753765797) ^ (740356187 + 740356187) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 740356187 * (2 : ZMod 402753765797) ^ 740356187 := by rw [pow_add]
          _ = 227935706104 := by rw [factor_1_29]; decide
      have factor_1_31 : (2 : ZMod 402753765797) ^ 2961424748 = 3301054273 := by
        calc
          (2 : ZMod 402753765797) ^ 2961424748 = (2 : ZMod 402753765797) ^ (1480712374 + 1480712374) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 1480712374 * (2 : ZMod 402753765797) ^ 1480712374 := by rw [pow_add]
          _ = 3301054273 := by rw [factor_1_30]; decide
      have factor_1_32 : (2 : ZMod 402753765797) ^ 5922849497 = 122027916853 := by
        calc
          (2 : ZMod 402753765797) ^ 5922849497 = (2 : ZMod 402753765797) ^ (2961424748 + 2961424748 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 2961424748 * (2 : ZMod 402753765797) ^ 2961424748) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 122027916853 := by rw [factor_1_31]; decide
      have factor_1_33 : (2 : ZMod 402753765797) ^ 11845698994 = 375522649705 := by
        calc
          (2 : ZMod 402753765797) ^ 11845698994 = (2 : ZMod 402753765797) ^ (5922849497 + 5922849497) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 5922849497 * (2 : ZMod 402753765797) ^ 5922849497 := by rw [pow_add]
          _ = 375522649705 := by rw [factor_1_32]; decide
      have factor_1_34 : (2 : ZMod 402753765797) ^ 23691397988 = 391042848585 := by
        calc
          (2 : ZMod 402753765797) ^ 23691397988 = (2 : ZMod 402753765797) ^ (11845698994 + 11845698994) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 11845698994 * (2 : ZMod 402753765797) ^ 11845698994 := by rw [pow_add]
          _ = 391042848585 := by rw [factor_1_33]; decide
      change (2 : ZMod 402753765797) ^ 23691397988 ≠ 1
      rw [factor_1_34]
      decide
    ·
      have factor_2_0 : (2 : ZMod 402753765797) ^ 1 = 2 := by norm_num
      have factor_2_1 : (2 : ZMod 402753765797) ^ 3 = 8 := by
        calc
          (2 : ZMod 402753765797) ^ 3 = (2 : ZMod 402753765797) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 1 * (2 : ZMod 402753765797) ^ 1) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_2_0]; decide
      have factor_2_2 : (2 : ZMod 402753765797) ^ 7 = 128 := by
        calc
          (2 : ZMod 402753765797) ^ 7 = (2 : ZMod 402753765797) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 3 * (2 : ZMod 402753765797) ^ 3) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 128 := by rw [factor_2_1]; decide
      have factor_2_3 : (2 : ZMod 402753765797) ^ 15 = 32768 := by
        calc
          (2 : ZMod 402753765797) ^ 15 = (2 : ZMod 402753765797) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 7 * (2 : ZMod 402753765797) ^ 7) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 32768 := by rw [factor_2_2]; decide
      have factor_2_4 : (2 : ZMod 402753765797) ^ 31 = 2147483648 := by
        calc
          (2 : ZMod 402753765797) ^ 31 = (2 : ZMod 402753765797) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 15 * (2 : ZMod 402753765797) ^ 15) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 2147483648 := by rw [factor_2_3]; decide
      have factor_2_5 : (2 : ZMod 402753765797) ^ 62 = 339851906059 := by
        calc
          (2 : ZMod 402753765797) ^ 62 = (2 : ZMod 402753765797) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 31 * (2 : ZMod 402753765797) ^ 31 := by rw [pow_add]
          _ = 339851906059 := by rw [factor_2_4]; decide
      have factor_2_6 : (2 : ZMod 402753765797) ^ 125 = 193834997663 := by
        calc
          (2 : ZMod 402753765797) ^ 125 = (2 : ZMod 402753765797) ^ (62 + 62 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 62 * (2 : ZMod 402753765797) ^ 62) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 193834997663 := by rw [factor_2_5]; decide
      have factor_2_7 : (2 : ZMod 402753765797) ^ 250 = 89247468644 := by
        calc
          (2 : ZMod 402753765797) ^ 250 = (2 : ZMod 402753765797) ^ (125 + 125) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 125 * (2 : ZMod 402753765797) ^ 125 := by rw [pow_add]
          _ = 89247468644 := by rw [factor_2_6]; decide
      have factor_2_8 : (2 : ZMod 402753765797) ^ 501 = 143875859011 := by
        calc
          (2 : ZMod 402753765797) ^ 501 = (2 : ZMod 402753765797) ^ (250 + 250 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 250 * (2 : ZMod 402753765797) ^ 250) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 143875859011 := by rw [factor_2_7]; decide
      have factor_2_9 : (2 : ZMod 402753765797) ^ 1002 = 357076826527 := by
        calc
          (2 : ZMod 402753765797) ^ 1002 = (2 : ZMod 402753765797) ^ (501 + 501) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 501 * (2 : ZMod 402753765797) ^ 501 := by rw [pow_add]
          _ = 357076826527 := by rw [factor_2_8]; decide
      have factor_2_10 : (2 : ZMod 402753765797) ^ 2005 = 332612011181 := by
        calc
          (2 : ZMod 402753765797) ^ 2005 = (2 : ZMod 402753765797) ^ (1002 + 1002 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 1002 * (2 : ZMod 402753765797) ^ 1002) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 332612011181 := by rw [factor_2_9]; decide
      have factor_2_11 : (2 : ZMod 402753765797) ^ 4011 = 255011877847 := by
        calc
          (2 : ZMod 402753765797) ^ 4011 = (2 : ZMod 402753765797) ^ (2005 + 2005 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 2005 * (2 : ZMod 402753765797) ^ 2005) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 255011877847 := by rw [factor_2_10]; decide
      have factor_2_12 : (2 : ZMod 402753765797) ^ 8022 = 187789792481 := by
        calc
          (2 : ZMod 402753765797) ^ 8022 = (2 : ZMod 402753765797) ^ (4011 + 4011) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 4011 * (2 : ZMod 402753765797) ^ 4011 := by rw [pow_add]
          _ = 187789792481 := by rw [factor_2_11]; decide
      have factor_2_13 : (2 : ZMod 402753765797) ^ 16045 = 20543760173 := by
        calc
          (2 : ZMod 402753765797) ^ 16045 = (2 : ZMod 402753765797) ^ (8022 + 8022 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 8022 * (2 : ZMod 402753765797) ^ 8022) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 20543760173 := by rw [factor_2_12]; decide
      have factor_2_14 : (2 : ZMod 402753765797) ^ 32091 = 116447153978 := by
        calc
          (2 : ZMod 402753765797) ^ 32091 = (2 : ZMod 402753765797) ^ (16045 + 16045 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 16045 * (2 : ZMod 402753765797) ^ 16045) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 116447153978 := by rw [factor_2_13]; decide
      have factor_2_15 : (2 : ZMod 402753765797) ^ 64183 = 309280092152 := by
        calc
          (2 : ZMod 402753765797) ^ 64183 = (2 : ZMod 402753765797) ^ (32091 + 32091 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 32091 * (2 : ZMod 402753765797) ^ 32091) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 309280092152 := by rw [factor_2_14]; decide
      have factor_2_16 : (2 : ZMod 402753765797) ^ 128366 = 369764828086 := by
        calc
          (2 : ZMod 402753765797) ^ 128366 = (2 : ZMod 402753765797) ^ (64183 + 64183) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 64183 * (2 : ZMod 402753765797) ^ 64183 := by rw [pow_add]
          _ = 369764828086 := by rw [factor_2_15]; decide
      have factor_2_17 : (2 : ZMod 402753765797) ^ 256732 = 337950797635 := by
        calc
          (2 : ZMod 402753765797) ^ 256732 = (2 : ZMod 402753765797) ^ (128366 + 128366) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 128366 * (2 : ZMod 402753765797) ^ 128366 := by rw [pow_add]
          _ = 337950797635 := by rw [factor_2_16]; decide
      have factor_2_18 : (2 : ZMod 402753765797) ^ 513465 = 48439347098 := by
        calc
          (2 : ZMod 402753765797) ^ 513465 = (2 : ZMod 402753765797) ^ (256732 + 256732 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 256732 * (2 : ZMod 402753765797) ^ 256732) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 48439347098 := by rw [factor_2_17]; decide
      have factor_2_19 : (2 : ZMod 402753765797) ^ 1026930 = 306123392758 := by
        calc
          (2 : ZMod 402753765797) ^ 1026930 = (2 : ZMod 402753765797) ^ (513465 + 513465) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 513465 * (2 : ZMod 402753765797) ^ 513465 := by rw [pow_add]
          _ = 306123392758 := by rw [factor_2_18]; decide
      have factor_2_20 : (2 : ZMod 402753765797) ^ 2053860 = 79225223510 := by
        calc
          (2 : ZMod 402753765797) ^ 2053860 = (2 : ZMod 402753765797) ^ (1026930 + 1026930) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 1026930 * (2 : ZMod 402753765797) ^ 1026930 := by rw [pow_add]
          _ = 79225223510 := by rw [factor_2_19]; decide
      have factor_2_21 : (2 : ZMod 402753765797) ^ 4107720 = 291836426030 := by
        calc
          (2 : ZMod 402753765797) ^ 4107720 = (2 : ZMod 402753765797) ^ (2053860 + 2053860) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 2053860 * (2 : ZMod 402753765797) ^ 2053860 := by rw [pow_add]
          _ = 291836426030 := by rw [factor_2_20]; decide
      have factor_2_22 : (2 : ZMod 402753765797) ^ 8215440 = 366959534703 := by
        calc
          (2 : ZMod 402753765797) ^ 8215440 = (2 : ZMod 402753765797) ^ (4107720 + 4107720) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 4107720 * (2 : ZMod 402753765797) ^ 4107720 := by rw [pow_add]
          _ = 366959534703 := by rw [factor_2_21]; decide
      have factor_2_23 : (2 : ZMod 402753765797) ^ 16430881 = 392489668131 := by
        calc
          (2 : ZMod 402753765797) ^ 16430881 = (2 : ZMod 402753765797) ^ (8215440 + 8215440 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 8215440 * (2 : ZMod 402753765797) ^ 8215440) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 392489668131 := by rw [factor_2_22]; decide
      have factor_2_24 : (2 : ZMod 402753765797) ^ 32861762 = 344143328267 := by
        calc
          (2 : ZMod 402753765797) ^ 32861762 = (2 : ZMod 402753765797) ^ (16430881 + 16430881) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 16430881 * (2 : ZMod 402753765797) ^ 16430881 := by rw [pow_add]
          _ = 344143328267 := by rw [factor_2_23]; decide
      have factor_2_25 : (2 : ZMod 402753765797) ^ 65723525 = 84661328685 := by
        calc
          (2 : ZMod 402753765797) ^ 65723525 = (2 : ZMod 402753765797) ^ (32861762 + 32861762 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 32861762 * (2 : ZMod 402753765797) ^ 32861762) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 84661328685 := by rw [factor_2_24]; decide
      have factor_2_26 : (2 : ZMod 402753765797) ^ 131447051 = 328108229426 := by
        calc
          (2 : ZMod 402753765797) ^ 131447051 = (2 : ZMod 402753765797) ^ (65723525 + 65723525 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 65723525 * (2 : ZMod 402753765797) ^ 65723525) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 328108229426 := by rw [factor_2_25]; decide
      have factor_2_27 : (2 : ZMod 402753765797) ^ 262894103 = 247183978924 := by
        calc
          (2 : ZMod 402753765797) ^ 262894103 = (2 : ZMod 402753765797) ^ (131447051 + 131447051 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 131447051 * (2 : ZMod 402753765797) ^ 131447051) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 247183978924 := by rw [factor_2_26]; decide
      have factor_2_28 : (2 : ZMod 402753765797) ^ 525788206 = 219716782274 := by
        calc
          (2 : ZMod 402753765797) ^ 525788206 = (2 : ZMod 402753765797) ^ (262894103 + 262894103) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 262894103 * (2 : ZMod 402753765797) ^ 262894103 := by rw [pow_add]
          _ = 219716782274 := by rw [factor_2_27]; decide
      have factor_2_29 : (2 : ZMod 402753765797) ^ 1051576412 = 304267109315 := by
        calc
          (2 : ZMod 402753765797) ^ 1051576412 = (2 : ZMod 402753765797) ^ (525788206 + 525788206) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 525788206 * (2 : ZMod 402753765797) ^ 525788206 := by rw [pow_add]
          _ = 304267109315 := by rw [factor_2_28]; decide
      change (2 : ZMod 402753765797) ^ 1051576412 ≠ 1
      rw [factor_2_29]
      decide
    ·
      have factor_3_0 : (2 : ZMod 402753765797) ^ 1 = 2 := by norm_num
      have factor_3_1 : (2 : ZMod 402753765797) ^ 3 = 8 := by
        calc
          (2 : ZMod 402753765797) ^ 3 = (2 : ZMod 402753765797) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 1 * (2 : ZMod 402753765797) ^ 1) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_3_0]; decide
      have factor_3_2 : (2 : ZMod 402753765797) ^ 6 = 64 := by
        calc
          (2 : ZMod 402753765797) ^ 6 = (2 : ZMod 402753765797) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 3 * (2 : ZMod 402753765797) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_3_1]; decide
      have factor_3_3 : (2 : ZMod 402753765797) ^ 12 = 4096 := by
        calc
          (2 : ZMod 402753765797) ^ 12 = (2 : ZMod 402753765797) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 6 * (2 : ZMod 402753765797) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_3_2]; decide
      have factor_3_4 : (2 : ZMod 402753765797) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 402753765797) ^ 25 = (2 : ZMod 402753765797) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 12 * (2 : ZMod 402753765797) ^ 12) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [factor_3_3]; decide
      have factor_3_5 : (2 : ZMod 402753765797) ^ 50 = 203131440009 := by
        calc
          (2 : ZMod 402753765797) ^ 50 = (2 : ZMod 402753765797) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 25 * (2 : ZMod 402753765797) ^ 25 := by rw [pow_add]
          _ = 203131440009 := by rw [factor_3_4]; decide
      have factor_3_6 : (2 : ZMod 402753765797) ^ 101 = 388736124649 := by
        calc
          (2 : ZMod 402753765797) ^ 101 = (2 : ZMod 402753765797) ^ (50 + 50 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 50 * (2 : ZMod 402753765797) ^ 50) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 388736124649 := by rw [factor_3_5]; decide
      have factor_3_7 : (2 : ZMod 402753765797) ^ 203 = 4136123877 := by
        calc
          (2 : ZMod 402753765797) ^ 203 = (2 : ZMod 402753765797) ^ (101 + 101 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 101 * (2 : ZMod 402753765797) ^ 101) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 4136123877 := by rw [factor_3_6]; decide
      have factor_3_8 : (2 : ZMod 402753765797) ^ 406 = 334480199457 := by
        calc
          (2 : ZMod 402753765797) ^ 406 = (2 : ZMod 402753765797) ^ (203 + 203) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 203 * (2 : ZMod 402753765797) ^ 203 := by rw [pow_add]
          _ = 334480199457 := by rw [factor_3_7]; decide
      have factor_3_9 : (2 : ZMod 402753765797) ^ 813 = 308455049144 := by
        calc
          (2 : ZMod 402753765797) ^ 813 = (2 : ZMod 402753765797) ^ (406 + 406 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 406 * (2 : ZMod 402753765797) ^ 406) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 308455049144 := by rw [factor_3_8]; decide
      have factor_3_10 : (2 : ZMod 402753765797) ^ 1627 = 10160615562 := by
        calc
          (2 : ZMod 402753765797) ^ 1627 = (2 : ZMod 402753765797) ^ (813 + 813 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 813 * (2 : ZMod 402753765797) ^ 813) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 10160615562 := by rw [factor_3_9]; decide
      have factor_3_11 : (2 : ZMod 402753765797) ^ 3255 = 402117149198 := by
        calc
          (2 : ZMod 402753765797) ^ 3255 = (2 : ZMod 402753765797) ^ (1627 + 1627 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 1627 * (2 : ZMod 402753765797) ^ 1627) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 402117149198 := by rw [factor_3_10]; decide
      have factor_3_12 : (2 : ZMod 402753765797) ^ 6511 = 102397432846 := by
        calc
          (2 : ZMod 402753765797) ^ 6511 = (2 : ZMod 402753765797) ^ (3255 + 3255 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = ((2 : ZMod 402753765797) ^ 3255 * (2 : ZMod 402753765797) ^ 3255) * (2 : ZMod 402753765797) := by rw [pow_succ, pow_add]
          _ = 102397432846 := by rw [factor_3_11]; decide
      have factor_3_13 : (2 : ZMod 402753765797) ^ 13022 = 373859796011 := by
        calc
          (2 : ZMod 402753765797) ^ 13022 = (2 : ZMod 402753765797) ^ (6511 + 6511) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 6511 * (2 : ZMod 402753765797) ^ 6511 := by rw [pow_add]
          _ = 373859796011 := by rw [factor_3_12]; decide
      have factor_3_14 : (2 : ZMod 402753765797) ^ 26044 = 107678454810 := by
        calc
          (2 : ZMod 402753765797) ^ 26044 = (2 : ZMod 402753765797) ^ (13022 + 13022) :=
            congrArg (fun n : ℕ => (2 : ZMod 402753765797) ^ n) (by norm_num)
          _ = (2 : ZMod 402753765797) ^ 13022 * (2 : ZMod 402753765797) ^ 13022 := by rw [pow_add]
          _ = 107678454810 := by rw [factor_3_13]; decide
      change (2 : ZMod 402753765797) ^ 26044 ≠ 1
      rw [factor_3_14]
      decide

#print axioms prime_lucas_402753765797

end TotientTailPeriodKiller
end Erdos249257
