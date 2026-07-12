import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime79719069217

/-! A bounded Lucas certificate for one t=37 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_3667077183983 : Nat.Prime 3667077183983 := by
  apply lucas_primality 3667077183983 (10 : ZMod 3667077183983)
  ·
      have fermat_0 : (10 : ZMod 3667077183983) ^ 1 = 10 := by norm_num
      have fermat_1 : (10 : ZMod 3667077183983) ^ 3 = 1000 := by
        calc
          (10 : ZMod 3667077183983) ^ 3 = (10 : ZMod 3667077183983) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 1 * (10 : ZMod 3667077183983) ^ 1) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [fermat_0]; decide
      have fermat_2 : (10 : ZMod 3667077183983) ^ 6 = 1000000 := by
        calc
          (10 : ZMod 3667077183983) ^ 6 = (10 : ZMod 3667077183983) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 3 * (10 : ZMod 3667077183983) ^ 3 := by rw [pow_add]
          _ = 1000000 := by rw [fermat_1]; decide
      have fermat_3 : (10 : ZMod 3667077183983) ^ 13 = 2665845632034 := by
        calc
          (10 : ZMod 3667077183983) ^ 13 = (10 : ZMod 3667077183983) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 6 * (10 : ZMod 3667077183983) ^ 6) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 2665845632034 := by rw [fermat_2]; decide
      have fermat_4 : (10 : ZMod 3667077183983) ^ 26 = 23042499405 := by
        calc
          (10 : ZMod 3667077183983) ^ 26 = (10 : ZMod 3667077183983) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 13 * (10 : ZMod 3667077183983) ^ 13 := by rw [pow_add]
          _ = 23042499405 := by rw [fermat_3]; decide
      have fermat_5 : (10 : ZMod 3667077183983) ^ 53 = 851558047462 := by
        calc
          (10 : ZMod 3667077183983) ^ 53 = (10 : ZMod 3667077183983) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 26 * (10 : ZMod 3667077183983) ^ 26) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 851558047462 := by rw [fermat_4]; decide
      have fermat_6 : (10 : ZMod 3667077183983) ^ 106 = 2961332370233 := by
        calc
          (10 : ZMod 3667077183983) ^ 106 = (10 : ZMod 3667077183983) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 53 * (10 : ZMod 3667077183983) ^ 53 := by rw [pow_add]
          _ = 2961332370233 := by rw [fermat_5]; decide
      have fermat_7 : (10 : ZMod 3667077183983) ^ 213 = 2318744809432 := by
        calc
          (10 : ZMod 3667077183983) ^ 213 = (10 : ZMod 3667077183983) ^ (106 + 106 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 106 * (10 : ZMod 3667077183983) ^ 106) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 2318744809432 := by rw [fermat_6]; decide
      have fermat_8 : (10 : ZMod 3667077183983) ^ 426 = 282361980958 := by
        calc
          (10 : ZMod 3667077183983) ^ 426 = (10 : ZMod 3667077183983) ^ (213 + 213) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 213 * (10 : ZMod 3667077183983) ^ 213 := by rw [pow_add]
          _ = 282361980958 := by rw [fermat_7]; decide
      have fermat_9 : (10 : ZMod 3667077183983) ^ 853 = 3286424893460 := by
        calc
          (10 : ZMod 3667077183983) ^ 853 = (10 : ZMod 3667077183983) ^ (426 + 426 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 426 * (10 : ZMod 3667077183983) ^ 426) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 3286424893460 := by rw [fermat_8]; decide
      have fermat_10 : (10 : ZMod 3667077183983) ^ 1707 = 995417474753 := by
        calc
          (10 : ZMod 3667077183983) ^ 1707 = (10 : ZMod 3667077183983) ^ (853 + 853 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 853 * (10 : ZMod 3667077183983) ^ 853) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 995417474753 := by rw [fermat_9]; decide
      have fermat_11 : (10 : ZMod 3667077183983) ^ 3415 = 20205742580 := by
        calc
          (10 : ZMod 3667077183983) ^ 3415 = (10 : ZMod 3667077183983) ^ (1707 + 1707 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 1707 * (10 : ZMod 3667077183983) ^ 1707) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 20205742580 := by rw [fermat_10]; decide
      have fermat_12 : (10 : ZMod 3667077183983) ^ 6830 = 821697390101 := by
        calc
          (10 : ZMod 3667077183983) ^ 6830 = (10 : ZMod 3667077183983) ^ (3415 + 3415) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 3415 * (10 : ZMod 3667077183983) ^ 3415 := by rw [pow_add]
          _ = 821697390101 := by rw [fermat_11]; decide
      have fermat_13 : (10 : ZMod 3667077183983) ^ 13660 = 3234610491108 := by
        calc
          (10 : ZMod 3667077183983) ^ 13660 = (10 : ZMod 3667077183983) ^ (6830 + 6830) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 6830 * (10 : ZMod 3667077183983) ^ 6830 := by rw [pow_add]
          _ = 3234610491108 := by rw [fermat_12]; decide
      have fermat_14 : (10 : ZMod 3667077183983) ^ 27321 = 646231462506 := by
        calc
          (10 : ZMod 3667077183983) ^ 27321 = (10 : ZMod 3667077183983) ^ (13660 + 13660 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 13660 * (10 : ZMod 3667077183983) ^ 13660) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 646231462506 := by rw [fermat_13]; decide
      have fermat_15 : (10 : ZMod 3667077183983) ^ 54643 = 3548511331945 := by
        calc
          (10 : ZMod 3667077183983) ^ 54643 = (10 : ZMod 3667077183983) ^ (27321 + 27321 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 27321 * (10 : ZMod 3667077183983) ^ 27321) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 3548511331945 := by rw [fermat_14]; decide
      have fermat_16 : (10 : ZMod 3667077183983) ^ 109287 = 2321236906456 := by
        calc
          (10 : ZMod 3667077183983) ^ 109287 = (10 : ZMod 3667077183983) ^ (54643 + 54643 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 54643 * (10 : ZMod 3667077183983) ^ 54643) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 2321236906456 := by rw [fermat_15]; decide
      have fermat_17 : (10 : ZMod 3667077183983) ^ 218574 = 3573021344967 := by
        calc
          (10 : ZMod 3667077183983) ^ 218574 = (10 : ZMod 3667077183983) ^ (109287 + 109287) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 109287 * (10 : ZMod 3667077183983) ^ 109287 := by rw [pow_add]
          _ = 3573021344967 := by rw [fermat_16]; decide
      have fermat_18 : (10 : ZMod 3667077183983) ^ 437149 = 1537831139573 := by
        calc
          (10 : ZMod 3667077183983) ^ 437149 = (10 : ZMod 3667077183983) ^ (218574 + 218574 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 218574 * (10 : ZMod 3667077183983) ^ 218574) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 1537831139573 := by rw [fermat_17]; decide
      have fermat_19 : (10 : ZMod 3667077183983) ^ 874299 = 2583671838610 := by
        calc
          (10 : ZMod 3667077183983) ^ 874299 = (10 : ZMod 3667077183983) ^ (437149 + 437149 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 437149 * (10 : ZMod 3667077183983) ^ 437149) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 2583671838610 := by rw [fermat_18]; decide
      have fermat_20 : (10 : ZMod 3667077183983) ^ 1748598 = 999705534232 := by
        calc
          (10 : ZMod 3667077183983) ^ 1748598 = (10 : ZMod 3667077183983) ^ (874299 + 874299) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 874299 * (10 : ZMod 3667077183983) ^ 874299 := by rw [pow_add]
          _ = 999705534232 := by rw [fermat_19]; decide
      have fermat_21 : (10 : ZMod 3667077183983) ^ 3497197 = 3609178729037 := by
        calc
          (10 : ZMod 3667077183983) ^ 3497197 = (10 : ZMod 3667077183983) ^ (1748598 + 1748598 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 1748598 * (10 : ZMod 3667077183983) ^ 1748598) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 3609178729037 := by rw [fermat_20]; decide
      have fermat_22 : (10 : ZMod 3667077183983) ^ 6994394 = 2477275389314 := by
        calc
          (10 : ZMod 3667077183983) ^ 6994394 = (10 : ZMod 3667077183983) ^ (3497197 + 3497197) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 3497197 * (10 : ZMod 3667077183983) ^ 3497197 := by rw [pow_add]
          _ = 2477275389314 := by rw [fermat_21]; decide
      have fermat_23 : (10 : ZMod 3667077183983) ^ 13988789 = 45901226491 := by
        calc
          (10 : ZMod 3667077183983) ^ 13988789 = (10 : ZMod 3667077183983) ^ (6994394 + 6994394 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 6994394 * (10 : ZMod 3667077183983) ^ 6994394) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 45901226491 := by rw [fermat_22]; decide
      have fermat_24 : (10 : ZMod 3667077183983) ^ 27977578 = 1607175154823 := by
        calc
          (10 : ZMod 3667077183983) ^ 27977578 = (10 : ZMod 3667077183983) ^ (13988789 + 13988789) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 13988789 * (10 : ZMod 3667077183983) ^ 13988789 := by rw [pow_add]
          _ = 1607175154823 := by rw [fermat_23]; decide
      have fermat_25 : (10 : ZMod 3667077183983) ^ 55955157 = 570686239395 := by
        calc
          (10 : ZMod 3667077183983) ^ 55955157 = (10 : ZMod 3667077183983) ^ (27977578 + 27977578 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 27977578 * (10 : ZMod 3667077183983) ^ 27977578) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 570686239395 := by rw [fermat_24]; decide
      have fermat_26 : (10 : ZMod 3667077183983) ^ 111910314 = 3636559720212 := by
        calc
          (10 : ZMod 3667077183983) ^ 111910314 = (10 : ZMod 3667077183983) ^ (55955157 + 55955157) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 55955157 * (10 : ZMod 3667077183983) ^ 55955157 := by rw [pow_add]
          _ = 3636559720212 := by rw [fermat_25]; decide
      have fermat_27 : (10 : ZMod 3667077183983) ^ 223820628 = 1274681022817 := by
        calc
          (10 : ZMod 3667077183983) ^ 223820628 = (10 : ZMod 3667077183983) ^ (111910314 + 111910314) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 111910314 * (10 : ZMod 3667077183983) ^ 111910314 := by rw [pow_add]
          _ = 1274681022817 := by rw [fermat_26]; decide
      have fermat_28 : (10 : ZMod 3667077183983) ^ 447641257 = 2667825553959 := by
        calc
          (10 : ZMod 3667077183983) ^ 447641257 = (10 : ZMod 3667077183983) ^ (223820628 + 223820628 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 223820628 * (10 : ZMod 3667077183983) ^ 223820628) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 2667825553959 := by rw [fermat_27]; decide
      have fermat_29 : (10 : ZMod 3667077183983) ^ 895282515 = 247859104701 := by
        calc
          (10 : ZMod 3667077183983) ^ 895282515 = (10 : ZMod 3667077183983) ^ (447641257 + 447641257 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 447641257 * (10 : ZMod 3667077183983) ^ 447641257) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 247859104701 := by rw [fermat_28]; decide
      have fermat_30 : (10 : ZMod 3667077183983) ^ 1790565031 = 1863912594771 := by
        calc
          (10 : ZMod 3667077183983) ^ 1790565031 = (10 : ZMod 3667077183983) ^ (895282515 + 895282515 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 895282515 * (10 : ZMod 3667077183983) ^ 895282515) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 1863912594771 := by rw [fermat_29]; decide
      have fermat_31 : (10 : ZMod 3667077183983) ^ 3581130062 = 1942514711340 := by
        calc
          (10 : ZMod 3667077183983) ^ 3581130062 = (10 : ZMod 3667077183983) ^ (1790565031 + 1790565031) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 1790565031 * (10 : ZMod 3667077183983) ^ 1790565031 := by rw [pow_add]
          _ = 1942514711340 := by rw [fermat_30]; decide
      have fermat_32 : (10 : ZMod 3667077183983) ^ 7162260124 = 2750359538778 := by
        calc
          (10 : ZMod 3667077183983) ^ 7162260124 = (10 : ZMod 3667077183983) ^ (3581130062 + 3581130062) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 3581130062 * (10 : ZMod 3667077183983) ^ 3581130062 := by rw [pow_add]
          _ = 2750359538778 := by rw [fermat_31]; decide
      have fermat_33 : (10 : ZMod 3667077183983) ^ 14324520249 = 2347260766520 := by
        calc
          (10 : ZMod 3667077183983) ^ 14324520249 = (10 : ZMod 3667077183983) ^ (7162260124 + 7162260124 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 7162260124 * (10 : ZMod 3667077183983) ^ 7162260124) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 2347260766520 := by rw [fermat_32]; decide
      have fermat_34 : (10 : ZMod 3667077183983) ^ 28649040499 = 17074866049 := by
        calc
          (10 : ZMod 3667077183983) ^ 28649040499 = (10 : ZMod 3667077183983) ^ (14324520249 + 14324520249 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 14324520249 * (10 : ZMod 3667077183983) ^ 14324520249) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 17074866049 := by rw [fermat_33]; decide
      have fermat_35 : (10 : ZMod 3667077183983) ^ 57298080999 = 2365649997665 := by
        calc
          (10 : ZMod 3667077183983) ^ 57298080999 = (10 : ZMod 3667077183983) ^ (28649040499 + 28649040499 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 28649040499 * (10 : ZMod 3667077183983) ^ 28649040499) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 2365649997665 := by rw [fermat_34]; decide
      have fermat_36 : (10 : ZMod 3667077183983) ^ 114596161999 = 1598407831989 := by
        calc
          (10 : ZMod 3667077183983) ^ 114596161999 = (10 : ZMod 3667077183983) ^ (57298080999 + 57298080999 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 57298080999 * (10 : ZMod 3667077183983) ^ 57298080999) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 1598407831989 := by rw [fermat_35]; decide
      have fermat_37 : (10 : ZMod 3667077183983) ^ 229192323998 = 1003764711921 := by
        calc
          (10 : ZMod 3667077183983) ^ 229192323998 = (10 : ZMod 3667077183983) ^ (114596161999 + 114596161999) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 114596161999 * (10 : ZMod 3667077183983) ^ 114596161999 := by rw [pow_add]
          _ = 1003764711921 := by rw [fermat_36]; decide
      have fermat_38 : (10 : ZMod 3667077183983) ^ 458384647997 = 1583908654577 := by
        calc
          (10 : ZMod 3667077183983) ^ 458384647997 = (10 : ZMod 3667077183983) ^ (229192323998 + 229192323998 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 229192323998 * (10 : ZMod 3667077183983) ^ 229192323998) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 1583908654577 := by rw [fermat_37]; decide
      have fermat_39 : (10 : ZMod 3667077183983) ^ 916769295995 = 2886908563116 := by
        calc
          (10 : ZMod 3667077183983) ^ 916769295995 = (10 : ZMod 3667077183983) ^ (458384647997 + 458384647997 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 458384647997 * (10 : ZMod 3667077183983) ^ 458384647997) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 2886908563116 := by rw [fermat_38]; decide
      have fermat_40 : (10 : ZMod 3667077183983) ^ 1833538591991 = 3667077183982 := by
        calc
          (10 : ZMod 3667077183983) ^ 1833538591991 = (10 : ZMod 3667077183983) ^ (916769295995 + 916769295995 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 916769295995 * (10 : ZMod 3667077183983) ^ 916769295995) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 3667077183982 := by rw [fermat_39]; decide
      have fermat_41 : (10 : ZMod 3667077183983) ^ 3667077183982 = 1 := by
        calc
          (10 : ZMod 3667077183983) ^ 3667077183982 = (10 : ZMod 3667077183983) ^ (1833538591991 + 1833538591991) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 1833538591991 * (10 : ZMod 3667077183983) ^ 1833538591991 := by rw [pow_add]
          _ = 1 := by rw [fermat_40]; decide
      simpa using fermat_41
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (23, 1), (79719069217, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (23, 1), (79719069217, 1)] : List FactorBlock).map factorBlockValue).prod = 3667077183983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · norm_num
      · norm_num
      · exact prime_lucas_79719069217) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    ·
      have factor_0_0 : (10 : ZMod 3667077183983) ^ 1 = 10 := by norm_num
      have factor_0_1 : (10 : ZMod 3667077183983) ^ 3 = 1000 := by
        calc
          (10 : ZMod 3667077183983) ^ 3 = (10 : ZMod 3667077183983) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 1 * (10 : ZMod 3667077183983) ^ 1) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 1000 := by rw [factor_0_0]; decide
      have factor_0_2 : (10 : ZMod 3667077183983) ^ 6 = 1000000 := by
        calc
          (10 : ZMod 3667077183983) ^ 6 = (10 : ZMod 3667077183983) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 3 * (10 : ZMod 3667077183983) ^ 3 := by rw [pow_add]
          _ = 1000000 := by rw [factor_0_1]; decide
      have factor_0_3 : (10 : ZMod 3667077183983) ^ 13 = 2665845632034 := by
        calc
          (10 : ZMod 3667077183983) ^ 13 = (10 : ZMod 3667077183983) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 6 * (10 : ZMod 3667077183983) ^ 6) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 2665845632034 := by rw [factor_0_2]; decide
      have factor_0_4 : (10 : ZMod 3667077183983) ^ 26 = 23042499405 := by
        calc
          (10 : ZMod 3667077183983) ^ 26 = (10 : ZMod 3667077183983) ^ (13 + 13) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 13 * (10 : ZMod 3667077183983) ^ 13 := by rw [pow_add]
          _ = 23042499405 := by rw [factor_0_3]; decide
      have factor_0_5 : (10 : ZMod 3667077183983) ^ 53 = 851558047462 := by
        calc
          (10 : ZMod 3667077183983) ^ 53 = (10 : ZMod 3667077183983) ^ (26 + 26 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 26 * (10 : ZMod 3667077183983) ^ 26) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 851558047462 := by rw [factor_0_4]; decide
      have factor_0_6 : (10 : ZMod 3667077183983) ^ 106 = 2961332370233 := by
        calc
          (10 : ZMod 3667077183983) ^ 106 = (10 : ZMod 3667077183983) ^ (53 + 53) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 53 * (10 : ZMod 3667077183983) ^ 53 := by rw [pow_add]
          _ = 2961332370233 := by rw [factor_0_5]; decide
      have factor_0_7 : (10 : ZMod 3667077183983) ^ 213 = 2318744809432 := by
        calc
          (10 : ZMod 3667077183983) ^ 213 = (10 : ZMod 3667077183983) ^ (106 + 106 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 106 * (10 : ZMod 3667077183983) ^ 106) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 2318744809432 := by rw [factor_0_6]; decide
      have factor_0_8 : (10 : ZMod 3667077183983) ^ 426 = 282361980958 := by
        calc
          (10 : ZMod 3667077183983) ^ 426 = (10 : ZMod 3667077183983) ^ (213 + 213) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 213 * (10 : ZMod 3667077183983) ^ 213 := by rw [pow_add]
          _ = 282361980958 := by rw [factor_0_7]; decide
      have factor_0_9 : (10 : ZMod 3667077183983) ^ 853 = 3286424893460 := by
        calc
          (10 : ZMod 3667077183983) ^ 853 = (10 : ZMod 3667077183983) ^ (426 + 426 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 426 * (10 : ZMod 3667077183983) ^ 426) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 3286424893460 := by rw [factor_0_8]; decide
      have factor_0_10 : (10 : ZMod 3667077183983) ^ 1707 = 995417474753 := by
        calc
          (10 : ZMod 3667077183983) ^ 1707 = (10 : ZMod 3667077183983) ^ (853 + 853 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 853 * (10 : ZMod 3667077183983) ^ 853) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 995417474753 := by rw [factor_0_9]; decide
      have factor_0_11 : (10 : ZMod 3667077183983) ^ 3415 = 20205742580 := by
        calc
          (10 : ZMod 3667077183983) ^ 3415 = (10 : ZMod 3667077183983) ^ (1707 + 1707 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 1707 * (10 : ZMod 3667077183983) ^ 1707) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 20205742580 := by rw [factor_0_10]; decide
      have factor_0_12 : (10 : ZMod 3667077183983) ^ 6830 = 821697390101 := by
        calc
          (10 : ZMod 3667077183983) ^ 6830 = (10 : ZMod 3667077183983) ^ (3415 + 3415) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 3415 * (10 : ZMod 3667077183983) ^ 3415 := by rw [pow_add]
          _ = 821697390101 := by rw [factor_0_11]; decide
      have factor_0_13 : (10 : ZMod 3667077183983) ^ 13660 = 3234610491108 := by
        calc
          (10 : ZMod 3667077183983) ^ 13660 = (10 : ZMod 3667077183983) ^ (6830 + 6830) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 6830 * (10 : ZMod 3667077183983) ^ 6830 := by rw [pow_add]
          _ = 3234610491108 := by rw [factor_0_12]; decide
      have factor_0_14 : (10 : ZMod 3667077183983) ^ 27321 = 646231462506 := by
        calc
          (10 : ZMod 3667077183983) ^ 27321 = (10 : ZMod 3667077183983) ^ (13660 + 13660 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 13660 * (10 : ZMod 3667077183983) ^ 13660) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 646231462506 := by rw [factor_0_13]; decide
      have factor_0_15 : (10 : ZMod 3667077183983) ^ 54643 = 3548511331945 := by
        calc
          (10 : ZMod 3667077183983) ^ 54643 = (10 : ZMod 3667077183983) ^ (27321 + 27321 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 27321 * (10 : ZMod 3667077183983) ^ 27321) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 3548511331945 := by rw [factor_0_14]; decide
      have factor_0_16 : (10 : ZMod 3667077183983) ^ 109287 = 2321236906456 := by
        calc
          (10 : ZMod 3667077183983) ^ 109287 = (10 : ZMod 3667077183983) ^ (54643 + 54643 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 54643 * (10 : ZMod 3667077183983) ^ 54643) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 2321236906456 := by rw [factor_0_15]; decide
      have factor_0_17 : (10 : ZMod 3667077183983) ^ 218574 = 3573021344967 := by
        calc
          (10 : ZMod 3667077183983) ^ 218574 = (10 : ZMod 3667077183983) ^ (109287 + 109287) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 109287 * (10 : ZMod 3667077183983) ^ 109287 := by rw [pow_add]
          _ = 3573021344967 := by rw [factor_0_16]; decide
      have factor_0_18 : (10 : ZMod 3667077183983) ^ 437149 = 1537831139573 := by
        calc
          (10 : ZMod 3667077183983) ^ 437149 = (10 : ZMod 3667077183983) ^ (218574 + 218574 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 218574 * (10 : ZMod 3667077183983) ^ 218574) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 1537831139573 := by rw [factor_0_17]; decide
      have factor_0_19 : (10 : ZMod 3667077183983) ^ 874299 = 2583671838610 := by
        calc
          (10 : ZMod 3667077183983) ^ 874299 = (10 : ZMod 3667077183983) ^ (437149 + 437149 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 437149 * (10 : ZMod 3667077183983) ^ 437149) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 2583671838610 := by rw [factor_0_18]; decide
      have factor_0_20 : (10 : ZMod 3667077183983) ^ 1748598 = 999705534232 := by
        calc
          (10 : ZMod 3667077183983) ^ 1748598 = (10 : ZMod 3667077183983) ^ (874299 + 874299) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 874299 * (10 : ZMod 3667077183983) ^ 874299 := by rw [pow_add]
          _ = 999705534232 := by rw [factor_0_19]; decide
      have factor_0_21 : (10 : ZMod 3667077183983) ^ 3497197 = 3609178729037 := by
        calc
          (10 : ZMod 3667077183983) ^ 3497197 = (10 : ZMod 3667077183983) ^ (1748598 + 1748598 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 1748598 * (10 : ZMod 3667077183983) ^ 1748598) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 3609178729037 := by rw [factor_0_20]; decide
      have factor_0_22 : (10 : ZMod 3667077183983) ^ 6994394 = 2477275389314 := by
        calc
          (10 : ZMod 3667077183983) ^ 6994394 = (10 : ZMod 3667077183983) ^ (3497197 + 3497197) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 3497197 * (10 : ZMod 3667077183983) ^ 3497197 := by rw [pow_add]
          _ = 2477275389314 := by rw [factor_0_21]; decide
      have factor_0_23 : (10 : ZMod 3667077183983) ^ 13988789 = 45901226491 := by
        calc
          (10 : ZMod 3667077183983) ^ 13988789 = (10 : ZMod 3667077183983) ^ (6994394 + 6994394 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 6994394 * (10 : ZMod 3667077183983) ^ 6994394) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 45901226491 := by rw [factor_0_22]; decide
      have factor_0_24 : (10 : ZMod 3667077183983) ^ 27977578 = 1607175154823 := by
        calc
          (10 : ZMod 3667077183983) ^ 27977578 = (10 : ZMod 3667077183983) ^ (13988789 + 13988789) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 13988789 * (10 : ZMod 3667077183983) ^ 13988789 := by rw [pow_add]
          _ = 1607175154823 := by rw [factor_0_23]; decide
      have factor_0_25 : (10 : ZMod 3667077183983) ^ 55955157 = 570686239395 := by
        calc
          (10 : ZMod 3667077183983) ^ 55955157 = (10 : ZMod 3667077183983) ^ (27977578 + 27977578 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 27977578 * (10 : ZMod 3667077183983) ^ 27977578) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 570686239395 := by rw [factor_0_24]; decide
      have factor_0_26 : (10 : ZMod 3667077183983) ^ 111910314 = 3636559720212 := by
        calc
          (10 : ZMod 3667077183983) ^ 111910314 = (10 : ZMod 3667077183983) ^ (55955157 + 55955157) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 55955157 * (10 : ZMod 3667077183983) ^ 55955157 := by rw [pow_add]
          _ = 3636559720212 := by rw [factor_0_25]; decide
      have factor_0_27 : (10 : ZMod 3667077183983) ^ 223820628 = 1274681022817 := by
        calc
          (10 : ZMod 3667077183983) ^ 223820628 = (10 : ZMod 3667077183983) ^ (111910314 + 111910314) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 111910314 * (10 : ZMod 3667077183983) ^ 111910314 := by rw [pow_add]
          _ = 1274681022817 := by rw [factor_0_26]; decide
      have factor_0_28 : (10 : ZMod 3667077183983) ^ 447641257 = 2667825553959 := by
        calc
          (10 : ZMod 3667077183983) ^ 447641257 = (10 : ZMod 3667077183983) ^ (223820628 + 223820628 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 223820628 * (10 : ZMod 3667077183983) ^ 223820628) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 2667825553959 := by rw [factor_0_27]; decide
      have factor_0_29 : (10 : ZMod 3667077183983) ^ 895282515 = 247859104701 := by
        calc
          (10 : ZMod 3667077183983) ^ 895282515 = (10 : ZMod 3667077183983) ^ (447641257 + 447641257 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 447641257 * (10 : ZMod 3667077183983) ^ 447641257) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 247859104701 := by rw [factor_0_28]; decide
      have factor_0_30 : (10 : ZMod 3667077183983) ^ 1790565031 = 1863912594771 := by
        calc
          (10 : ZMod 3667077183983) ^ 1790565031 = (10 : ZMod 3667077183983) ^ (895282515 + 895282515 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 895282515 * (10 : ZMod 3667077183983) ^ 895282515) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 1863912594771 := by rw [factor_0_29]; decide
      have factor_0_31 : (10 : ZMod 3667077183983) ^ 3581130062 = 1942514711340 := by
        calc
          (10 : ZMod 3667077183983) ^ 3581130062 = (10 : ZMod 3667077183983) ^ (1790565031 + 1790565031) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 1790565031 * (10 : ZMod 3667077183983) ^ 1790565031 := by rw [pow_add]
          _ = 1942514711340 := by rw [factor_0_30]; decide
      have factor_0_32 : (10 : ZMod 3667077183983) ^ 7162260124 = 2750359538778 := by
        calc
          (10 : ZMod 3667077183983) ^ 7162260124 = (10 : ZMod 3667077183983) ^ (3581130062 + 3581130062) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 3581130062 * (10 : ZMod 3667077183983) ^ 3581130062 := by rw [pow_add]
          _ = 2750359538778 := by rw [factor_0_31]; decide
      have factor_0_33 : (10 : ZMod 3667077183983) ^ 14324520249 = 2347260766520 := by
        calc
          (10 : ZMod 3667077183983) ^ 14324520249 = (10 : ZMod 3667077183983) ^ (7162260124 + 7162260124 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 7162260124 * (10 : ZMod 3667077183983) ^ 7162260124) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 2347260766520 := by rw [factor_0_32]; decide
      have factor_0_34 : (10 : ZMod 3667077183983) ^ 28649040499 = 17074866049 := by
        calc
          (10 : ZMod 3667077183983) ^ 28649040499 = (10 : ZMod 3667077183983) ^ (14324520249 + 14324520249 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 14324520249 * (10 : ZMod 3667077183983) ^ 14324520249) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 17074866049 := by rw [factor_0_33]; decide
      have factor_0_35 : (10 : ZMod 3667077183983) ^ 57298080999 = 2365649997665 := by
        calc
          (10 : ZMod 3667077183983) ^ 57298080999 = (10 : ZMod 3667077183983) ^ (28649040499 + 28649040499 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 28649040499 * (10 : ZMod 3667077183983) ^ 28649040499) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 2365649997665 := by rw [factor_0_34]; decide
      have factor_0_36 : (10 : ZMod 3667077183983) ^ 114596161999 = 1598407831989 := by
        calc
          (10 : ZMod 3667077183983) ^ 114596161999 = (10 : ZMod 3667077183983) ^ (57298080999 + 57298080999 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 57298080999 * (10 : ZMod 3667077183983) ^ 57298080999) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 1598407831989 := by rw [factor_0_35]; decide
      have factor_0_37 : (10 : ZMod 3667077183983) ^ 229192323998 = 1003764711921 := by
        calc
          (10 : ZMod 3667077183983) ^ 229192323998 = (10 : ZMod 3667077183983) ^ (114596161999 + 114596161999) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 114596161999 * (10 : ZMod 3667077183983) ^ 114596161999 := by rw [pow_add]
          _ = 1003764711921 := by rw [factor_0_36]; decide
      have factor_0_38 : (10 : ZMod 3667077183983) ^ 458384647997 = 1583908654577 := by
        calc
          (10 : ZMod 3667077183983) ^ 458384647997 = (10 : ZMod 3667077183983) ^ (229192323998 + 229192323998 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 229192323998 * (10 : ZMod 3667077183983) ^ 229192323998) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 1583908654577 := by rw [factor_0_37]; decide
      have factor_0_39 : (10 : ZMod 3667077183983) ^ 916769295995 = 2886908563116 := by
        calc
          (10 : ZMod 3667077183983) ^ 916769295995 = (10 : ZMod 3667077183983) ^ (458384647997 + 458384647997 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 458384647997 * (10 : ZMod 3667077183983) ^ 458384647997) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 2886908563116 := by rw [factor_0_38]; decide
      have factor_0_40 : (10 : ZMod 3667077183983) ^ 1833538591991 = 3667077183982 := by
        calc
          (10 : ZMod 3667077183983) ^ 1833538591991 = (10 : ZMod 3667077183983) ^ (916769295995 + 916769295995 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 916769295995 * (10 : ZMod 3667077183983) ^ 916769295995) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 3667077183982 := by rw [factor_0_39]; decide
      change (10 : ZMod 3667077183983) ^ 1833538591991 ≠ 1
      rw [factor_0_40]
      decide
    ·
      have factor_1_0 : (10 : ZMod 3667077183983) ^ 1 = 10 := by norm_num
      have factor_1_1 : (10 : ZMod 3667077183983) ^ 2 = 100 := by
        calc
          (10 : ZMod 3667077183983) ^ 2 = (10 : ZMod 3667077183983) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 1 * (10 : ZMod 3667077183983) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_1_0]; decide
      have factor_1_2 : (10 : ZMod 3667077183983) ^ 4 = 10000 := by
        calc
          (10 : ZMod 3667077183983) ^ 4 = (10 : ZMod 3667077183983) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 2 * (10 : ZMod 3667077183983) ^ 2 := by rw [pow_add]
          _ = 10000 := by rw [factor_1_1]; decide
      have factor_1_3 : (10 : ZMod 3667077183983) ^ 9 = 1000000000 := by
        calc
          (10 : ZMod 3667077183983) ^ 9 = (10 : ZMod 3667077183983) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 4 * (10 : ZMod 3667077183983) ^ 4) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 1000000000 := by rw [factor_1_2]; decide
      have factor_1_4 : (10 : ZMod 3667077183983) ^ 18 = 2720236571832 := by
        calc
          (10 : ZMod 3667077183983) ^ 18 = (10 : ZMod 3667077183983) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 9 * (10 : ZMod 3667077183983) ^ 9 := by rw [pow_add]
          _ = 2720236571832 := by rw [factor_1_3]; decide
      have factor_1_5 : (10 : ZMod 3667077183983) ^ 37 = 243448160667 := by
        calc
          (10 : ZMod 3667077183983) ^ 37 = (10 : ZMod 3667077183983) ^ (18 + 18 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 18 * (10 : ZMod 3667077183983) ^ 18) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 243448160667 := by rw [factor_1_4]; decide
      have factor_1_6 : (10 : ZMod 3667077183983) ^ 74 = 2249154295551 := by
        calc
          (10 : ZMod 3667077183983) ^ 74 = (10 : ZMod 3667077183983) ^ (37 + 37) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 37 * (10 : ZMod 3667077183983) ^ 37 := by rw [pow_add]
          _ = 2249154295551 := by rw [factor_1_5]; decide
      have factor_1_7 : (10 : ZMod 3667077183983) ^ 148 = 3118757467495 := by
        calc
          (10 : ZMod 3667077183983) ^ 148 = (10 : ZMod 3667077183983) ^ (74 + 74) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 74 * (10 : ZMod 3667077183983) ^ 74 := by rw [pow_add]
          _ = 3118757467495 := by rw [factor_1_6]; decide
      have factor_1_8 : (10 : ZMod 3667077183983) ^ 296 = 2005309690874 := by
        calc
          (10 : ZMod 3667077183983) ^ 296 = (10 : ZMod 3667077183983) ^ (148 + 148) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 148 * (10 : ZMod 3667077183983) ^ 148 := by rw [pow_add]
          _ = 2005309690874 := by rw [factor_1_7]; decide
      have factor_1_9 : (10 : ZMod 3667077183983) ^ 593 = 3639106006587 := by
        calc
          (10 : ZMod 3667077183983) ^ 593 = (10 : ZMod 3667077183983) ^ (296 + 296 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 296 * (10 : ZMod 3667077183983) ^ 296) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 3639106006587 := by rw [factor_1_8]; decide
      have factor_1_10 : (10 : ZMod 3667077183983) ^ 1187 = 749699898832 := by
        calc
          (10 : ZMod 3667077183983) ^ 1187 = (10 : ZMod 3667077183983) ^ (593 + 593 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 593 * (10 : ZMod 3667077183983) ^ 593) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 749699898832 := by rw [factor_1_9]; decide
      have factor_1_11 : (10 : ZMod 3667077183983) ^ 2375 = 2927047480158 := by
        calc
          (10 : ZMod 3667077183983) ^ 2375 = (10 : ZMod 3667077183983) ^ (1187 + 1187 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 1187 * (10 : ZMod 3667077183983) ^ 1187) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 2927047480158 := by rw [factor_1_10]; decide
      have factor_1_12 : (10 : ZMod 3667077183983) ^ 4751 = 447610117056 := by
        calc
          (10 : ZMod 3667077183983) ^ 4751 = (10 : ZMod 3667077183983) ^ (2375 + 2375 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 2375 * (10 : ZMod 3667077183983) ^ 2375) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 447610117056 := by rw [factor_1_11]; decide
      have factor_1_13 : (10 : ZMod 3667077183983) ^ 9503 = 370842252260 := by
        calc
          (10 : ZMod 3667077183983) ^ 9503 = (10 : ZMod 3667077183983) ^ (4751 + 4751 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 4751 * (10 : ZMod 3667077183983) ^ 4751) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 370842252260 := by rw [factor_1_12]; decide
      have factor_1_14 : (10 : ZMod 3667077183983) ^ 19006 = 884712746847 := by
        calc
          (10 : ZMod 3667077183983) ^ 19006 = (10 : ZMod 3667077183983) ^ (9503 + 9503) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 9503 * (10 : ZMod 3667077183983) ^ 9503 := by rw [pow_add]
          _ = 884712746847 := by rw [factor_1_13]; decide
      have factor_1_15 : (10 : ZMod 3667077183983) ^ 38013 = 3230062479271 := by
        calc
          (10 : ZMod 3667077183983) ^ 38013 = (10 : ZMod 3667077183983) ^ (19006 + 19006 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 19006 * (10 : ZMod 3667077183983) ^ 19006) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 3230062479271 := by rw [factor_1_14]; decide
      have factor_1_16 : (10 : ZMod 3667077183983) ^ 76026 = 3466151496867 := by
        calc
          (10 : ZMod 3667077183983) ^ 76026 = (10 : ZMod 3667077183983) ^ (38013 + 38013) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 38013 * (10 : ZMod 3667077183983) ^ 38013 := by rw [pow_add]
          _ = 3466151496867 := by rw [factor_1_15]; decide
      have factor_1_17 : (10 : ZMod 3667077183983) ^ 152052 = 332029314969 := by
        calc
          (10 : ZMod 3667077183983) ^ 152052 = (10 : ZMod 3667077183983) ^ (76026 + 76026) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 76026 * (10 : ZMod 3667077183983) ^ 76026 := by rw [pow_add]
          _ = 332029314969 := by rw [factor_1_16]; decide
      have factor_1_18 : (10 : ZMod 3667077183983) ^ 304104 = 2085612360655 := by
        calc
          (10 : ZMod 3667077183983) ^ 304104 = (10 : ZMod 3667077183983) ^ (152052 + 152052) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 152052 * (10 : ZMod 3667077183983) ^ 152052 := by rw [pow_add]
          _ = 2085612360655 := by rw [factor_1_17]; decide
      have factor_1_19 : (10 : ZMod 3667077183983) ^ 608208 = 1645814579554 := by
        calc
          (10 : ZMod 3667077183983) ^ 608208 = (10 : ZMod 3667077183983) ^ (304104 + 304104) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 304104 * (10 : ZMod 3667077183983) ^ 304104 := by rw [pow_add]
          _ = 1645814579554 := by rw [factor_1_18]; decide
      have factor_1_20 : (10 : ZMod 3667077183983) ^ 1216416 = 2497244340689 := by
        calc
          (10 : ZMod 3667077183983) ^ 1216416 = (10 : ZMod 3667077183983) ^ (608208 + 608208) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 608208 * (10 : ZMod 3667077183983) ^ 608208 := by rw [pow_add]
          _ = 2497244340689 := by rw [factor_1_19]; decide
      have factor_1_21 : (10 : ZMod 3667077183983) ^ 2432832 = 2108475932116 := by
        calc
          (10 : ZMod 3667077183983) ^ 2432832 = (10 : ZMod 3667077183983) ^ (1216416 + 1216416) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 1216416 * (10 : ZMod 3667077183983) ^ 1216416 := by rw [pow_add]
          _ = 2108475932116 := by rw [factor_1_20]; decide
      have factor_1_22 : (10 : ZMod 3667077183983) ^ 4865665 = 3194496583811 := by
        calc
          (10 : ZMod 3667077183983) ^ 4865665 = (10 : ZMod 3667077183983) ^ (2432832 + 2432832 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 2432832 * (10 : ZMod 3667077183983) ^ 2432832) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 3194496583811 := by rw [factor_1_21]; decide
      have factor_1_23 : (10 : ZMod 3667077183983) ^ 9731331 = 318051621740 := by
        calc
          (10 : ZMod 3667077183983) ^ 9731331 = (10 : ZMod 3667077183983) ^ (4865665 + 4865665 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 4865665 * (10 : ZMod 3667077183983) ^ 4865665) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 318051621740 := by rw [factor_1_22]; decide
      have factor_1_24 : (10 : ZMod 3667077183983) ^ 19462663 = 167020717475 := by
        calc
          (10 : ZMod 3667077183983) ^ 19462663 = (10 : ZMod 3667077183983) ^ (9731331 + 9731331 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 9731331 * (10 : ZMod 3667077183983) ^ 9731331) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 167020717475 := by rw [factor_1_23]; decide
      have factor_1_25 : (10 : ZMod 3667077183983) ^ 38925326 = 1703466502312 := by
        calc
          (10 : ZMod 3667077183983) ^ 38925326 = (10 : ZMod 3667077183983) ^ (19462663 + 19462663) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 19462663 * (10 : ZMod 3667077183983) ^ 19462663 := by rw [pow_add]
          _ = 1703466502312 := by rw [factor_1_24]; decide
      have factor_1_26 : (10 : ZMod 3667077183983) ^ 77850653 = 1253444810344 := by
        calc
          (10 : ZMod 3667077183983) ^ 77850653 = (10 : ZMod 3667077183983) ^ (38925326 + 38925326 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 38925326 * (10 : ZMod 3667077183983) ^ 38925326) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 1253444810344 := by rw [factor_1_25]; decide
      have factor_1_27 : (10 : ZMod 3667077183983) ^ 155701307 = 3208260219192 := by
        calc
          (10 : ZMod 3667077183983) ^ 155701307 = (10 : ZMod 3667077183983) ^ (77850653 + 77850653 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 77850653 * (10 : ZMod 3667077183983) ^ 77850653) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 3208260219192 := by rw [factor_1_26]; decide
      have factor_1_28 : (10 : ZMod 3667077183983) ^ 311402614 = 1611157087469 := by
        calc
          (10 : ZMod 3667077183983) ^ 311402614 = (10 : ZMod 3667077183983) ^ (155701307 + 155701307) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 155701307 * (10 : ZMod 3667077183983) ^ 155701307 := by rw [pow_add]
          _ = 1611157087469 := by rw [factor_1_27]; decide
      have factor_1_29 : (10 : ZMod 3667077183983) ^ 622805228 = 3011111665992 := by
        calc
          (10 : ZMod 3667077183983) ^ 622805228 = (10 : ZMod 3667077183983) ^ (311402614 + 311402614) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 311402614 * (10 : ZMod 3667077183983) ^ 311402614 := by rw [pow_add]
          _ = 3011111665992 := by rw [factor_1_28]; decide
      have factor_1_30 : (10 : ZMod 3667077183983) ^ 1245610456 = 2928184884479 := by
        calc
          (10 : ZMod 3667077183983) ^ 1245610456 = (10 : ZMod 3667077183983) ^ (622805228 + 622805228) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 622805228 * (10 : ZMod 3667077183983) ^ 622805228 := by rw [pow_add]
          _ = 2928184884479 := by rw [factor_1_29]; decide
      have factor_1_31 : (10 : ZMod 3667077183983) ^ 2491220913 = 3520184224445 := by
        calc
          (10 : ZMod 3667077183983) ^ 2491220913 = (10 : ZMod 3667077183983) ^ (1245610456 + 1245610456 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 1245610456 * (10 : ZMod 3667077183983) ^ 1245610456) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 3520184224445 := by rw [factor_1_30]; decide
      have factor_1_32 : (10 : ZMod 3667077183983) ^ 4982441826 = 3514000967187 := by
        calc
          (10 : ZMod 3667077183983) ^ 4982441826 = (10 : ZMod 3667077183983) ^ (2491220913 + 2491220913) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 2491220913 * (10 : ZMod 3667077183983) ^ 2491220913 := by rw [pow_add]
          _ = 3514000967187 := by rw [factor_1_31]; decide
      have factor_1_33 : (10 : ZMod 3667077183983) ^ 9964883652 = 3289000145762 := by
        calc
          (10 : ZMod 3667077183983) ^ 9964883652 = (10 : ZMod 3667077183983) ^ (4982441826 + 4982441826) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 4982441826 * (10 : ZMod 3667077183983) ^ 4982441826 := by rw [pow_add]
          _ = 3289000145762 := by rw [factor_1_32]; decide
      have factor_1_34 : (10 : ZMod 3667077183983) ^ 19929767304 = 192165305433 := by
        calc
          (10 : ZMod 3667077183983) ^ 19929767304 = (10 : ZMod 3667077183983) ^ (9964883652 + 9964883652) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 9964883652 * (10 : ZMod 3667077183983) ^ 9964883652 := by rw [pow_add]
          _ = 192165305433 := by rw [factor_1_33]; decide
      have factor_1_35 : (10 : ZMod 3667077183983) ^ 39859534608 = 1932864530719 := by
        calc
          (10 : ZMod 3667077183983) ^ 39859534608 = (10 : ZMod 3667077183983) ^ (19929767304 + 19929767304) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 19929767304 * (10 : ZMod 3667077183983) ^ 19929767304 := by rw [pow_add]
          _ = 1932864530719 := by rw [factor_1_34]; decide
      have factor_1_36 : (10 : ZMod 3667077183983) ^ 79719069217 = 3640100822329 := by
        calc
          (10 : ZMod 3667077183983) ^ 79719069217 = (10 : ZMod 3667077183983) ^ (39859534608 + 39859534608 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 39859534608 * (10 : ZMod 3667077183983) ^ 39859534608) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 3640100822329 := by rw [factor_1_35]; decide
      have factor_1_37 : (10 : ZMod 3667077183983) ^ 159438138434 = 2752346623495 := by
        calc
          (10 : ZMod 3667077183983) ^ 159438138434 = (10 : ZMod 3667077183983) ^ (79719069217 + 79719069217) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 79719069217 * (10 : ZMod 3667077183983) ^ 79719069217 := by rw [pow_add]
          _ = 2752346623495 := by rw [factor_1_36]; decide
      change (10 : ZMod 3667077183983) ^ 159438138434 ≠ 1
      rw [factor_1_37]
      decide
    ·
      have factor_2_0 : (10 : ZMod 3667077183983) ^ 1 = 10 := by norm_num
      have factor_2_1 : (10 : ZMod 3667077183983) ^ 2 = 100 := by
        calc
          (10 : ZMod 3667077183983) ^ 2 = (10 : ZMod 3667077183983) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 1 * (10 : ZMod 3667077183983) ^ 1 := by rw [pow_add]
          _ = 100 := by rw [factor_2_0]; decide
      have factor_2_2 : (10 : ZMod 3667077183983) ^ 5 = 100000 := by
        calc
          (10 : ZMod 3667077183983) ^ 5 = (10 : ZMod 3667077183983) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 2 * (10 : ZMod 3667077183983) ^ 2) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 100000 := by rw [factor_2_1]; decide
      have factor_2_3 : (10 : ZMod 3667077183983) ^ 11 = 100000000000 := by
        calc
          (10 : ZMod 3667077183983) ^ 11 = (10 : ZMod 3667077183983) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 5 * (10 : ZMod 3667077183983) ^ 5) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 100000000000 := by rw [factor_2_2]; decide
      have factor_2_4 : (10 : ZMod 3667077183983) ^ 23 = 3538752525043 := by
        calc
          (10 : ZMod 3667077183983) ^ 23 = (10 : ZMod 3667077183983) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = ((10 : ZMod 3667077183983) ^ 11 * (10 : ZMod 3667077183983) ^ 11) * (10 : ZMod 3667077183983) := by rw [pow_succ, pow_add]
          _ = 3538752525043 := by rw [factor_2_3]; decide
      have factor_2_5 : (10 : ZMod 3667077183983) ^ 46 = 773784907840 := by
        calc
          (10 : ZMod 3667077183983) ^ 46 = (10 : ZMod 3667077183983) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (10 : ZMod 3667077183983) ^ n) (by norm_num)
          _ = (10 : ZMod 3667077183983) ^ 23 * (10 : ZMod 3667077183983) ^ 23 := by rw [pow_add]
          _ = 773784907840 := by rw [factor_2_4]; decide
      change (10 : ZMod 3667077183983) ^ 46 ≠ 1
      rw [factor_2_5]
      decide

#print axioms prime_lucas_3667077183983

end TotientTailPeriodKiller
end Erdos249257
