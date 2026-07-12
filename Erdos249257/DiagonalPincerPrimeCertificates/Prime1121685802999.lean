import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_1121685802999 : Nat.Prime 1121685802999 := by
  apply lucas_primality 1121685802999 (6 : ZMod 1121685802999)
  ·
      have fermat_0 : (6 : ZMod 1121685802999) ^ 1 = 6 := by norm_num
      have fermat_1 : (6 : ZMod 1121685802999) ^ 2 = 36 := by
        calc
          (6 : ZMod 1121685802999) ^ 2 = (6 : ZMod 1121685802999) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 1 * (6 : ZMod 1121685802999) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [fermat_0]; decide
      have fermat_2 : (6 : ZMod 1121685802999) ^ 4 = 1296 := by
        calc
          (6 : ZMod 1121685802999) ^ 4 = (6 : ZMod 1121685802999) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 2 * (6 : ZMod 1121685802999) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [fermat_1]; decide
      have fermat_3 : (6 : ZMod 1121685802999) ^ 8 = 1679616 := by
        calc
          (6 : ZMod 1121685802999) ^ 8 = (6 : ZMod 1121685802999) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 4 * (6 : ZMod 1121685802999) ^ 4 := by rw [pow_add]
          _ = 1679616 := by rw [fermat_2]; decide
      have fermat_4 : (6 : ZMod 1121685802999) ^ 16 = 577738301458 := by
        calc
          (6 : ZMod 1121685802999) ^ 16 = (6 : ZMod 1121685802999) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 8 * (6 : ZMod 1121685802999) ^ 8 := by rw [pow_add]
          _ = 577738301458 := by rw [fermat_3]; decide
      have fermat_5 : (6 : ZMod 1121685802999) ^ 32 = 963861514547 := by
        calc
          (6 : ZMod 1121685802999) ^ 32 = (6 : ZMod 1121685802999) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 16 * (6 : ZMod 1121685802999) ^ 16 := by rw [pow_add]
          _ = 963861514547 := by rw [fermat_4]; decide
      have fermat_6 : (6 : ZMod 1121685802999) ^ 65 = 401523275804 := by
        calc
          (6 : ZMod 1121685802999) ^ 65 = (6 : ZMod 1121685802999) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 32 * (6 : ZMod 1121685802999) ^ 32) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 401523275804 := by rw [fermat_5]; decide
      have fermat_7 : (6 : ZMod 1121685802999) ^ 130 = 911714385079 := by
        calc
          (6 : ZMod 1121685802999) ^ 130 = (6 : ZMod 1121685802999) ^ (65 + 65) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 65 * (6 : ZMod 1121685802999) ^ 65 := by rw [pow_add]
          _ = 911714385079 := by rw [fermat_6]; decide
      have fermat_8 : (6 : ZMod 1121685802999) ^ 261 = 711086961108 := by
        calc
          (6 : ZMod 1121685802999) ^ 261 = (6 : ZMod 1121685802999) ^ (130 + 130 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 130 * (6 : ZMod 1121685802999) ^ 130) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 711086961108 := by rw [fermat_7]; decide
      have fermat_9 : (6 : ZMod 1121685802999) ^ 522 = 870974730127 := by
        calc
          (6 : ZMod 1121685802999) ^ 522 = (6 : ZMod 1121685802999) ^ (261 + 261) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 261 * (6 : ZMod 1121685802999) ^ 261 := by rw [pow_add]
          _ = 870974730127 := by rw [fermat_8]; decide
      have fermat_10 : (6 : ZMod 1121685802999) ^ 1044 = 144333739487 := by
        calc
          (6 : ZMod 1121685802999) ^ 1044 = (6 : ZMod 1121685802999) ^ (522 + 522) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 522 * (6 : ZMod 1121685802999) ^ 522 := by rw [pow_add]
          _ = 144333739487 := by rw [fermat_9]; decide
      have fermat_11 : (6 : ZMod 1121685802999) ^ 2089 = 376640080732 := by
        calc
          (6 : ZMod 1121685802999) ^ 2089 = (6 : ZMod 1121685802999) ^ (1044 + 1044 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 1044 * (6 : ZMod 1121685802999) ^ 1044) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 376640080732 := by rw [fermat_10]; decide
      have fermat_12 : (6 : ZMod 1121685802999) ^ 4178 = 771650183764 := by
        calc
          (6 : ZMod 1121685802999) ^ 4178 = (6 : ZMod 1121685802999) ^ (2089 + 2089) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 2089 * (6 : ZMod 1121685802999) ^ 2089 := by rw [pow_add]
          _ = 771650183764 := by rw [fermat_11]; decide
      have fermat_13 : (6 : ZMod 1121685802999) ^ 8357 = 180644635871 := by
        calc
          (6 : ZMod 1121685802999) ^ 8357 = (6 : ZMod 1121685802999) ^ (4178 + 4178 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 4178 * (6 : ZMod 1121685802999) ^ 4178) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 180644635871 := by rw [fermat_12]; decide
      have fermat_14 : (6 : ZMod 1121685802999) ^ 16714 = 196578758217 := by
        calc
          (6 : ZMod 1121685802999) ^ 16714 = (6 : ZMod 1121685802999) ^ (8357 + 8357) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 8357 * (6 : ZMod 1121685802999) ^ 8357 := by rw [pow_add]
          _ = 196578758217 := by rw [fermat_13]; decide
      have fermat_15 : (6 : ZMod 1121685802999) ^ 33428 = 1035330526523 := by
        calc
          (6 : ZMod 1121685802999) ^ 33428 = (6 : ZMod 1121685802999) ^ (16714 + 16714) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 16714 * (6 : ZMod 1121685802999) ^ 16714 := by rw [pow_add]
          _ = 1035330526523 := by rw [fermat_14]; decide
      have fermat_16 : (6 : ZMod 1121685802999) ^ 66857 = 333991186293 := by
        calc
          (6 : ZMod 1121685802999) ^ 66857 = (6 : ZMod 1121685802999) ^ (33428 + 33428 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 33428 * (6 : ZMod 1121685802999) ^ 33428) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 333991186293 := by rw [fermat_15]; decide
      have fermat_17 : (6 : ZMod 1121685802999) ^ 133715 = 1115178273353 := by
        calc
          (6 : ZMod 1121685802999) ^ 133715 = (6 : ZMod 1121685802999) ^ (66857 + 66857 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 66857 * (6 : ZMod 1121685802999) ^ 66857) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 1115178273353 := by rw [fermat_16]; decide
      have fermat_18 : (6 : ZMod 1121685802999) ^ 267430 = 243616331152 := by
        calc
          (6 : ZMod 1121685802999) ^ 267430 = (6 : ZMod 1121685802999) ^ (133715 + 133715) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 133715 * (6 : ZMod 1121685802999) ^ 133715 := by rw [pow_add]
          _ = 243616331152 := by rw [fermat_17]; decide
      have fermat_19 : (6 : ZMod 1121685802999) ^ 534861 = 754110766325 := by
        calc
          (6 : ZMod 1121685802999) ^ 534861 = (6 : ZMod 1121685802999) ^ (267430 + 267430 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 267430 * (6 : ZMod 1121685802999) ^ 267430) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 754110766325 := by rw [fermat_18]; decide
      have fermat_20 : (6 : ZMod 1121685802999) ^ 1069722 = 395849996698 := by
        calc
          (6 : ZMod 1121685802999) ^ 1069722 = (6 : ZMod 1121685802999) ^ (534861 + 534861) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 534861 * (6 : ZMod 1121685802999) ^ 534861 := by rw [pow_add]
          _ = 395849996698 := by rw [fermat_19]; decide
      have fermat_21 : (6 : ZMod 1121685802999) ^ 2139445 = 188572784958 := by
        calc
          (6 : ZMod 1121685802999) ^ 2139445 = (6 : ZMod 1121685802999) ^ (1069722 + 1069722 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 1069722 * (6 : ZMod 1121685802999) ^ 1069722) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 188572784958 := by rw [fermat_20]; decide
      have fermat_22 : (6 : ZMod 1121685802999) ^ 4278891 = 1062774272238 := by
        calc
          (6 : ZMod 1121685802999) ^ 4278891 = (6 : ZMod 1121685802999) ^ (2139445 + 2139445 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 2139445 * (6 : ZMod 1121685802999) ^ 2139445) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 1062774272238 := by rw [fermat_21]; decide
      have fermat_23 : (6 : ZMod 1121685802999) ^ 8557783 = 482416678974 := by
        calc
          (6 : ZMod 1121685802999) ^ 8557783 = (6 : ZMod 1121685802999) ^ (4278891 + 4278891 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 4278891 * (6 : ZMod 1121685802999) ^ 4278891) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 482416678974 := by rw [fermat_22]; decide
      have fermat_24 : (6 : ZMod 1121685802999) ^ 17115567 = 903301874776 := by
        calc
          (6 : ZMod 1121685802999) ^ 17115567 = (6 : ZMod 1121685802999) ^ (8557783 + 8557783 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 8557783 * (6 : ZMod 1121685802999) ^ 8557783) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 903301874776 := by rw [fermat_23]; decide
      have fermat_25 : (6 : ZMod 1121685802999) ^ 34231134 = 683241456068 := by
        calc
          (6 : ZMod 1121685802999) ^ 34231134 = (6 : ZMod 1121685802999) ^ (17115567 + 17115567) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 17115567 * (6 : ZMod 1121685802999) ^ 17115567 := by rw [pow_add]
          _ = 683241456068 := by rw [fermat_24]; decide
      have fermat_26 : (6 : ZMod 1121685802999) ^ 68462268 = 2101811013 := by
        calc
          (6 : ZMod 1121685802999) ^ 68462268 = (6 : ZMod 1121685802999) ^ (34231134 + 34231134) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 34231134 * (6 : ZMod 1121685802999) ^ 34231134 := by rw [pow_add]
          _ = 2101811013 := by rw [fermat_25]; decide
      have fermat_27 : (6 : ZMod 1121685802999) ^ 136924536 = 305154126535 := by
        calc
          (6 : ZMod 1121685802999) ^ 136924536 = (6 : ZMod 1121685802999) ^ (68462268 + 68462268) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 68462268 * (6 : ZMod 1121685802999) ^ 68462268 := by rw [pow_add]
          _ = 305154126535 := by rw [fermat_26]; decide
      have fermat_28 : (6 : ZMod 1121685802999) ^ 273849072 = 873660731365 := by
        calc
          (6 : ZMod 1121685802999) ^ 273849072 = (6 : ZMod 1121685802999) ^ (136924536 + 136924536) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 136924536 * (6 : ZMod 1121685802999) ^ 136924536 := by rw [pow_add]
          _ = 873660731365 := by rw [fermat_27]; decide
      have fermat_29 : (6 : ZMod 1121685802999) ^ 547698145 = 798101415806 := by
        calc
          (6 : ZMod 1121685802999) ^ 547698145 = (6 : ZMod 1121685802999) ^ (273849072 + 273849072 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 273849072 * (6 : ZMod 1121685802999) ^ 273849072) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 798101415806 := by rw [fermat_28]; decide
      have fermat_30 : (6 : ZMod 1121685802999) ^ 1095396291 = 423543718477 := by
        calc
          (6 : ZMod 1121685802999) ^ 1095396291 = (6 : ZMod 1121685802999) ^ (547698145 + 547698145 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 547698145 * (6 : ZMod 1121685802999) ^ 547698145) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 423543718477 := by rw [fermat_29]; decide
      have fermat_31 : (6 : ZMod 1121685802999) ^ 2190792583 = 742523470710 := by
        calc
          (6 : ZMod 1121685802999) ^ 2190792583 = (6 : ZMod 1121685802999) ^ (1095396291 + 1095396291 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 1095396291 * (6 : ZMod 1121685802999) ^ 1095396291) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 742523470710 := by rw [fermat_30]; decide
      have fermat_32 : (6 : ZMod 1121685802999) ^ 4381585167 = 1116683994283 := by
        calc
          (6 : ZMod 1121685802999) ^ 4381585167 = (6 : ZMod 1121685802999) ^ (2190792583 + 2190792583 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 2190792583 * (6 : ZMod 1121685802999) ^ 2190792583) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 1116683994283 := by rw [fermat_31]; decide
      have fermat_33 : (6 : ZMod 1121685802999) ^ 8763170335 = 1117149873990 := by
        calc
          (6 : ZMod 1121685802999) ^ 8763170335 = (6 : ZMod 1121685802999) ^ (4381585167 + 4381585167 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 4381585167 * (6 : ZMod 1121685802999) ^ 4381585167) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 1117149873990 := by rw [fermat_32]; decide
      have fermat_34 : (6 : ZMod 1121685802999) ^ 17526340671 = 105752500182 := by
        calc
          (6 : ZMod 1121685802999) ^ 17526340671 = (6 : ZMod 1121685802999) ^ (8763170335 + 8763170335 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 8763170335 * (6 : ZMod 1121685802999) ^ 8763170335) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 105752500182 := by rw [fermat_33]; decide
      have fermat_35 : (6 : ZMod 1121685802999) ^ 35052681343 = 111106484933 := by
        calc
          (6 : ZMod 1121685802999) ^ 35052681343 = (6 : ZMod 1121685802999) ^ (17526340671 + 17526340671 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 17526340671 * (6 : ZMod 1121685802999) ^ 17526340671) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 111106484933 := by rw [fermat_34]; decide
      have fermat_36 : (6 : ZMod 1121685802999) ^ 70105362687 = 1094900065697 := by
        calc
          (6 : ZMod 1121685802999) ^ 70105362687 = (6 : ZMod 1121685802999) ^ (35052681343 + 35052681343 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 35052681343 * (6 : ZMod 1121685802999) ^ 35052681343) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 1094900065697 := by rw [fermat_35]; decide
      have fermat_37 : (6 : ZMod 1121685802999) ^ 140210725374 = 1097653835752 := by
        calc
          (6 : ZMod 1121685802999) ^ 140210725374 = (6 : ZMod 1121685802999) ^ (70105362687 + 70105362687) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 70105362687 * (6 : ZMod 1121685802999) ^ 70105362687 := by rw [pow_add]
          _ = 1097653835752 := by rw [fermat_36]; decide
      have fermat_38 : (6 : ZMod 1121685802999) ^ 280421450749 = 112449540022 := by
        calc
          (6 : ZMod 1121685802999) ^ 280421450749 = (6 : ZMod 1121685802999) ^ (140210725374 + 140210725374 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 140210725374 * (6 : ZMod 1121685802999) ^ 140210725374) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 112449540022 := by rw [fermat_37]; decide
      have fermat_39 : (6 : ZMod 1121685802999) ^ 560842901499 = 1121685802998 := by
        calc
          (6 : ZMod 1121685802999) ^ 560842901499 = (6 : ZMod 1121685802999) ^ (280421450749 + 280421450749 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 280421450749 * (6 : ZMod 1121685802999) ^ 280421450749) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 1121685802998 := by rw [fermat_38]; decide
      have fermat_40 : (6 : ZMod 1121685802999) ^ 1121685802998 = 1 := by
        calc
          (6 : ZMod 1121685802999) ^ 1121685802998 = (6 : ZMod 1121685802999) ^ (560842901499 + 560842901499) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 560842901499 * (6 : ZMod 1121685802999) ^ 560842901499 := by rw [pow_add]
          _ = 1 := by rw [fermat_39]; decide
      simpa using fermat_40
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7699, 1), (24282067, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7699, 1), (24282067, 1)] : List FactorBlock).map factorBlockValue).prod = 1121685802999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (6 : ZMod 1121685802999) ^ 1 = 6 := by norm_num
      have factor_0_1 : (6 : ZMod 1121685802999) ^ 2 = 36 := by
        calc
          (6 : ZMod 1121685802999) ^ 2 = (6 : ZMod 1121685802999) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 1 * (6 : ZMod 1121685802999) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_0_0]; decide
      have factor_0_2 : (6 : ZMod 1121685802999) ^ 4 = 1296 := by
        calc
          (6 : ZMod 1121685802999) ^ 4 = (6 : ZMod 1121685802999) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 2 * (6 : ZMod 1121685802999) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_0_1]; decide
      have factor_0_3 : (6 : ZMod 1121685802999) ^ 8 = 1679616 := by
        calc
          (6 : ZMod 1121685802999) ^ 8 = (6 : ZMod 1121685802999) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 4 * (6 : ZMod 1121685802999) ^ 4 := by rw [pow_add]
          _ = 1679616 := by rw [factor_0_2]; decide
      have factor_0_4 : (6 : ZMod 1121685802999) ^ 16 = 577738301458 := by
        calc
          (6 : ZMod 1121685802999) ^ 16 = (6 : ZMod 1121685802999) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 8 * (6 : ZMod 1121685802999) ^ 8 := by rw [pow_add]
          _ = 577738301458 := by rw [factor_0_3]; decide
      have factor_0_5 : (6 : ZMod 1121685802999) ^ 32 = 963861514547 := by
        calc
          (6 : ZMod 1121685802999) ^ 32 = (6 : ZMod 1121685802999) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 16 * (6 : ZMod 1121685802999) ^ 16 := by rw [pow_add]
          _ = 963861514547 := by rw [factor_0_4]; decide
      have factor_0_6 : (6 : ZMod 1121685802999) ^ 65 = 401523275804 := by
        calc
          (6 : ZMod 1121685802999) ^ 65 = (6 : ZMod 1121685802999) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 32 * (6 : ZMod 1121685802999) ^ 32) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 401523275804 := by rw [factor_0_5]; decide
      have factor_0_7 : (6 : ZMod 1121685802999) ^ 130 = 911714385079 := by
        calc
          (6 : ZMod 1121685802999) ^ 130 = (6 : ZMod 1121685802999) ^ (65 + 65) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 65 * (6 : ZMod 1121685802999) ^ 65 := by rw [pow_add]
          _ = 911714385079 := by rw [factor_0_6]; decide
      have factor_0_8 : (6 : ZMod 1121685802999) ^ 261 = 711086961108 := by
        calc
          (6 : ZMod 1121685802999) ^ 261 = (6 : ZMod 1121685802999) ^ (130 + 130 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 130 * (6 : ZMod 1121685802999) ^ 130) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 711086961108 := by rw [factor_0_7]; decide
      have factor_0_9 : (6 : ZMod 1121685802999) ^ 522 = 870974730127 := by
        calc
          (6 : ZMod 1121685802999) ^ 522 = (6 : ZMod 1121685802999) ^ (261 + 261) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 261 * (6 : ZMod 1121685802999) ^ 261 := by rw [pow_add]
          _ = 870974730127 := by rw [factor_0_8]; decide
      have factor_0_10 : (6 : ZMod 1121685802999) ^ 1044 = 144333739487 := by
        calc
          (6 : ZMod 1121685802999) ^ 1044 = (6 : ZMod 1121685802999) ^ (522 + 522) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 522 * (6 : ZMod 1121685802999) ^ 522 := by rw [pow_add]
          _ = 144333739487 := by rw [factor_0_9]; decide
      have factor_0_11 : (6 : ZMod 1121685802999) ^ 2089 = 376640080732 := by
        calc
          (6 : ZMod 1121685802999) ^ 2089 = (6 : ZMod 1121685802999) ^ (1044 + 1044 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 1044 * (6 : ZMod 1121685802999) ^ 1044) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 376640080732 := by rw [factor_0_10]; decide
      have factor_0_12 : (6 : ZMod 1121685802999) ^ 4178 = 771650183764 := by
        calc
          (6 : ZMod 1121685802999) ^ 4178 = (6 : ZMod 1121685802999) ^ (2089 + 2089) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 2089 * (6 : ZMod 1121685802999) ^ 2089 := by rw [pow_add]
          _ = 771650183764 := by rw [factor_0_11]; decide
      have factor_0_13 : (6 : ZMod 1121685802999) ^ 8357 = 180644635871 := by
        calc
          (6 : ZMod 1121685802999) ^ 8357 = (6 : ZMod 1121685802999) ^ (4178 + 4178 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 4178 * (6 : ZMod 1121685802999) ^ 4178) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 180644635871 := by rw [factor_0_12]; decide
      have factor_0_14 : (6 : ZMod 1121685802999) ^ 16714 = 196578758217 := by
        calc
          (6 : ZMod 1121685802999) ^ 16714 = (6 : ZMod 1121685802999) ^ (8357 + 8357) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 8357 * (6 : ZMod 1121685802999) ^ 8357 := by rw [pow_add]
          _ = 196578758217 := by rw [factor_0_13]; decide
      have factor_0_15 : (6 : ZMod 1121685802999) ^ 33428 = 1035330526523 := by
        calc
          (6 : ZMod 1121685802999) ^ 33428 = (6 : ZMod 1121685802999) ^ (16714 + 16714) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 16714 * (6 : ZMod 1121685802999) ^ 16714 := by rw [pow_add]
          _ = 1035330526523 := by rw [factor_0_14]; decide
      have factor_0_16 : (6 : ZMod 1121685802999) ^ 66857 = 333991186293 := by
        calc
          (6 : ZMod 1121685802999) ^ 66857 = (6 : ZMod 1121685802999) ^ (33428 + 33428 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 33428 * (6 : ZMod 1121685802999) ^ 33428) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 333991186293 := by rw [factor_0_15]; decide
      have factor_0_17 : (6 : ZMod 1121685802999) ^ 133715 = 1115178273353 := by
        calc
          (6 : ZMod 1121685802999) ^ 133715 = (6 : ZMod 1121685802999) ^ (66857 + 66857 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 66857 * (6 : ZMod 1121685802999) ^ 66857) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 1115178273353 := by rw [factor_0_16]; decide
      have factor_0_18 : (6 : ZMod 1121685802999) ^ 267430 = 243616331152 := by
        calc
          (6 : ZMod 1121685802999) ^ 267430 = (6 : ZMod 1121685802999) ^ (133715 + 133715) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 133715 * (6 : ZMod 1121685802999) ^ 133715 := by rw [pow_add]
          _ = 243616331152 := by rw [factor_0_17]; decide
      have factor_0_19 : (6 : ZMod 1121685802999) ^ 534861 = 754110766325 := by
        calc
          (6 : ZMod 1121685802999) ^ 534861 = (6 : ZMod 1121685802999) ^ (267430 + 267430 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 267430 * (6 : ZMod 1121685802999) ^ 267430) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 754110766325 := by rw [factor_0_18]; decide
      have factor_0_20 : (6 : ZMod 1121685802999) ^ 1069722 = 395849996698 := by
        calc
          (6 : ZMod 1121685802999) ^ 1069722 = (6 : ZMod 1121685802999) ^ (534861 + 534861) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 534861 * (6 : ZMod 1121685802999) ^ 534861 := by rw [pow_add]
          _ = 395849996698 := by rw [factor_0_19]; decide
      have factor_0_21 : (6 : ZMod 1121685802999) ^ 2139445 = 188572784958 := by
        calc
          (6 : ZMod 1121685802999) ^ 2139445 = (6 : ZMod 1121685802999) ^ (1069722 + 1069722 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 1069722 * (6 : ZMod 1121685802999) ^ 1069722) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 188572784958 := by rw [factor_0_20]; decide
      have factor_0_22 : (6 : ZMod 1121685802999) ^ 4278891 = 1062774272238 := by
        calc
          (6 : ZMod 1121685802999) ^ 4278891 = (6 : ZMod 1121685802999) ^ (2139445 + 2139445 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 2139445 * (6 : ZMod 1121685802999) ^ 2139445) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 1062774272238 := by rw [factor_0_21]; decide
      have factor_0_23 : (6 : ZMod 1121685802999) ^ 8557783 = 482416678974 := by
        calc
          (6 : ZMod 1121685802999) ^ 8557783 = (6 : ZMod 1121685802999) ^ (4278891 + 4278891 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 4278891 * (6 : ZMod 1121685802999) ^ 4278891) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 482416678974 := by rw [factor_0_22]; decide
      have factor_0_24 : (6 : ZMod 1121685802999) ^ 17115567 = 903301874776 := by
        calc
          (6 : ZMod 1121685802999) ^ 17115567 = (6 : ZMod 1121685802999) ^ (8557783 + 8557783 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 8557783 * (6 : ZMod 1121685802999) ^ 8557783) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 903301874776 := by rw [factor_0_23]; decide
      have factor_0_25 : (6 : ZMod 1121685802999) ^ 34231134 = 683241456068 := by
        calc
          (6 : ZMod 1121685802999) ^ 34231134 = (6 : ZMod 1121685802999) ^ (17115567 + 17115567) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 17115567 * (6 : ZMod 1121685802999) ^ 17115567 := by rw [pow_add]
          _ = 683241456068 := by rw [factor_0_24]; decide
      have factor_0_26 : (6 : ZMod 1121685802999) ^ 68462268 = 2101811013 := by
        calc
          (6 : ZMod 1121685802999) ^ 68462268 = (6 : ZMod 1121685802999) ^ (34231134 + 34231134) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 34231134 * (6 : ZMod 1121685802999) ^ 34231134 := by rw [pow_add]
          _ = 2101811013 := by rw [factor_0_25]; decide
      have factor_0_27 : (6 : ZMod 1121685802999) ^ 136924536 = 305154126535 := by
        calc
          (6 : ZMod 1121685802999) ^ 136924536 = (6 : ZMod 1121685802999) ^ (68462268 + 68462268) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 68462268 * (6 : ZMod 1121685802999) ^ 68462268 := by rw [pow_add]
          _ = 305154126535 := by rw [factor_0_26]; decide
      have factor_0_28 : (6 : ZMod 1121685802999) ^ 273849072 = 873660731365 := by
        calc
          (6 : ZMod 1121685802999) ^ 273849072 = (6 : ZMod 1121685802999) ^ (136924536 + 136924536) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 136924536 * (6 : ZMod 1121685802999) ^ 136924536 := by rw [pow_add]
          _ = 873660731365 := by rw [factor_0_27]; decide
      have factor_0_29 : (6 : ZMod 1121685802999) ^ 547698145 = 798101415806 := by
        calc
          (6 : ZMod 1121685802999) ^ 547698145 = (6 : ZMod 1121685802999) ^ (273849072 + 273849072 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 273849072 * (6 : ZMod 1121685802999) ^ 273849072) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 798101415806 := by rw [factor_0_28]; decide
      have factor_0_30 : (6 : ZMod 1121685802999) ^ 1095396291 = 423543718477 := by
        calc
          (6 : ZMod 1121685802999) ^ 1095396291 = (6 : ZMod 1121685802999) ^ (547698145 + 547698145 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 547698145 * (6 : ZMod 1121685802999) ^ 547698145) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 423543718477 := by rw [factor_0_29]; decide
      have factor_0_31 : (6 : ZMod 1121685802999) ^ 2190792583 = 742523470710 := by
        calc
          (6 : ZMod 1121685802999) ^ 2190792583 = (6 : ZMod 1121685802999) ^ (1095396291 + 1095396291 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 1095396291 * (6 : ZMod 1121685802999) ^ 1095396291) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 742523470710 := by rw [factor_0_30]; decide
      have factor_0_32 : (6 : ZMod 1121685802999) ^ 4381585167 = 1116683994283 := by
        calc
          (6 : ZMod 1121685802999) ^ 4381585167 = (6 : ZMod 1121685802999) ^ (2190792583 + 2190792583 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 2190792583 * (6 : ZMod 1121685802999) ^ 2190792583) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 1116683994283 := by rw [factor_0_31]; decide
      have factor_0_33 : (6 : ZMod 1121685802999) ^ 8763170335 = 1117149873990 := by
        calc
          (6 : ZMod 1121685802999) ^ 8763170335 = (6 : ZMod 1121685802999) ^ (4381585167 + 4381585167 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 4381585167 * (6 : ZMod 1121685802999) ^ 4381585167) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 1117149873990 := by rw [factor_0_32]; decide
      have factor_0_34 : (6 : ZMod 1121685802999) ^ 17526340671 = 105752500182 := by
        calc
          (6 : ZMod 1121685802999) ^ 17526340671 = (6 : ZMod 1121685802999) ^ (8763170335 + 8763170335 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 8763170335 * (6 : ZMod 1121685802999) ^ 8763170335) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 105752500182 := by rw [factor_0_33]; decide
      have factor_0_35 : (6 : ZMod 1121685802999) ^ 35052681343 = 111106484933 := by
        calc
          (6 : ZMod 1121685802999) ^ 35052681343 = (6 : ZMod 1121685802999) ^ (17526340671 + 17526340671 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 17526340671 * (6 : ZMod 1121685802999) ^ 17526340671) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 111106484933 := by rw [factor_0_34]; decide
      have factor_0_36 : (6 : ZMod 1121685802999) ^ 70105362687 = 1094900065697 := by
        calc
          (6 : ZMod 1121685802999) ^ 70105362687 = (6 : ZMod 1121685802999) ^ (35052681343 + 35052681343 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 35052681343 * (6 : ZMod 1121685802999) ^ 35052681343) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 1094900065697 := by rw [factor_0_35]; decide
      have factor_0_37 : (6 : ZMod 1121685802999) ^ 140210725374 = 1097653835752 := by
        calc
          (6 : ZMod 1121685802999) ^ 140210725374 = (6 : ZMod 1121685802999) ^ (70105362687 + 70105362687) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 70105362687 * (6 : ZMod 1121685802999) ^ 70105362687 := by rw [pow_add]
          _ = 1097653835752 := by rw [factor_0_36]; decide
      have factor_0_38 : (6 : ZMod 1121685802999) ^ 280421450749 = 112449540022 := by
        calc
          (6 : ZMod 1121685802999) ^ 280421450749 = (6 : ZMod 1121685802999) ^ (140210725374 + 140210725374 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 140210725374 * (6 : ZMod 1121685802999) ^ 140210725374) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 112449540022 := by rw [factor_0_37]; decide
      have factor_0_39 : (6 : ZMod 1121685802999) ^ 560842901499 = 1121685802998 := by
        calc
          (6 : ZMod 1121685802999) ^ 560842901499 = (6 : ZMod 1121685802999) ^ (280421450749 + 280421450749 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 280421450749 * (6 : ZMod 1121685802999) ^ 280421450749) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 1121685802998 := by rw [factor_0_38]; decide
      change (6 : ZMod 1121685802999) ^ 560842901499 ≠ 1
      rw [factor_0_39]
      decide
    ·
      have factor_1_0 : (6 : ZMod 1121685802999) ^ 1 = 6 := by norm_num
      have factor_1_1 : (6 : ZMod 1121685802999) ^ 2 = 36 := by
        calc
          (6 : ZMod 1121685802999) ^ 2 = (6 : ZMod 1121685802999) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 1 * (6 : ZMod 1121685802999) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_1_0]; decide
      have factor_1_2 : (6 : ZMod 1121685802999) ^ 5 = 7776 := by
        calc
          (6 : ZMod 1121685802999) ^ 5 = (6 : ZMod 1121685802999) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 2 * (6 : ZMod 1121685802999) ^ 2) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 7776 := by rw [factor_1_1]; decide
      have factor_1_3 : (6 : ZMod 1121685802999) ^ 10 = 60466176 := by
        calc
          (6 : ZMod 1121685802999) ^ 10 = (6 : ZMod 1121685802999) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 5 * (6 : ZMod 1121685802999) ^ 5 := by rw [pow_add]
          _ = 60466176 := by rw [factor_1_2]; decide
      have factor_1_4 : (6 : ZMod 1121685802999) ^ 21 = 141391126413 := by
        calc
          (6 : ZMod 1121685802999) ^ 21 = (6 : ZMod 1121685802999) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 10 * (6 : ZMod 1121685802999) ^ 10) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 141391126413 := by rw [factor_1_3]; decide
      have factor_1_5 : (6 : ZMod 1121685802999) ^ 43 = 968026600140 := by
        calc
          (6 : ZMod 1121685802999) ^ 43 = (6 : ZMod 1121685802999) ^ (21 + 21 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 21 * (6 : ZMod 1121685802999) ^ 21) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 968026600140 := by rw [factor_1_4]; decide
      have factor_1_6 : (6 : ZMod 1121685802999) ^ 87 = 51689188506 := by
        calc
          (6 : ZMod 1121685802999) ^ 87 = (6 : ZMod 1121685802999) ^ (43 + 43 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 43 * (6 : ZMod 1121685802999) ^ 43) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 51689188506 := by rw [factor_1_5]; decide
      have factor_1_7 : (6 : ZMod 1121685802999) ^ 174 = 570921427706 := by
        calc
          (6 : ZMod 1121685802999) ^ 174 = (6 : ZMod 1121685802999) ^ (87 + 87) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 87 * (6 : ZMod 1121685802999) ^ 87 := by rw [pow_add]
          _ = 570921427706 := by rw [factor_1_6]; decide
      have factor_1_8 : (6 : ZMod 1121685802999) ^ 348 = 1070133384560 := by
        calc
          (6 : ZMod 1121685802999) ^ 348 = (6 : ZMod 1121685802999) ^ (174 + 174) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 174 * (6 : ZMod 1121685802999) ^ 174 := by rw [pow_add]
          _ = 1070133384560 := by rw [factor_1_7]; decide
      have factor_1_9 : (6 : ZMod 1121685802999) ^ 696 = 993263477873 := by
        calc
          (6 : ZMod 1121685802999) ^ 696 = (6 : ZMod 1121685802999) ^ (348 + 348) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 348 * (6 : ZMod 1121685802999) ^ 348 := by rw [pow_add]
          _ = 993263477873 := by rw [factor_1_8]; decide
      have factor_1_10 : (6 : ZMod 1121685802999) ^ 1392 = 160309676133 := by
        calc
          (6 : ZMod 1121685802999) ^ 1392 = (6 : ZMod 1121685802999) ^ (696 + 696) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 696 * (6 : ZMod 1121685802999) ^ 696 := by rw [pow_add]
          _ = 160309676133 := by rw [factor_1_9]; decide
      have factor_1_11 : (6 : ZMod 1121685802999) ^ 2785 = 1229500145 := by
        calc
          (6 : ZMod 1121685802999) ^ 2785 = (6 : ZMod 1121685802999) ^ (1392 + 1392 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 1392 * (6 : ZMod 1121685802999) ^ 1392) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 1229500145 := by rw [factor_1_10]; decide
      have factor_1_12 : (6 : ZMod 1121685802999) ^ 5571 = 448388820214 := by
        calc
          (6 : ZMod 1121685802999) ^ 5571 = (6 : ZMod 1121685802999) ^ (2785 + 2785 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 2785 * (6 : ZMod 1121685802999) ^ 2785) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 448388820214 := by rw [factor_1_11]; decide
      have factor_1_13 : (6 : ZMod 1121685802999) ^ 11142 = 552653129155 := by
        calc
          (6 : ZMod 1121685802999) ^ 11142 = (6 : ZMod 1121685802999) ^ (5571 + 5571) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 5571 * (6 : ZMod 1121685802999) ^ 5571 := by rw [pow_add]
          _ = 552653129155 := by rw [factor_1_12]; decide
      have factor_1_14 : (6 : ZMod 1121685802999) ^ 22285 = 811045087831 := by
        calc
          (6 : ZMod 1121685802999) ^ 22285 = (6 : ZMod 1121685802999) ^ (11142 + 11142 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 11142 * (6 : ZMod 1121685802999) ^ 11142) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 811045087831 := by rw [factor_1_13]; decide
      have factor_1_15 : (6 : ZMod 1121685802999) ^ 44571 = 752707309171 := by
        calc
          (6 : ZMod 1121685802999) ^ 44571 = (6 : ZMod 1121685802999) ^ (22285 + 22285 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 22285 * (6 : ZMod 1121685802999) ^ 22285) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 752707309171 := by rw [factor_1_14]; decide
      have factor_1_16 : (6 : ZMod 1121685802999) ^ 89143 = 445930691978 := by
        calc
          (6 : ZMod 1121685802999) ^ 89143 = (6 : ZMod 1121685802999) ^ (44571 + 44571 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 44571 * (6 : ZMod 1121685802999) ^ 44571) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 445930691978 := by rw [factor_1_15]; decide
      have factor_1_17 : (6 : ZMod 1121685802999) ^ 178287 = 725816406812 := by
        calc
          (6 : ZMod 1121685802999) ^ 178287 = (6 : ZMod 1121685802999) ^ (89143 + 89143 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 89143 * (6 : ZMod 1121685802999) ^ 89143) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 725816406812 := by rw [factor_1_16]; decide
      have factor_1_18 : (6 : ZMod 1121685802999) ^ 356574 = 744317308997 := by
        calc
          (6 : ZMod 1121685802999) ^ 356574 = (6 : ZMod 1121685802999) ^ (178287 + 178287) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 178287 * (6 : ZMod 1121685802999) ^ 178287 := by rw [pow_add]
          _ = 744317308997 := by rw [factor_1_17]; decide
      have factor_1_19 : (6 : ZMod 1121685802999) ^ 713148 = 596335583733 := by
        calc
          (6 : ZMod 1121685802999) ^ 713148 = (6 : ZMod 1121685802999) ^ (356574 + 356574) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 356574 * (6 : ZMod 1121685802999) ^ 356574 := by rw [pow_add]
          _ = 596335583733 := by rw [factor_1_18]; decide
      have factor_1_20 : (6 : ZMod 1121685802999) ^ 1426297 = 469950384307 := by
        calc
          (6 : ZMod 1121685802999) ^ 1426297 = (6 : ZMod 1121685802999) ^ (713148 + 713148 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 713148 * (6 : ZMod 1121685802999) ^ 713148) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 469950384307 := by rw [factor_1_19]; decide
      have factor_1_21 : (6 : ZMod 1121685802999) ^ 2852594 = 285636586191 := by
        calc
          (6 : ZMod 1121685802999) ^ 2852594 = (6 : ZMod 1121685802999) ^ (1426297 + 1426297) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 1426297 * (6 : ZMod 1121685802999) ^ 1426297 := by rw [pow_add]
          _ = 285636586191 := by rw [factor_1_20]; decide
      have factor_1_22 : (6 : ZMod 1121685802999) ^ 5705189 = 1113079095986 := by
        calc
          (6 : ZMod 1121685802999) ^ 5705189 = (6 : ZMod 1121685802999) ^ (2852594 + 2852594 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 2852594 * (6 : ZMod 1121685802999) ^ 2852594) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 1113079095986 := by rw [factor_1_21]; decide
      have factor_1_23 : (6 : ZMod 1121685802999) ^ 11410378 = 908283962522 := by
        calc
          (6 : ZMod 1121685802999) ^ 11410378 = (6 : ZMod 1121685802999) ^ (5705189 + 5705189) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 5705189 * (6 : ZMod 1121685802999) ^ 5705189 := by rw [pow_add]
          _ = 908283962522 := by rw [factor_1_22]; decide
      have factor_1_24 : (6 : ZMod 1121685802999) ^ 22820756 = 783227229086 := by
        calc
          (6 : ZMod 1121685802999) ^ 22820756 = (6 : ZMod 1121685802999) ^ (11410378 + 11410378) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 11410378 * (6 : ZMod 1121685802999) ^ 11410378 := by rw [pow_add]
          _ = 783227229086 := by rw [factor_1_23]; decide
      have factor_1_25 : (6 : ZMod 1121685802999) ^ 45641512 = 1028923390490 := by
        calc
          (6 : ZMod 1121685802999) ^ 45641512 = (6 : ZMod 1121685802999) ^ (22820756 + 22820756) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 22820756 * (6 : ZMod 1121685802999) ^ 22820756 := by rw [pow_add]
          _ = 1028923390490 := by rw [factor_1_24]; decide
      have factor_1_26 : (6 : ZMod 1121685802999) ^ 91283024 = 328828241615 := by
        calc
          (6 : ZMod 1121685802999) ^ 91283024 = (6 : ZMod 1121685802999) ^ (45641512 + 45641512) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 45641512 * (6 : ZMod 1121685802999) ^ 45641512 := by rw [pow_add]
          _ = 328828241615 := by rw [factor_1_25]; decide
      have factor_1_27 : (6 : ZMod 1121685802999) ^ 182566048 = 913398873394 := by
        calc
          (6 : ZMod 1121685802999) ^ 182566048 = (6 : ZMod 1121685802999) ^ (91283024 + 91283024) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 91283024 * (6 : ZMod 1121685802999) ^ 91283024 := by rw [pow_add]
          _ = 913398873394 := by rw [factor_1_26]; decide
      have factor_1_28 : (6 : ZMod 1121685802999) ^ 365132097 = 83590733490 := by
        calc
          (6 : ZMod 1121685802999) ^ 365132097 = (6 : ZMod 1121685802999) ^ (182566048 + 182566048 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 182566048 * (6 : ZMod 1121685802999) ^ 182566048) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 83590733490 := by rw [factor_1_27]; decide
      have factor_1_29 : (6 : ZMod 1121685802999) ^ 730264194 = 473582288325 := by
        calc
          (6 : ZMod 1121685802999) ^ 730264194 = (6 : ZMod 1121685802999) ^ (365132097 + 365132097) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 365132097 * (6 : ZMod 1121685802999) ^ 365132097 := by rw [pow_add]
          _ = 473582288325 := by rw [factor_1_28]; decide
      have factor_1_30 : (6 : ZMod 1121685802999) ^ 1460528389 = 242808164715 := by
        calc
          (6 : ZMod 1121685802999) ^ 1460528389 = (6 : ZMod 1121685802999) ^ (730264194 + 730264194 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 730264194 * (6 : ZMod 1121685802999) ^ 730264194) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 242808164715 := by rw [factor_1_29]; decide
      have factor_1_31 : (6 : ZMod 1121685802999) ^ 2921056778 = 72063580375 := by
        calc
          (6 : ZMod 1121685802999) ^ 2921056778 = (6 : ZMod 1121685802999) ^ (1460528389 + 1460528389) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 1460528389 * (6 : ZMod 1121685802999) ^ 1460528389 := by rw [pow_add]
          _ = 72063580375 := by rw [factor_1_30]; decide
      have factor_1_32 : (6 : ZMod 1121685802999) ^ 5842113557 = 77661165738 := by
        calc
          (6 : ZMod 1121685802999) ^ 5842113557 = (6 : ZMod 1121685802999) ^ (2921056778 + 2921056778 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 2921056778 * (6 : ZMod 1121685802999) ^ 2921056778) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 77661165738 := by rw [factor_1_31]; decide
      have factor_1_33 : (6 : ZMod 1121685802999) ^ 11684227114 = 408327550941 := by
        calc
          (6 : ZMod 1121685802999) ^ 11684227114 = (6 : ZMod 1121685802999) ^ (5842113557 + 5842113557) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 5842113557 * (6 : ZMod 1121685802999) ^ 5842113557 := by rw [pow_add]
          _ = 408327550941 := by rw [factor_1_32]; decide
      have factor_1_34 : (6 : ZMod 1121685802999) ^ 23368454229 = 392387951625 := by
        calc
          (6 : ZMod 1121685802999) ^ 23368454229 = (6 : ZMod 1121685802999) ^ (11684227114 + 11684227114 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 11684227114 * (6 : ZMod 1121685802999) ^ 11684227114) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 392387951625 := by rw [factor_1_33]; decide
      have factor_1_35 : (6 : ZMod 1121685802999) ^ 46736908458 = 137929404301 := by
        calc
          (6 : ZMod 1121685802999) ^ 46736908458 = (6 : ZMod 1121685802999) ^ (23368454229 + 23368454229) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 23368454229 * (6 : ZMod 1121685802999) ^ 23368454229 := by rw [pow_add]
          _ = 137929404301 := by rw [factor_1_34]; decide
      have factor_1_36 : (6 : ZMod 1121685802999) ^ 93473816916 = 449364864829 := by
        calc
          (6 : ZMod 1121685802999) ^ 93473816916 = (6 : ZMod 1121685802999) ^ (46736908458 + 46736908458) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 46736908458 * (6 : ZMod 1121685802999) ^ 46736908458 := by rw [pow_add]
          _ = 449364864829 := by rw [factor_1_35]; decide
      have factor_1_37 : (6 : ZMod 1121685802999) ^ 186947633833 = 157731075463 := by
        calc
          (6 : ZMod 1121685802999) ^ 186947633833 = (6 : ZMod 1121685802999) ^ (93473816916 + 93473816916 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 93473816916 * (6 : ZMod 1121685802999) ^ 93473816916) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 157731075463 := by rw [factor_1_36]; decide
      have factor_1_38 : (6 : ZMod 1121685802999) ^ 373895267666 = 157731075462 := by
        calc
          (6 : ZMod 1121685802999) ^ 373895267666 = (6 : ZMod 1121685802999) ^ (186947633833 + 186947633833) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 186947633833 * (6 : ZMod 1121685802999) ^ 186947633833 := by rw [pow_add]
          _ = 157731075462 := by rw [factor_1_37]; decide
      change (6 : ZMod 1121685802999) ^ 373895267666 ≠ 1
      rw [factor_1_38]
      decide
    ·
      have factor_2_0 : (6 : ZMod 1121685802999) ^ 1 = 6 := by norm_num
      have factor_2_1 : (6 : ZMod 1121685802999) ^ 2 = 36 := by
        calc
          (6 : ZMod 1121685802999) ^ 2 = (6 : ZMod 1121685802999) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 1 * (6 : ZMod 1121685802999) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_2_0]; decide
      have factor_2_2 : (6 : ZMod 1121685802999) ^ 4 = 1296 := by
        calc
          (6 : ZMod 1121685802999) ^ 4 = (6 : ZMod 1121685802999) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 2 * (6 : ZMod 1121685802999) ^ 2 := by rw [pow_add]
          _ = 1296 := by rw [factor_2_1]; decide
      have factor_2_3 : (6 : ZMod 1121685802999) ^ 8 = 1679616 := by
        calc
          (6 : ZMod 1121685802999) ^ 8 = (6 : ZMod 1121685802999) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 4 * (6 : ZMod 1121685802999) ^ 4 := by rw [pow_add]
          _ = 1679616 := by rw [factor_2_2]; decide
      have factor_2_4 : (6 : ZMod 1121685802999) ^ 17 = 101372399751 := by
        calc
          (6 : ZMod 1121685802999) ^ 17 = (6 : ZMod 1121685802999) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 8 * (6 : ZMod 1121685802999) ^ 8) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 101372399751 := by rw [factor_2_3]; decide
      have factor_2_5 : (6 : ZMod 1121685802999) ^ 34 = 1048440433722 := by
        calc
          (6 : ZMod 1121685802999) ^ 34 = (6 : ZMod 1121685802999) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 17 * (6 : ZMod 1121685802999) ^ 17 := by rw [pow_add]
          _ = 1048440433722 := by rw [factor_2_4]; decide
      have factor_2_6 : (6 : ZMod 1121685802999) ^ 69 = 1033638653447 := by
        calc
          (6 : ZMod 1121685802999) ^ 69 = (6 : ZMod 1121685802999) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 34 * (6 : ZMod 1121685802999) ^ 34) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 1033638653447 := by rw [factor_2_5]; decide
      have factor_2_7 : (6 : ZMod 1121685802999) ^ 138 = 123611402868 := by
        calc
          (6 : ZMod 1121685802999) ^ 138 = (6 : ZMod 1121685802999) ^ (69 + 69) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 69 * (6 : ZMod 1121685802999) ^ 69 := by rw [pow_add]
          _ = 123611402868 := by rw [factor_2_6]; decide
      have factor_2_8 : (6 : ZMod 1121685802999) ^ 277 = 558208252156 := by
        calc
          (6 : ZMod 1121685802999) ^ 277 = (6 : ZMod 1121685802999) ^ (138 + 138 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 138 * (6 : ZMod 1121685802999) ^ 138) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 558208252156 := by rw [factor_2_7]; decide
      have factor_2_9 : (6 : ZMod 1121685802999) ^ 555 = 130200131515 := by
        calc
          (6 : ZMod 1121685802999) ^ 555 = (6 : ZMod 1121685802999) ^ (277 + 277 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 277 * (6 : ZMod 1121685802999) ^ 277) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 130200131515 := by rw [factor_2_8]; decide
      have factor_2_10 : (6 : ZMod 1121685802999) ^ 1111 = 762522741692 := by
        calc
          (6 : ZMod 1121685802999) ^ 1111 = (6 : ZMod 1121685802999) ^ (555 + 555 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 555 * (6 : ZMod 1121685802999) ^ 555) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 762522741692 := by rw [factor_2_9]; decide
      have factor_2_11 : (6 : ZMod 1121685802999) ^ 2223 = 8740439999 := by
        calc
          (6 : ZMod 1121685802999) ^ 2223 = (6 : ZMod 1121685802999) ^ (1111 + 1111 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 1111 * (6 : ZMod 1121685802999) ^ 1111) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 8740439999 := by rw [factor_2_10]; decide
      have factor_2_12 : (6 : ZMod 1121685802999) ^ 4446 = 395415926568 := by
        calc
          (6 : ZMod 1121685802999) ^ 4446 = (6 : ZMod 1121685802999) ^ (2223 + 2223) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 2223 * (6 : ZMod 1121685802999) ^ 2223 := by rw [pow_add]
          _ = 395415926568 := by rw [factor_2_11]; decide
      have factor_2_13 : (6 : ZMod 1121685802999) ^ 8892 = 691766745714 := by
        calc
          (6 : ZMod 1121685802999) ^ 8892 = (6 : ZMod 1121685802999) ^ (4446 + 4446) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 4446 * (6 : ZMod 1121685802999) ^ 4446 := by rw [pow_add]
          _ = 691766745714 := by rw [factor_2_12]; decide
      have factor_2_14 : (6 : ZMod 1121685802999) ^ 17784 = 542967632910 := by
        calc
          (6 : ZMod 1121685802999) ^ 17784 = (6 : ZMod 1121685802999) ^ (8892 + 8892) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 8892 * (6 : ZMod 1121685802999) ^ 8892 := by rw [pow_add]
          _ = 542967632910 := by rw [factor_2_13]; decide
      have factor_2_15 : (6 : ZMod 1121685802999) ^ 35569 = 712462554239 := by
        calc
          (6 : ZMod 1121685802999) ^ 35569 = (6 : ZMod 1121685802999) ^ (17784 + 17784 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 17784 * (6 : ZMod 1121685802999) ^ 17784) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 712462554239 := by rw [factor_2_14]; decide
      have factor_2_16 : (6 : ZMod 1121685802999) ^ 71138 = 916265416978 := by
        calc
          (6 : ZMod 1121685802999) ^ 71138 = (6 : ZMod 1121685802999) ^ (35569 + 35569) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 35569 * (6 : ZMod 1121685802999) ^ 35569 := by rw [pow_add]
          _ = 916265416978 := by rw [factor_2_15]; decide
      have factor_2_17 : (6 : ZMod 1121685802999) ^ 142277 = 318521673605 := by
        calc
          (6 : ZMod 1121685802999) ^ 142277 = (6 : ZMod 1121685802999) ^ (71138 + 71138 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 71138 * (6 : ZMod 1121685802999) ^ 71138) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 318521673605 := by rw [factor_2_16]; decide
      have factor_2_18 : (6 : ZMod 1121685802999) ^ 284555 = 61722368396 := by
        calc
          (6 : ZMod 1121685802999) ^ 284555 = (6 : ZMod 1121685802999) ^ (142277 + 142277 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 142277 * (6 : ZMod 1121685802999) ^ 142277) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 61722368396 := by rw [factor_2_17]; decide
      have factor_2_19 : (6 : ZMod 1121685802999) ^ 569110 = 222643315569 := by
        calc
          (6 : ZMod 1121685802999) ^ 569110 = (6 : ZMod 1121685802999) ^ (284555 + 284555) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 284555 * (6 : ZMod 1121685802999) ^ 284555 := by rw [pow_add]
          _ = 222643315569 := by rw [factor_2_18]; decide
      have factor_2_20 : (6 : ZMod 1121685802999) ^ 1138221 = 61144725349 := by
        calc
          (6 : ZMod 1121685802999) ^ 1138221 = (6 : ZMod 1121685802999) ^ (569110 + 569110 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 569110 * (6 : ZMod 1121685802999) ^ 569110) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 61144725349 := by rw [factor_2_19]; decide
      have factor_2_21 : (6 : ZMod 1121685802999) ^ 2276443 = 256840989529 := by
        calc
          (6 : ZMod 1121685802999) ^ 2276443 = (6 : ZMod 1121685802999) ^ (1138221 + 1138221 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 1138221 * (6 : ZMod 1121685802999) ^ 1138221) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 256840989529 := by rw [factor_2_20]; decide
      have factor_2_22 : (6 : ZMod 1121685802999) ^ 4552887 = 387195500460 := by
        calc
          (6 : ZMod 1121685802999) ^ 4552887 = (6 : ZMod 1121685802999) ^ (2276443 + 2276443 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 2276443 * (6 : ZMod 1121685802999) ^ 2276443) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 387195500460 := by rw [factor_2_21]; decide
      have factor_2_23 : (6 : ZMod 1121685802999) ^ 9105775 = 188161089027 := by
        calc
          (6 : ZMod 1121685802999) ^ 9105775 = (6 : ZMod 1121685802999) ^ (4552887 + 4552887 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 4552887 * (6 : ZMod 1121685802999) ^ 4552887) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 188161089027 := by rw [factor_2_22]; decide
      have factor_2_24 : (6 : ZMod 1121685802999) ^ 18211550 = 441793036498 := by
        calc
          (6 : ZMod 1121685802999) ^ 18211550 = (6 : ZMod 1121685802999) ^ (9105775 + 9105775) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 9105775 * (6 : ZMod 1121685802999) ^ 9105775 := by rw [pow_add]
          _ = 441793036498 := by rw [factor_2_23]; decide
      have factor_2_25 : (6 : ZMod 1121685802999) ^ 36423100 = 308749362823 := by
        calc
          (6 : ZMod 1121685802999) ^ 36423100 = (6 : ZMod 1121685802999) ^ (18211550 + 18211550) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 18211550 * (6 : ZMod 1121685802999) ^ 18211550 := by rw [pow_add]
          _ = 308749362823 := by rw [factor_2_24]; decide
      have factor_2_26 : (6 : ZMod 1121685802999) ^ 72846201 = 866041699000 := by
        calc
          (6 : ZMod 1121685802999) ^ 72846201 = (6 : ZMod 1121685802999) ^ (36423100 + 36423100 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 36423100 * (6 : ZMod 1121685802999) ^ 36423100) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 866041699000 := by rw [factor_2_25]; decide
      have factor_2_27 : (6 : ZMod 1121685802999) ^ 145692402 = 955609194602 := by
        calc
          (6 : ZMod 1121685802999) ^ 145692402 = (6 : ZMod 1121685802999) ^ (72846201 + 72846201) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 72846201 * (6 : ZMod 1121685802999) ^ 72846201 := by rw [pow_add]
          _ = 955609194602 := by rw [factor_2_26]; decide
      change (6 : ZMod 1121685802999) ^ 145692402 ≠ 1
      rw [factor_2_27]
      decide
    ·
      have factor_3_0 : (6 : ZMod 1121685802999) ^ 1 = 6 := by norm_num
      have factor_3_1 : (6 : ZMod 1121685802999) ^ 2 = 36 := by
        calc
          (6 : ZMod 1121685802999) ^ 2 = (6 : ZMod 1121685802999) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 1 * (6 : ZMod 1121685802999) ^ 1 := by rw [pow_add]
          _ = 36 := by rw [factor_3_0]; decide
      have factor_3_2 : (6 : ZMod 1121685802999) ^ 5 = 7776 := by
        calc
          (6 : ZMod 1121685802999) ^ 5 = (6 : ZMod 1121685802999) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 2 * (6 : ZMod 1121685802999) ^ 2) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 7776 := by rw [factor_3_1]; decide
      have factor_3_3 : (6 : ZMod 1121685802999) ^ 11 = 362797056 := by
        calc
          (6 : ZMod 1121685802999) ^ 11 = (6 : ZMod 1121685802999) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 5 * (6 : ZMod 1121685802999) ^ 5) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 362797056 := by rw [factor_3_2]; decide
      have factor_3_4 : (6 : ZMod 1121685802999) ^ 22 = 848346758478 := by
        calc
          (6 : ZMod 1121685802999) ^ 22 = (6 : ZMod 1121685802999) ^ (11 + 11) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 11 * (6 : ZMod 1121685802999) ^ 11 := by rw [pow_add]
          _ = 848346758478 := by rw [factor_3_3]; decide
      have factor_3_5 : (6 : ZMod 1121685802999) ^ 45 = 76697712071 := by
        calc
          (6 : ZMod 1121685802999) ^ 45 = (6 : ZMod 1121685802999) ^ (22 + 22 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 22 * (6 : ZMod 1121685802999) ^ 22) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 76697712071 := by rw [factor_3_4]; decide
      have factor_3_6 : (6 : ZMod 1121685802999) ^ 90 = 1069692490305 := by
        calc
          (6 : ZMod 1121685802999) ^ 90 = (6 : ZMod 1121685802999) ^ (45 + 45) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 45 * (6 : ZMod 1121685802999) ^ 45 := by rw [pow_add]
          _ = 1069692490305 := by rw [factor_3_5]; decide
      have factor_3_7 : (6 : ZMod 1121685802999) ^ 180 = 237367233883 := by
        calc
          (6 : ZMod 1121685802999) ^ 180 = (6 : ZMod 1121685802999) ^ (90 + 90) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 90 * (6 : ZMod 1121685802999) ^ 90 := by rw [pow_add]
          _ = 237367233883 := by rw [factor_3_6]; decide
      have factor_3_8 : (6 : ZMod 1121685802999) ^ 360 = 530315292086 := by
        calc
          (6 : ZMod 1121685802999) ^ 360 = (6 : ZMod 1121685802999) ^ (180 + 180) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 180 * (6 : ZMod 1121685802999) ^ 180 := by rw [pow_add]
          _ = 530315292086 := by rw [factor_3_7]; decide
      have factor_3_9 : (6 : ZMod 1121685802999) ^ 721 = 536273434645 := by
        calc
          (6 : ZMod 1121685802999) ^ 721 = (6 : ZMod 1121685802999) ^ (360 + 360 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 360 * (6 : ZMod 1121685802999) ^ 360) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 536273434645 := by rw [factor_3_8]; decide
      have factor_3_10 : (6 : ZMod 1121685802999) ^ 1443 = 712814176153 := by
        calc
          (6 : ZMod 1121685802999) ^ 1443 = (6 : ZMod 1121685802999) ^ (721 + 721 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 721 * (6 : ZMod 1121685802999) ^ 721) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 712814176153 := by rw [factor_3_9]; decide
      have factor_3_11 : (6 : ZMod 1121685802999) ^ 2887 = 682096756446 := by
        calc
          (6 : ZMod 1121685802999) ^ 2887 = (6 : ZMod 1121685802999) ^ (1443 + 1443 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 1443 * (6 : ZMod 1121685802999) ^ 1443) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 682096756446 := by rw [factor_3_10]; decide
      have factor_3_12 : (6 : ZMod 1121685802999) ^ 5774 = 481352260215 := by
        calc
          (6 : ZMod 1121685802999) ^ 5774 = (6 : ZMod 1121685802999) ^ (2887 + 2887) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 2887 * (6 : ZMod 1121685802999) ^ 2887 := by rw [pow_add]
          _ = 481352260215 := by rw [factor_3_11]; decide
      have factor_3_13 : (6 : ZMod 1121685802999) ^ 11548 = 830629328425 := by
        calc
          (6 : ZMod 1121685802999) ^ 11548 = (6 : ZMod 1121685802999) ^ (5774 + 5774) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 5774 * (6 : ZMod 1121685802999) ^ 5774 := by rw [pow_add]
          _ = 830629328425 := by rw [factor_3_12]; decide
      have factor_3_14 : (6 : ZMod 1121685802999) ^ 23097 = 13117314664 := by
        calc
          (6 : ZMod 1121685802999) ^ 23097 = (6 : ZMod 1121685802999) ^ (11548 + 11548 + 1) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = ((6 : ZMod 1121685802999) ^ 11548 * (6 : ZMod 1121685802999) ^ 11548) * (6 : ZMod 1121685802999) := by rw [pow_succ, pow_add]
          _ = 13117314664 := by rw [factor_3_13]; decide
      have factor_3_15 : (6 : ZMod 1121685802999) ^ 46194 = 209695940526 := by
        calc
          (6 : ZMod 1121685802999) ^ 46194 = (6 : ZMod 1121685802999) ^ (23097 + 23097) :=
            congrArg (fun n : ℕ => (6 : ZMod 1121685802999) ^ n) (by norm_num)
          _ = (6 : ZMod 1121685802999) ^ 23097 * (6 : ZMod 1121685802999) ^ 23097 := by rw [pow_add]
          _ = 209695940526 := by rw [factor_3_14]; decide
      change (6 : ZMod 1121685802999) ^ 46194 ≠ 1
      rw [factor_3_15]
      decide

#print axioms prime_lucas_1121685802999

end TotientTailPeriodKiller
end Erdos249257
