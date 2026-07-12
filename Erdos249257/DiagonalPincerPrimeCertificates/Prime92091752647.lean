import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime103010909

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_92091752647 : Nat.Prime 92091752647 := by
  apply lucas_primality 92091752647 (3 : ZMod 92091752647)
  ·
      have fermat_0 : (3 : ZMod 92091752647) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 92091752647) ^ 2 = 9 := by
        calc
          (3 : ZMod 92091752647) ^ 2 = (3 : ZMod 92091752647) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 1 * (3 : ZMod 92091752647) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 92091752647) ^ 5 = 243 := by
        calc
          (3 : ZMod 92091752647) ^ 5 = (3 : ZMod 92091752647) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 2 * (3 : ZMod 92091752647) ^ 2) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 92091752647) ^ 10 = 59049 := by
        calc
          (3 : ZMod 92091752647) ^ 10 = (3 : ZMod 92091752647) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 5 * (3 : ZMod 92091752647) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 92091752647) ^ 21 = 10460353203 := by
        calc
          (3 : ZMod 92091752647) ^ 21 = (3 : ZMod 92091752647) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 10 * (3 : ZMod 92091752647) ^ 10) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 10460353203 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 92091752647) ^ 42 = 91484332849 := by
        calc
          (3 : ZMod 92091752647) ^ 42 = (3 : ZMod 92091752647) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 21 * (3 : ZMod 92091752647) ^ 21 := by rw [pow_add]
          _ = 91484332849 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 92091752647) ^ 85 = 56435553546 := by
        calc
          (3 : ZMod 92091752647) ^ 85 = (3 : ZMod 92091752647) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 42 * (3 : ZMod 92091752647) ^ 42) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 56435553546 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 92091752647) ^ 171 = 14405732796 := by
        calc
          (3 : ZMod 92091752647) ^ 171 = (3 : ZMod 92091752647) ^ (85 + 85 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 85 * (3 : ZMod 92091752647) ^ 85) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 14405732796 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 92091752647) ^ 343 = 52790955015 := by
        calc
          (3 : ZMod 92091752647) ^ 343 = (3 : ZMod 92091752647) ^ (171 + 171 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 171 * (3 : ZMod 92091752647) ^ 171) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 52790955015 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 92091752647) ^ 686 = 43371438568 := by
        calc
          (3 : ZMod 92091752647) ^ 686 = (3 : ZMod 92091752647) ^ (343 + 343) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 343 * (3 : ZMod 92091752647) ^ 343 := by rw [pow_add]
          _ = 43371438568 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 92091752647) ^ 1372 = 91613614082 := by
        calc
          (3 : ZMod 92091752647) ^ 1372 = (3 : ZMod 92091752647) ^ (686 + 686) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 686 * (3 : ZMod 92091752647) ^ 686 := by rw [pow_add]
          _ = 91613614082 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 92091752647) ^ 2744 = 678618783 := by
        calc
          (3 : ZMod 92091752647) ^ 2744 = (3 : ZMod 92091752647) ^ (1372 + 1372) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 1372 * (3 : ZMod 92091752647) ^ 1372 := by rw [pow_add]
          _ = 678618783 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 92091752647) ^ 5489 = 30893376038 := by
        calc
          (3 : ZMod 92091752647) ^ 5489 = (3 : ZMod 92091752647) ^ (2744 + 2744 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 2744 * (3 : ZMod 92091752647) ^ 2744) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 30893376038 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 92091752647) ^ 10978 = 60418254782 := by
        calc
          (3 : ZMod 92091752647) ^ 10978 = (3 : ZMod 92091752647) ^ (5489 + 5489) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 5489 * (3 : ZMod 92091752647) ^ 5489 := by rw [pow_add]
          _ = 60418254782 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 92091752647) ^ 21956 = 29541784242 := by
        calc
          (3 : ZMod 92091752647) ^ 21956 = (3 : ZMod 92091752647) ^ (10978 + 10978) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 10978 * (3 : ZMod 92091752647) ^ 10978 := by rw [pow_add]
          _ = 29541784242 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 92091752647) ^ 43912 = 46452067411 := by
        calc
          (3 : ZMod 92091752647) ^ 43912 = (3 : ZMod 92091752647) ^ (21956 + 21956) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 21956 * (3 : ZMod 92091752647) ^ 21956 := by rw [pow_add]
          _ = 46452067411 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 92091752647) ^ 87825 = 20736048618 := by
        calc
          (3 : ZMod 92091752647) ^ 87825 = (3 : ZMod 92091752647) ^ (43912 + 43912 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 43912 * (3 : ZMod 92091752647) ^ 43912) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 20736048618 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 92091752647) ^ 175651 = 8974752915 := by
        calc
          (3 : ZMod 92091752647) ^ 175651 = (3 : ZMod 92091752647) ^ (87825 + 87825 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 87825 * (3 : ZMod 92091752647) ^ 87825) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 8974752915 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 92091752647) ^ 351302 = 67382206330 := by
        calc
          (3 : ZMod 92091752647) ^ 351302 = (3 : ZMod 92091752647) ^ (175651 + 175651) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 175651 * (3 : ZMod 92091752647) ^ 175651 := by rw [pow_add]
          _ = 67382206330 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 92091752647) ^ 702604 = 62825144953 := by
        calc
          (3 : ZMod 92091752647) ^ 702604 = (3 : ZMod 92091752647) ^ (351302 + 351302) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 351302 * (3 : ZMod 92091752647) ^ 351302 := by rw [pow_add]
          _ = 62825144953 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 92091752647) ^ 1405208 = 13475803215 := by
        calc
          (3 : ZMod 92091752647) ^ 1405208 = (3 : ZMod 92091752647) ^ (702604 + 702604) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 702604 * (3 : ZMod 92091752647) ^ 702604 := by rw [pow_add]
          _ = 13475803215 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 92091752647) ^ 2810417 = 19710363989 := by
        calc
          (3 : ZMod 92091752647) ^ 2810417 = (3 : ZMod 92091752647) ^ (1405208 + 1405208 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 1405208 * (3 : ZMod 92091752647) ^ 1405208) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 19710363989 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 92091752647) ^ 5620834 = 86123346060 := by
        calc
          (3 : ZMod 92091752647) ^ 5620834 = (3 : ZMod 92091752647) ^ (2810417 + 2810417) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 2810417 * (3 : ZMod 92091752647) ^ 2810417 := by rw [pow_add]
          _ = 86123346060 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 92091752647) ^ 11241669 = 6567780745 := by
        calc
          (3 : ZMod 92091752647) ^ 11241669 = (3 : ZMod 92091752647) ^ (5620834 + 5620834 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 5620834 * (3 : ZMod 92091752647) ^ 5620834) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 6567780745 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 92091752647) ^ 22483338 = 35477155298 := by
        calc
          (3 : ZMod 92091752647) ^ 22483338 = (3 : ZMod 92091752647) ^ (11241669 + 11241669) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 11241669 * (3 : ZMod 92091752647) ^ 11241669 := by rw [pow_add]
          _ = 35477155298 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 92091752647) ^ 44966676 = 30180310258 := by
        calc
          (3 : ZMod 92091752647) ^ 44966676 = (3 : ZMod 92091752647) ^ (22483338 + 22483338) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 22483338 * (3 : ZMod 92091752647) ^ 22483338 := by rw [pow_add]
          _ = 30180310258 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 92091752647) ^ 89933352 = 79335029307 := by
        calc
          (3 : ZMod 92091752647) ^ 89933352 = (3 : ZMod 92091752647) ^ (44966676 + 44966676) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 44966676 * (3 : ZMod 92091752647) ^ 44966676 := by rw [pow_add]
          _ = 79335029307 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 92091752647) ^ 179866704 = 7568486211 := by
        calc
          (3 : ZMod 92091752647) ^ 179866704 = (3 : ZMod 92091752647) ^ (89933352 + 89933352) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 89933352 * (3 : ZMod 92091752647) ^ 89933352 := by rw [pow_add]
          _ = 7568486211 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 92091752647) ^ 359733408 = 13660383575 := by
        calc
          (3 : ZMod 92091752647) ^ 359733408 = (3 : ZMod 92091752647) ^ (179866704 + 179866704) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 179866704 * (3 : ZMod 92091752647) ^ 179866704 := by rw [pow_add]
          _ = 13660383575 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 92091752647) ^ 719466817 = 13669665303 := by
        calc
          (3 : ZMod 92091752647) ^ 719466817 = (3 : ZMod 92091752647) ^ (359733408 + 359733408 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 359733408 * (3 : ZMod 92091752647) ^ 359733408) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 13669665303 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 92091752647) ^ 1438933635 = 17407045832 := by
        calc
          (3 : ZMod 92091752647) ^ 1438933635 = (3 : ZMod 92091752647) ^ (719466817 + 719466817 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 719466817 * (3 : ZMod 92091752647) ^ 719466817) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 17407045832 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 92091752647) ^ 2877867270 = 68483357451 := by
        calc
          (3 : ZMod 92091752647) ^ 2877867270 = (3 : ZMod 92091752647) ^ (1438933635 + 1438933635) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 1438933635 * (3 : ZMod 92091752647) ^ 1438933635 := by rw [pow_add]
          _ = 68483357451 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 92091752647) ^ 5755734540 = 12907441357 := by
        calc
          (3 : ZMod 92091752647) ^ 5755734540 = (3 : ZMod 92091752647) ^ (2877867270 + 2877867270) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 2877867270 * (3 : ZMod 92091752647) ^ 2877867270 := by rw [pow_add]
          _ = 12907441357 := by rw [fermat_31]; decide
      have fermat_33 : (3 : ZMod 92091752647) ^ 11511469080 = 41852530422 := by
        calc
          (3 : ZMod 92091752647) ^ 11511469080 = (3 : ZMod 92091752647) ^ (5755734540 + 5755734540) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 5755734540 * (3 : ZMod 92091752647) ^ 5755734540 := by rw [pow_add]
          _ = 41852530422 := by rw [fermat_32]; decide
      have fermat_34 : (3 : ZMod 92091752647) ^ 23022938161 = 64556331410 := by
        calc
          (3 : ZMod 92091752647) ^ 23022938161 = (3 : ZMod 92091752647) ^ (11511469080 + 11511469080 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 11511469080 * (3 : ZMod 92091752647) ^ 11511469080) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 64556331410 := by rw [fermat_33]; decide
      have fermat_35 : (3 : ZMod 92091752647) ^ 46045876323 = 92091752646 := by
        calc
          (3 : ZMod 92091752647) ^ 46045876323 = (3 : ZMod 92091752647) ^ (23022938161 + 23022938161 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 23022938161 * (3 : ZMod 92091752647) ^ 23022938161) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 92091752646 := by rw [fermat_34]; decide
      have fermat_36 : (3 : ZMod 92091752647) ^ 92091752646 = 1 := by
        calc
          (3 : ZMod 92091752647) ^ 92091752646 = (3 : ZMod 92091752647) ^ (46045876323 + 46045876323) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 46045876323 * (3 : ZMod 92091752647) ^ 46045876323 := by rw [pow_add]
          _ = 1 := by rw [fermat_35]; decide
      simpa using fermat_36
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (149, 1), (103010909, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (149, 1), (103010909, 1)] : List FactorBlock).map factorBlockValue).prod = 92091752647 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact prime_lucas_103010909) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 92091752647) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 92091752647) ^ 2 = 9 := by
        calc
          (3 : ZMod 92091752647) ^ 2 = (3 : ZMod 92091752647) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 1 * (3 : ZMod 92091752647) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 92091752647) ^ 5 = 243 := by
        calc
          (3 : ZMod 92091752647) ^ 5 = (3 : ZMod 92091752647) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 2 * (3 : ZMod 92091752647) ^ 2) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 243 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 92091752647) ^ 10 = 59049 := by
        calc
          (3 : ZMod 92091752647) ^ 10 = (3 : ZMod 92091752647) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 5 * (3 : ZMod 92091752647) ^ 5 := by rw [pow_add]
          _ = 59049 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 92091752647) ^ 21 = 10460353203 := by
        calc
          (3 : ZMod 92091752647) ^ 21 = (3 : ZMod 92091752647) ^ (10 + 10 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 10 * (3 : ZMod 92091752647) ^ 10) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 10460353203 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 92091752647) ^ 42 = 91484332849 := by
        calc
          (3 : ZMod 92091752647) ^ 42 = (3 : ZMod 92091752647) ^ (21 + 21) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 21 * (3 : ZMod 92091752647) ^ 21 := by rw [pow_add]
          _ = 91484332849 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 92091752647) ^ 85 = 56435553546 := by
        calc
          (3 : ZMod 92091752647) ^ 85 = (3 : ZMod 92091752647) ^ (42 + 42 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 42 * (3 : ZMod 92091752647) ^ 42) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 56435553546 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 92091752647) ^ 171 = 14405732796 := by
        calc
          (3 : ZMod 92091752647) ^ 171 = (3 : ZMod 92091752647) ^ (85 + 85 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 85 * (3 : ZMod 92091752647) ^ 85) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 14405732796 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 92091752647) ^ 343 = 52790955015 := by
        calc
          (3 : ZMod 92091752647) ^ 343 = (3 : ZMod 92091752647) ^ (171 + 171 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 171 * (3 : ZMod 92091752647) ^ 171) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 52790955015 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 92091752647) ^ 686 = 43371438568 := by
        calc
          (3 : ZMod 92091752647) ^ 686 = (3 : ZMod 92091752647) ^ (343 + 343) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 343 * (3 : ZMod 92091752647) ^ 343 := by rw [pow_add]
          _ = 43371438568 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 92091752647) ^ 1372 = 91613614082 := by
        calc
          (3 : ZMod 92091752647) ^ 1372 = (3 : ZMod 92091752647) ^ (686 + 686) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 686 * (3 : ZMod 92091752647) ^ 686 := by rw [pow_add]
          _ = 91613614082 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 92091752647) ^ 2744 = 678618783 := by
        calc
          (3 : ZMod 92091752647) ^ 2744 = (3 : ZMod 92091752647) ^ (1372 + 1372) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 1372 * (3 : ZMod 92091752647) ^ 1372 := by rw [pow_add]
          _ = 678618783 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 92091752647) ^ 5489 = 30893376038 := by
        calc
          (3 : ZMod 92091752647) ^ 5489 = (3 : ZMod 92091752647) ^ (2744 + 2744 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 2744 * (3 : ZMod 92091752647) ^ 2744) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 30893376038 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 92091752647) ^ 10978 = 60418254782 := by
        calc
          (3 : ZMod 92091752647) ^ 10978 = (3 : ZMod 92091752647) ^ (5489 + 5489) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 5489 * (3 : ZMod 92091752647) ^ 5489 := by rw [pow_add]
          _ = 60418254782 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 92091752647) ^ 21956 = 29541784242 := by
        calc
          (3 : ZMod 92091752647) ^ 21956 = (3 : ZMod 92091752647) ^ (10978 + 10978) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 10978 * (3 : ZMod 92091752647) ^ 10978 := by rw [pow_add]
          _ = 29541784242 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 92091752647) ^ 43912 = 46452067411 := by
        calc
          (3 : ZMod 92091752647) ^ 43912 = (3 : ZMod 92091752647) ^ (21956 + 21956) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 21956 * (3 : ZMod 92091752647) ^ 21956 := by rw [pow_add]
          _ = 46452067411 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 92091752647) ^ 87825 = 20736048618 := by
        calc
          (3 : ZMod 92091752647) ^ 87825 = (3 : ZMod 92091752647) ^ (43912 + 43912 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 43912 * (3 : ZMod 92091752647) ^ 43912) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 20736048618 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 92091752647) ^ 175651 = 8974752915 := by
        calc
          (3 : ZMod 92091752647) ^ 175651 = (3 : ZMod 92091752647) ^ (87825 + 87825 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 87825 * (3 : ZMod 92091752647) ^ 87825) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 8974752915 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 92091752647) ^ 351302 = 67382206330 := by
        calc
          (3 : ZMod 92091752647) ^ 351302 = (3 : ZMod 92091752647) ^ (175651 + 175651) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 175651 * (3 : ZMod 92091752647) ^ 175651 := by rw [pow_add]
          _ = 67382206330 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 92091752647) ^ 702604 = 62825144953 := by
        calc
          (3 : ZMod 92091752647) ^ 702604 = (3 : ZMod 92091752647) ^ (351302 + 351302) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 351302 * (3 : ZMod 92091752647) ^ 351302 := by rw [pow_add]
          _ = 62825144953 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 92091752647) ^ 1405208 = 13475803215 := by
        calc
          (3 : ZMod 92091752647) ^ 1405208 = (3 : ZMod 92091752647) ^ (702604 + 702604) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 702604 * (3 : ZMod 92091752647) ^ 702604 := by rw [pow_add]
          _ = 13475803215 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 92091752647) ^ 2810417 = 19710363989 := by
        calc
          (3 : ZMod 92091752647) ^ 2810417 = (3 : ZMod 92091752647) ^ (1405208 + 1405208 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 1405208 * (3 : ZMod 92091752647) ^ 1405208) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 19710363989 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 92091752647) ^ 5620834 = 86123346060 := by
        calc
          (3 : ZMod 92091752647) ^ 5620834 = (3 : ZMod 92091752647) ^ (2810417 + 2810417) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 2810417 * (3 : ZMod 92091752647) ^ 2810417 := by rw [pow_add]
          _ = 86123346060 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 92091752647) ^ 11241669 = 6567780745 := by
        calc
          (3 : ZMod 92091752647) ^ 11241669 = (3 : ZMod 92091752647) ^ (5620834 + 5620834 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 5620834 * (3 : ZMod 92091752647) ^ 5620834) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 6567780745 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 92091752647) ^ 22483338 = 35477155298 := by
        calc
          (3 : ZMod 92091752647) ^ 22483338 = (3 : ZMod 92091752647) ^ (11241669 + 11241669) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 11241669 * (3 : ZMod 92091752647) ^ 11241669 := by rw [pow_add]
          _ = 35477155298 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 92091752647) ^ 44966676 = 30180310258 := by
        calc
          (3 : ZMod 92091752647) ^ 44966676 = (3 : ZMod 92091752647) ^ (22483338 + 22483338) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 22483338 * (3 : ZMod 92091752647) ^ 22483338 := by rw [pow_add]
          _ = 30180310258 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 92091752647) ^ 89933352 = 79335029307 := by
        calc
          (3 : ZMod 92091752647) ^ 89933352 = (3 : ZMod 92091752647) ^ (44966676 + 44966676) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 44966676 * (3 : ZMod 92091752647) ^ 44966676 := by rw [pow_add]
          _ = 79335029307 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 92091752647) ^ 179866704 = 7568486211 := by
        calc
          (3 : ZMod 92091752647) ^ 179866704 = (3 : ZMod 92091752647) ^ (89933352 + 89933352) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 89933352 * (3 : ZMod 92091752647) ^ 89933352 := by rw [pow_add]
          _ = 7568486211 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 92091752647) ^ 359733408 = 13660383575 := by
        calc
          (3 : ZMod 92091752647) ^ 359733408 = (3 : ZMod 92091752647) ^ (179866704 + 179866704) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 179866704 * (3 : ZMod 92091752647) ^ 179866704 := by rw [pow_add]
          _ = 13660383575 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 92091752647) ^ 719466817 = 13669665303 := by
        calc
          (3 : ZMod 92091752647) ^ 719466817 = (3 : ZMod 92091752647) ^ (359733408 + 359733408 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 359733408 * (3 : ZMod 92091752647) ^ 359733408) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 13669665303 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 92091752647) ^ 1438933635 = 17407045832 := by
        calc
          (3 : ZMod 92091752647) ^ 1438933635 = (3 : ZMod 92091752647) ^ (719466817 + 719466817 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 719466817 * (3 : ZMod 92091752647) ^ 719466817) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 17407045832 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 92091752647) ^ 2877867270 = 68483357451 := by
        calc
          (3 : ZMod 92091752647) ^ 2877867270 = (3 : ZMod 92091752647) ^ (1438933635 + 1438933635) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 1438933635 * (3 : ZMod 92091752647) ^ 1438933635 := by rw [pow_add]
          _ = 68483357451 := by rw [factor_0_30]; decide
      have factor_0_32 : (3 : ZMod 92091752647) ^ 5755734540 = 12907441357 := by
        calc
          (3 : ZMod 92091752647) ^ 5755734540 = (3 : ZMod 92091752647) ^ (2877867270 + 2877867270) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 2877867270 * (3 : ZMod 92091752647) ^ 2877867270 := by rw [pow_add]
          _ = 12907441357 := by rw [factor_0_31]; decide
      have factor_0_33 : (3 : ZMod 92091752647) ^ 11511469080 = 41852530422 := by
        calc
          (3 : ZMod 92091752647) ^ 11511469080 = (3 : ZMod 92091752647) ^ (5755734540 + 5755734540) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 5755734540 * (3 : ZMod 92091752647) ^ 5755734540 := by rw [pow_add]
          _ = 41852530422 := by rw [factor_0_32]; decide
      have factor_0_34 : (3 : ZMod 92091752647) ^ 23022938161 = 64556331410 := by
        calc
          (3 : ZMod 92091752647) ^ 23022938161 = (3 : ZMod 92091752647) ^ (11511469080 + 11511469080 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 11511469080 * (3 : ZMod 92091752647) ^ 11511469080) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 64556331410 := by rw [factor_0_33]; decide
      have factor_0_35 : (3 : ZMod 92091752647) ^ 46045876323 = 92091752646 := by
        calc
          (3 : ZMod 92091752647) ^ 46045876323 = (3 : ZMod 92091752647) ^ (23022938161 + 23022938161 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 23022938161 * (3 : ZMod 92091752647) ^ 23022938161) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 92091752646 := by rw [factor_0_34]; decide
      change (3 : ZMod 92091752647) ^ 46045876323 ≠ 1
      rw [factor_0_35]
      decide
    ·
      have factor_1_0 : (3 : ZMod 92091752647) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 92091752647) ^ 3 = 27 := by
        calc
          (3 : ZMod 92091752647) ^ 3 = (3 : ZMod 92091752647) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 1 * (3 : ZMod 92091752647) ^ 1) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 92091752647) ^ 7 = 2187 := by
        calc
          (3 : ZMod 92091752647) ^ 7 = (3 : ZMod 92091752647) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 3 * (3 : ZMod 92091752647) ^ 3) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 92091752647) ^ 14 = 4782969 := by
        calc
          (3 : ZMod 92091752647) ^ 14 = (3 : ZMod 92091752647) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 7 * (3 : ZMod 92091752647) ^ 7 := by rw [pow_add]
          _ = 4782969 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 92091752647) ^ 28 = 38037798505 := by
        calc
          (3 : ZMod 92091752647) ^ 28 = (3 : ZMod 92091752647) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 14 * (3 : ZMod 92091752647) ^ 14 := by rw [pow_add]
          _ = 38037798505 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 92091752647) ^ 57 = 29554309235 := by
        calc
          (3 : ZMod 92091752647) ^ 57 = (3 : ZMod 92091752647) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 28 * (3 : ZMod 92091752647) ^ 28) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 29554309235 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 92091752647) ^ 114 = 42945592919 := by
        calc
          (3 : ZMod 92091752647) ^ 114 = (3 : ZMod 92091752647) ^ (57 + 57) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 57 * (3 : ZMod 92091752647) ^ 57 := by rw [pow_add]
          _ = 42945592919 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 92091752647) ^ 228 = 87092108872 := by
        calc
          (3 : ZMod 92091752647) ^ 228 = (3 : ZMod 92091752647) ^ (114 + 114) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 114 * (3 : ZMod 92091752647) ^ 114 := by rw [pow_add]
          _ = 87092108872 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 92091752647) ^ 457 = 27129161530 := by
        calc
          (3 : ZMod 92091752647) ^ 457 = (3 : ZMod 92091752647) ^ (228 + 228 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 228 * (3 : ZMod 92091752647) ^ 228) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 27129161530 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 92091752647) ^ 914 = 66249504790 := by
        calc
          (3 : ZMod 92091752647) ^ 914 = (3 : ZMod 92091752647) ^ (457 + 457) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 457 * (3 : ZMod 92091752647) ^ 457 := by rw [pow_add]
          _ = 66249504790 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 92091752647) ^ 1829 = 86431076781 := by
        calc
          (3 : ZMod 92091752647) ^ 1829 = (3 : ZMod 92091752647) ^ (914 + 914 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 914 * (3 : ZMod 92091752647) ^ 914) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 86431076781 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 92091752647) ^ 3659 = 88664489726 := by
        calc
          (3 : ZMod 92091752647) ^ 3659 = (3 : ZMod 92091752647) ^ (1829 + 1829 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 1829 * (3 : ZMod 92091752647) ^ 1829) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 88664489726 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 92091752647) ^ 7318 = 14838794190 := by
        calc
          (3 : ZMod 92091752647) ^ 7318 = (3 : ZMod 92091752647) ^ (3659 + 3659) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 3659 * (3 : ZMod 92091752647) ^ 3659 := by rw [pow_add]
          _ = 14838794190 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 92091752647) ^ 14637 = 60042940002 := by
        calc
          (3 : ZMod 92091752647) ^ 14637 = (3 : ZMod 92091752647) ^ (7318 + 7318 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 7318 * (3 : ZMod 92091752647) ^ 7318) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 60042940002 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 92091752647) ^ 29275 = 42045560545 := by
        calc
          (3 : ZMod 92091752647) ^ 29275 = (3 : ZMod 92091752647) ^ (14637 + 14637 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 14637 * (3 : ZMod 92091752647) ^ 14637) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 42045560545 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 92091752647) ^ 58550 = 73901962883 := by
        calc
          (3 : ZMod 92091752647) ^ 58550 = (3 : ZMod 92091752647) ^ (29275 + 29275) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 29275 * (3 : ZMod 92091752647) ^ 29275 := by rw [pow_add]
          _ = 73901962883 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 92091752647) ^ 117100 = 30088005876 := by
        calc
          (3 : ZMod 92091752647) ^ 117100 = (3 : ZMod 92091752647) ^ (58550 + 58550) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 58550 * (3 : ZMod 92091752647) ^ 58550 := by rw [pow_add]
          _ = 30088005876 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 92091752647) ^ 234201 = 16479293745 := by
        calc
          (3 : ZMod 92091752647) ^ 234201 = (3 : ZMod 92091752647) ^ (117100 + 117100 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 117100 * (3 : ZMod 92091752647) ^ 117100) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 16479293745 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 92091752647) ^ 468402 = 84114164472 := by
        calc
          (3 : ZMod 92091752647) ^ 468402 = (3 : ZMod 92091752647) ^ (234201 + 234201) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 234201 * (3 : ZMod 92091752647) ^ 234201 := by rw [pow_add]
          _ = 84114164472 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 92091752647) ^ 936805 = 56428967883 := by
        calc
          (3 : ZMod 92091752647) ^ 936805 = (3 : ZMod 92091752647) ^ (468402 + 468402 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 468402 * (3 : ZMod 92091752647) ^ 468402) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 56428967883 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 92091752647) ^ 1873611 = 6210334133 := by
        calc
          (3 : ZMod 92091752647) ^ 1873611 = (3 : ZMod 92091752647) ^ (936805 + 936805 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 936805 * (3 : ZMod 92091752647) ^ 936805) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 6210334133 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 92091752647) ^ 3747223 = 19212967261 := by
        calc
          (3 : ZMod 92091752647) ^ 3747223 = (3 : ZMod 92091752647) ^ (1873611 + 1873611 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 1873611 * (3 : ZMod 92091752647) ^ 1873611) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 19212967261 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 92091752647) ^ 7494446 = 23287797896 := by
        calc
          (3 : ZMod 92091752647) ^ 7494446 = (3 : ZMod 92091752647) ^ (3747223 + 3747223) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 3747223 * (3 : ZMod 92091752647) ^ 3747223 := by rw [pow_add]
          _ = 23287797896 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 92091752647) ^ 14988892 = 22233244531 := by
        calc
          (3 : ZMod 92091752647) ^ 14988892 = (3 : ZMod 92091752647) ^ (7494446 + 7494446) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 7494446 * (3 : ZMod 92091752647) ^ 7494446 := by rw [pow_add]
          _ = 22233244531 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 92091752647) ^ 29977784 = 64546462279 := by
        calc
          (3 : ZMod 92091752647) ^ 29977784 = (3 : ZMod 92091752647) ^ (14988892 + 14988892) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 14988892 * (3 : ZMod 92091752647) ^ 14988892 := by rw [pow_add]
          _ = 64546462279 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 92091752647) ^ 59955568 = 52034267772 := by
        calc
          (3 : ZMod 92091752647) ^ 59955568 = (3 : ZMod 92091752647) ^ (29977784 + 29977784) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 29977784 * (3 : ZMod 92091752647) ^ 29977784 := by rw [pow_add]
          _ = 52034267772 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 92091752647) ^ 119911136 = 56240589155 := by
        calc
          (3 : ZMod 92091752647) ^ 119911136 = (3 : ZMod 92091752647) ^ (59955568 + 59955568) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 59955568 * (3 : ZMod 92091752647) ^ 59955568 := by rw [pow_add]
          _ = 56240589155 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 92091752647) ^ 239822272 = 47205460081 := by
        calc
          (3 : ZMod 92091752647) ^ 239822272 = (3 : ZMod 92091752647) ^ (119911136 + 119911136) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 119911136 * (3 : ZMod 92091752647) ^ 119911136 := by rw [pow_add]
          _ = 47205460081 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 92091752647) ^ 479644545 = 27404486380 := by
        calc
          (3 : ZMod 92091752647) ^ 479644545 = (3 : ZMod 92091752647) ^ (239822272 + 239822272 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 239822272 * (3 : ZMod 92091752647) ^ 239822272) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 27404486380 := by rw [factor_1_27]; decide
      have factor_1_29 : (3 : ZMod 92091752647) ^ 959289090 = 67749101122 := by
        calc
          (3 : ZMod 92091752647) ^ 959289090 = (3 : ZMod 92091752647) ^ (479644545 + 479644545) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 479644545 * (3 : ZMod 92091752647) ^ 479644545 := by rw [pow_add]
          _ = 67749101122 := by rw [factor_1_28]; decide
      have factor_1_30 : (3 : ZMod 92091752647) ^ 1918578180 = 88799180523 := by
        calc
          (3 : ZMod 92091752647) ^ 1918578180 = (3 : ZMod 92091752647) ^ (959289090 + 959289090) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 959289090 * (3 : ZMod 92091752647) ^ 959289090 := by rw [pow_add]
          _ = 88799180523 := by rw [factor_1_29]; decide
      have factor_1_31 : (3 : ZMod 92091752647) ^ 3837156360 = 16046317252 := by
        calc
          (3 : ZMod 92091752647) ^ 3837156360 = (3 : ZMod 92091752647) ^ (1918578180 + 1918578180) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 1918578180 * (3 : ZMod 92091752647) ^ 1918578180 := by rw [pow_add]
          _ = 16046317252 := by rw [factor_1_30]; decide
      have factor_1_32 : (3 : ZMod 92091752647) ^ 7674312720 = 78324042029 := by
        calc
          (3 : ZMod 92091752647) ^ 7674312720 = (3 : ZMod 92091752647) ^ (3837156360 + 3837156360) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 3837156360 * (3 : ZMod 92091752647) ^ 3837156360 := by rw [pow_add]
          _ = 78324042029 := by rw [factor_1_31]; decide
      have factor_1_33 : (3 : ZMod 92091752647) ^ 15348625441 = 50788620792 := by
        calc
          (3 : ZMod 92091752647) ^ 15348625441 = (3 : ZMod 92091752647) ^ (7674312720 + 7674312720 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 7674312720 * (3 : ZMod 92091752647) ^ 7674312720) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 50788620792 := by rw [factor_1_32]; decide
      have factor_1_34 : (3 : ZMod 92091752647) ^ 30697250882 = 50788620791 := by
        calc
          (3 : ZMod 92091752647) ^ 30697250882 = (3 : ZMod 92091752647) ^ (15348625441 + 15348625441) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 15348625441 * (3 : ZMod 92091752647) ^ 15348625441 := by rw [pow_add]
          _ = 50788620791 := by rw [factor_1_33]; decide
      change (3 : ZMod 92091752647) ^ 30697250882 ≠ 1
      rw [factor_1_34]
      decide
    ·
      have factor_2_0 : (3 : ZMod 92091752647) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 92091752647) ^ 2 = 9 := by
        calc
          (3 : ZMod 92091752647) ^ 2 = (3 : ZMod 92091752647) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 1 * (3 : ZMod 92091752647) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 92091752647) ^ 4 = 81 := by
        calc
          (3 : ZMod 92091752647) ^ 4 = (3 : ZMod 92091752647) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 2 * (3 : ZMod 92091752647) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 92091752647) ^ 9 = 19683 := by
        calc
          (3 : ZMod 92091752647) ^ 9 = (3 : ZMod 92091752647) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 4 * (3 : ZMod 92091752647) ^ 4) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 92091752647) ^ 18 = 387420489 := by
        calc
          (3 : ZMod 92091752647) ^ 18 = (3 : ZMod 92091752647) ^ (9 + 9) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 9 * (3 : ZMod 92091752647) ^ 9 := by rw [pow_add]
          _ = 387420489 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 92091752647) ^ 36 = 89438070582 := by
        calc
          (3 : ZMod 92091752647) ^ 36 = (3 : ZMod 92091752647) ^ (18 + 18) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 18 * (3 : ZMod 92091752647) ^ 18 := by rw [pow_add]
          _ = 89438070582 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 92091752647) ^ 73 = 36547868709 := by
        calc
          (3 : ZMod 92091752647) ^ 73 = (3 : ZMod 92091752647) ^ (36 + 36 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 36 * (3 : ZMod 92091752647) ^ 36) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 36547868709 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 92091752647) ^ 147 = 59801293059 := by
        calc
          (3 : ZMod 92091752647) ^ 147 = (3 : ZMod 92091752647) ^ (73 + 73 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 73 * (3 : ZMod 92091752647) ^ 73) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 59801293059 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 92091752647) ^ 294 = 42380694978 := by
        calc
          (3 : ZMod 92091752647) ^ 294 = (3 : ZMod 92091752647) ^ (147 + 147) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 147 * (3 : ZMod 92091752647) ^ 147 := by rw [pow_add]
          _ = 42380694978 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 92091752647) ^ 589 = 57836976434 := by
        calc
          (3 : ZMod 92091752647) ^ 589 = (3 : ZMod 92091752647) ^ (294 + 294 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 294 * (3 : ZMod 92091752647) ^ 294) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 57836976434 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 92091752647) ^ 1178 = 41624113047 := by
        calc
          (3 : ZMod 92091752647) ^ 1178 = (3 : ZMod 92091752647) ^ (589 + 589) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 589 * (3 : ZMod 92091752647) ^ 589 := by rw [pow_add]
          _ = 41624113047 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 92091752647) ^ 2357 = 24270471412 := by
        calc
          (3 : ZMod 92091752647) ^ 2357 = (3 : ZMod 92091752647) ^ (1178 + 1178 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 1178 * (3 : ZMod 92091752647) ^ 1178) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 24270471412 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 92091752647) ^ 4715 = 1588399357 := by
        calc
          (3 : ZMod 92091752647) ^ 4715 = (3 : ZMod 92091752647) ^ (2357 + 2357 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 2357 * (3 : ZMod 92091752647) ^ 2357) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 1588399357 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 92091752647) ^ 9430 = 3188379727 := by
        calc
          (3 : ZMod 92091752647) ^ 9430 = (3 : ZMod 92091752647) ^ (4715 + 4715) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 4715 * (3 : ZMod 92091752647) ^ 4715 := by rw [pow_add]
          _ = 3188379727 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 92091752647) ^ 18861 = 45758273709 := by
        calc
          (3 : ZMod 92091752647) ^ 18861 = (3 : ZMod 92091752647) ^ (9430 + 9430 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 9430 * (3 : ZMod 92091752647) ^ 9430) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 45758273709 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 92091752647) ^ 37723 = 28575547466 := by
        calc
          (3 : ZMod 92091752647) ^ 37723 = (3 : ZMod 92091752647) ^ (18861 + 18861 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 18861 * (3 : ZMod 92091752647) ^ 18861) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 28575547466 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 92091752647) ^ 75447 = 22282718758 := by
        calc
          (3 : ZMod 92091752647) ^ 75447 = (3 : ZMod 92091752647) ^ (37723 + 37723 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 37723 * (3 : ZMod 92091752647) ^ 37723) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 22282718758 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 92091752647) ^ 150894 = 70343075188 := by
        calc
          (3 : ZMod 92091752647) ^ 150894 = (3 : ZMod 92091752647) ^ (75447 + 75447) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 75447 * (3 : ZMod 92091752647) ^ 75447 := by rw [pow_add]
          _ = 70343075188 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 92091752647) ^ 301789 = 57105363447 := by
        calc
          (3 : ZMod 92091752647) ^ 301789 = (3 : ZMod 92091752647) ^ (150894 + 150894 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 150894 * (3 : ZMod 92091752647) ^ 150894) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 57105363447 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 92091752647) ^ 603579 = 11352341910 := by
        calc
          (3 : ZMod 92091752647) ^ 603579 = (3 : ZMod 92091752647) ^ (301789 + 301789 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 301789 * (3 : ZMod 92091752647) ^ 301789) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 11352341910 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 92091752647) ^ 1207159 = 16712114912 := by
        calc
          (3 : ZMod 92091752647) ^ 1207159 = (3 : ZMod 92091752647) ^ (603579 + 603579 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 603579 * (3 : ZMod 92091752647) ^ 603579) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 16712114912 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 92091752647) ^ 2414318 = 34715285876 := by
        calc
          (3 : ZMod 92091752647) ^ 2414318 = (3 : ZMod 92091752647) ^ (1207159 + 1207159) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 1207159 * (3 : ZMod 92091752647) ^ 1207159 := by rw [pow_add]
          _ = 34715285876 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 92091752647) ^ 4828636 = 12854652197 := by
        calc
          (3 : ZMod 92091752647) ^ 4828636 = (3 : ZMod 92091752647) ^ (2414318 + 2414318) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 2414318 * (3 : ZMod 92091752647) ^ 2414318 := by rw [pow_add]
          _ = 12854652197 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 92091752647) ^ 9657272 = 10821364168 := by
        calc
          (3 : ZMod 92091752647) ^ 9657272 = (3 : ZMod 92091752647) ^ (4828636 + 4828636) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 4828636 * (3 : ZMod 92091752647) ^ 4828636 := by rw [pow_add]
          _ = 10821364168 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 92091752647) ^ 19314545 = 52784813229 := by
        calc
          (3 : ZMod 92091752647) ^ 19314545 = (3 : ZMod 92091752647) ^ (9657272 + 9657272 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 9657272 * (3 : ZMod 92091752647) ^ 9657272) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 52784813229 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 92091752647) ^ 38629090 = 8107385898 := by
        calc
          (3 : ZMod 92091752647) ^ 38629090 = (3 : ZMod 92091752647) ^ (19314545 + 19314545) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 19314545 * (3 : ZMod 92091752647) ^ 19314545 := by rw [pow_add]
          _ = 8107385898 := by rw [factor_2_24]; decide
      have factor_2_26 : (3 : ZMod 92091752647) ^ 77258181 = 84378763301 := by
        calc
          (3 : ZMod 92091752647) ^ 77258181 = (3 : ZMod 92091752647) ^ (38629090 + 38629090 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 38629090 * (3 : ZMod 92091752647) ^ 38629090) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 84378763301 := by rw [factor_2_25]; decide
      have factor_2_27 : (3 : ZMod 92091752647) ^ 154516363 = 91616080514 := by
        calc
          (3 : ZMod 92091752647) ^ 154516363 = (3 : ZMod 92091752647) ^ (77258181 + 77258181 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 77258181 * (3 : ZMod 92091752647) ^ 77258181) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 91616080514 := by rw [factor_2_26]; decide
      have factor_2_28 : (3 : ZMod 92091752647) ^ 309032727 = 17909243233 := by
        calc
          (3 : ZMod 92091752647) ^ 309032727 = (3 : ZMod 92091752647) ^ (154516363 + 154516363 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 154516363 * (3 : ZMod 92091752647) ^ 154516363) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 17909243233 := by rw [factor_2_27]; decide
      have factor_2_29 : (3 : ZMod 92091752647) ^ 618065454 = 56910655034 := by
        calc
          (3 : ZMod 92091752647) ^ 618065454 = (3 : ZMod 92091752647) ^ (309032727 + 309032727) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 309032727 * (3 : ZMod 92091752647) ^ 309032727 := by rw [pow_add]
          _ = 56910655034 := by rw [factor_2_28]; decide
      change (3 : ZMod 92091752647) ^ 618065454 ≠ 1
      rw [factor_2_29]
      decide
    ·
      have factor_3_0 : (3 : ZMod 92091752647) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 92091752647) ^ 3 = 27 := by
        calc
          (3 : ZMod 92091752647) ^ 3 = (3 : ZMod 92091752647) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 1 * (3 : ZMod 92091752647) ^ 1) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 92091752647) ^ 6 = 729 := by
        calc
          (3 : ZMod 92091752647) ^ 6 = (3 : ZMod 92091752647) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 3 * (3 : ZMod 92091752647) ^ 3 := by rw [pow_add]
          _ = 729 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 92091752647) ^ 13 = 1594323 := by
        calc
          (3 : ZMod 92091752647) ^ 13 = (3 : ZMod 92091752647) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 6 * (3 : ZMod 92091752647) ^ 6) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 1594323 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 92091752647) ^ 27 = 74073767933 := by
        calc
          (3 : ZMod 92091752647) ^ 27 = (3 : ZMod 92091752647) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 13 * (3 : ZMod 92091752647) ^ 13) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 74073767933 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 92091752647) ^ 55 = 13516229098 := by
        calc
          (3 : ZMod 92091752647) ^ 55 = (3 : ZMod 92091752647) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 27 * (3 : ZMod 92091752647) ^ 27) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 13516229098 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 92091752647) ^ 111 = 56163467973 := by
        calc
          (3 : ZMod 92091752647) ^ 111 = (3 : ZMod 92091752647) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 55 * (3 : ZMod 92091752647) ^ 55) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 56163467973 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 92091752647) ^ 223 = 27265870563 := by
        calc
          (3 : ZMod 92091752647) ^ 223 = (3 : ZMod 92091752647) ^ (111 + 111 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 111 * (3 : ZMod 92091752647) ^ 111) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 27265870563 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 92091752647) ^ 447 = 57262069118 := by
        calc
          (3 : ZMod 92091752647) ^ 447 = (3 : ZMod 92091752647) ^ (223 + 223 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = ((3 : ZMod 92091752647) ^ 223 * (3 : ZMod 92091752647) ^ 223) * (3 : ZMod 92091752647) := by rw [pow_succ, pow_add]
          _ = 57262069118 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 92091752647) ^ 894 = 12709353940 := by
        calc
          (3 : ZMod 92091752647) ^ 894 = (3 : ZMod 92091752647) ^ (447 + 447) :=
            congrArg (fun n : ℕ => (3 : ZMod 92091752647) ^ n) (by norm_num)
          _ = (3 : ZMod 92091752647) ^ 447 * (3 : ZMod 92091752647) ^ 447 := by rw [pow_add]
          _ = 12709353940 := by rw [factor_3_8]; decide
      change (3 : ZMod 92091752647) ^ 894 ≠ 1
      rw [factor_3_9]
      decide

#print axioms prime_lucas_92091752647

end TotientTailPeriodKiller
end Erdos249257
