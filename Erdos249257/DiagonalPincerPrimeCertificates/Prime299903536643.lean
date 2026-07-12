import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime149951768321

/-! A bounded Lucas certificate for one t=32 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_299903536643 : Nat.Prime 299903536643 := by
  apply lucas_primality 299903536643 (2 : ZMod 299903536643)
  ·
      have fermat_0 : (2 : ZMod 299903536643) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 299903536643) ^ 2 = 4 := by
        calc
          (2 : ZMod 299903536643) ^ 2 = (2 : ZMod 299903536643) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 1 * (2 : ZMod 299903536643) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 299903536643) ^ 4 = 16 := by
        calc
          (2 : ZMod 299903536643) ^ 4 = (2 : ZMod 299903536643) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 2 * (2 : ZMod 299903536643) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 299903536643) ^ 8 = 256 := by
        calc
          (2 : ZMod 299903536643) ^ 8 = (2 : ZMod 299903536643) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 4 * (2 : ZMod 299903536643) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 299903536643) ^ 17 = 131072 := by
        calc
          (2 : ZMod 299903536643) ^ 17 = (2 : ZMod 299903536643) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 8 * (2 : ZMod 299903536643) ^ 8) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 299903536643) ^ 34 = 17179869184 := by
        calc
          (2 : ZMod 299903536643) ^ 34 = (2 : ZMod 299903536643) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 17 * (2 : ZMod 299903536643) ^ 17 := by rw [pow_add]
          _ = 17179869184 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 299903536643) ^ 69 = 194444704056 := by
        calc
          (2 : ZMod 299903536643) ^ 69 = (2 : ZMod 299903536643) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 34 * (2 : ZMod 299903536643) ^ 34) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 194444704056 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 299903536643) ^ 139 = 173936475234 := by
        calc
          (2 : ZMod 299903536643) ^ 139 = (2 : ZMod 299903536643) ^ (69 + 69 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 69 * (2 : ZMod 299903536643) ^ 69) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 173936475234 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 299903536643) ^ 279 = 69906125016 := by
        calc
          (2 : ZMod 299903536643) ^ 279 = (2 : ZMod 299903536643) ^ (139 + 139 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 139 * (2 : ZMod 299903536643) ^ 139) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 69906125016 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 299903536643) ^ 558 = 72294708844 := by
        calc
          (2 : ZMod 299903536643) ^ 558 = (2 : ZMod 299903536643) ^ (279 + 279) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 279 * (2 : ZMod 299903536643) ^ 279 := by rw [pow_add]
          _ = 72294708844 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 299903536643) ^ 1117 = 107658454836 := by
        calc
          (2 : ZMod 299903536643) ^ 1117 = (2 : ZMod 299903536643) ^ (558 + 558 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 558 * (2 : ZMod 299903536643) ^ 558) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 107658454836 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 299903536643) ^ 2234 = 178496741821 := by
        calc
          (2 : ZMod 299903536643) ^ 2234 = (2 : ZMod 299903536643) ^ (1117 + 1117) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 1117 * (2 : ZMod 299903536643) ^ 1117 := by rw [pow_add]
          _ = 178496741821 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 299903536643) ^ 4468 = 199122196544 := by
        calc
          (2 : ZMod 299903536643) ^ 4468 = (2 : ZMod 299903536643) ^ (2234 + 2234) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 2234 * (2 : ZMod 299903536643) ^ 2234 := by rw [pow_add]
          _ = 199122196544 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 299903536643) ^ 8937 = 152817537458 := by
        calc
          (2 : ZMod 299903536643) ^ 8937 = (2 : ZMod 299903536643) ^ (4468 + 4468 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 4468 * (2 : ZMod 299903536643) ^ 4468) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 152817537458 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 299903536643) ^ 17875 = 290269217301 := by
        calc
          (2 : ZMod 299903536643) ^ 17875 = (2 : ZMod 299903536643) ^ (8937 + 8937 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 8937 * (2 : ZMod 299903536643) ^ 8937) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 290269217301 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 299903536643) ^ 35751 = 262391810319 := by
        calc
          (2 : ZMod 299903536643) ^ 35751 = (2 : ZMod 299903536643) ^ (17875 + 17875 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 17875 * (2 : ZMod 299903536643) ^ 17875) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 262391810319 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 299903536643) ^ 71502 = 58116726375 := by
        calc
          (2 : ZMod 299903536643) ^ 71502 = (2 : ZMod 299903536643) ^ (35751 + 35751) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 35751 * (2 : ZMod 299903536643) ^ 35751 := by rw [pow_add]
          _ = 58116726375 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 299903536643) ^ 143005 = 42090394614 := by
        calc
          (2 : ZMod 299903536643) ^ 143005 = (2 : ZMod 299903536643) ^ (71502 + 71502 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 71502 * (2 : ZMod 299903536643) ^ 71502) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 42090394614 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 299903536643) ^ 286010 = 290060661972 := by
        calc
          (2 : ZMod 299903536643) ^ 286010 = (2 : ZMod 299903536643) ^ (143005 + 143005) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 143005 * (2 : ZMod 299903536643) ^ 143005 := by rw [pow_add]
          _ = 290060661972 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 299903536643) ^ 572020 = 43918014244 := by
        calc
          (2 : ZMod 299903536643) ^ 572020 = (2 : ZMod 299903536643) ^ (286010 + 286010) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 286010 * (2 : ZMod 299903536643) ^ 286010 := by rw [pow_add]
          _ = 43918014244 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 299903536643) ^ 1144041 = 32158998770 := by
        calc
          (2 : ZMod 299903536643) ^ 1144041 = (2 : ZMod 299903536643) ^ (572020 + 572020 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 572020 * (2 : ZMod 299903536643) ^ 572020) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 32158998770 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 299903536643) ^ 2288082 = 182660578876 := by
        calc
          (2 : ZMod 299903536643) ^ 2288082 = (2 : ZMod 299903536643) ^ (1144041 + 1144041) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 1144041 * (2 : ZMod 299903536643) ^ 1144041 := by rw [pow_add]
          _ = 182660578876 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 299903536643) ^ 4576164 = 160685368270 := by
        calc
          (2 : ZMod 299903536643) ^ 4576164 = (2 : ZMod 299903536643) ^ (2288082 + 2288082) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 2288082 * (2 : ZMod 299903536643) ^ 2288082 := by rw [pow_add]
          _ = 160685368270 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 299903536643) ^ 9152329 = 186854248007 := by
        calc
          (2 : ZMod 299903536643) ^ 9152329 = (2 : ZMod 299903536643) ^ (4576164 + 4576164 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 4576164 * (2 : ZMod 299903536643) ^ 4576164) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 186854248007 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 299903536643) ^ 18304659 = 78574823404 := by
        calc
          (2 : ZMod 299903536643) ^ 18304659 = (2 : ZMod 299903536643) ^ (9152329 + 9152329 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 9152329 * (2 : ZMod 299903536643) ^ 9152329) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 78574823404 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 299903536643) ^ 36609318 = 121507255774 := by
        calc
          (2 : ZMod 299903536643) ^ 36609318 = (2 : ZMod 299903536643) ^ (18304659 + 18304659) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 18304659 * (2 : ZMod 299903536643) ^ 18304659 := by rw [pow_add]
          _ = 121507255774 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 299903536643) ^ 73218636 = 72264985114 := by
        calc
          (2 : ZMod 299903536643) ^ 73218636 = (2 : ZMod 299903536643) ^ (36609318 + 36609318) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 36609318 * (2 : ZMod 299903536643) ^ 36609318 := by rw [pow_add]
          _ = 72264985114 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 299903536643) ^ 146437273 = 235340118785 := by
        calc
          (2 : ZMod 299903536643) ^ 146437273 = (2 : ZMod 299903536643) ^ (73218636 + 73218636 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 73218636 * (2 : ZMod 299903536643) ^ 73218636) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 235340118785 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 299903536643) ^ 292874547 = 289230605810 := by
        calc
          (2 : ZMod 299903536643) ^ 292874547 = (2 : ZMod 299903536643) ^ (146437273 + 146437273 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 146437273 * (2 : ZMod 299903536643) ^ 146437273) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 289230605810 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 299903536643) ^ 585749095 = 101793604500 := by
        calc
          (2 : ZMod 299903536643) ^ 585749095 = (2 : ZMod 299903536643) ^ (292874547 + 292874547 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 292874547 * (2 : ZMod 299903536643) ^ 292874547) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 101793604500 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 299903536643) ^ 1171498190 = 165207247470 := by
        calc
          (2 : ZMod 299903536643) ^ 1171498190 = (2 : ZMod 299903536643) ^ (585749095 + 585749095) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 585749095 * (2 : ZMod 299903536643) ^ 585749095 := by rw [pow_add]
          _ = 165207247470 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 299903536643) ^ 2342996380 = 237565914284 := by
        calc
          (2 : ZMod 299903536643) ^ 2342996380 = (2 : ZMod 299903536643) ^ (1171498190 + 1171498190) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 1171498190 * (2 : ZMod 299903536643) ^ 1171498190 := by rw [pow_add]
          _ = 237565914284 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 299903536643) ^ 4685992760 = 294366171058 := by
        calc
          (2 : ZMod 299903536643) ^ 4685992760 = (2 : ZMod 299903536643) ^ (2342996380 + 2342996380) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 2342996380 * (2 : ZMod 299903536643) ^ 2342996380 := by rw [pow_add]
          _ = 294366171058 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 299903536643) ^ 9371985520 = 225562384306 := by
        calc
          (2 : ZMod 299903536643) ^ 9371985520 = (2 : ZMod 299903536643) ^ (4685992760 + 4685992760) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 4685992760 * (2 : ZMod 299903536643) ^ 4685992760 := by rw [pow_add]
          _ = 225562384306 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 299903536643) ^ 18743971040 = 168745382925 := by
        calc
          (2 : ZMod 299903536643) ^ 18743971040 = (2 : ZMod 299903536643) ^ (9371985520 + 9371985520) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 9371985520 * (2 : ZMod 299903536643) ^ 9371985520 := by rw [pow_add]
          _ = 168745382925 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 299903536643) ^ 37487942080 = 78783416894 := by
        calc
          (2 : ZMod 299903536643) ^ 37487942080 = (2 : ZMod 299903536643) ^ (18743971040 + 18743971040) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 18743971040 * (2 : ZMod 299903536643) ^ 18743971040 := by rw [pow_add]
          _ = 78783416894 := by rw [fermat_34]; decide
      have fermat_36 : (2 : ZMod 299903536643) ^ 74975884160 = 286990566693 := by
        calc
          (2 : ZMod 299903536643) ^ 74975884160 = (2 : ZMod 299903536643) ^ (37487942080 + 37487942080) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 37487942080 * (2 : ZMod 299903536643) ^ 37487942080 := by rw [pow_add]
          _ = 286990566693 := by rw [fermat_35]; decide
      have fermat_37 : (2 : ZMod 299903536643) ^ 149951768321 = 299903536642 := by
        calc
          (2 : ZMod 299903536643) ^ 149951768321 = (2 : ZMod 299903536643) ^ (74975884160 + 74975884160 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 74975884160 * (2 : ZMod 299903536643) ^ 74975884160) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 299903536642 := by rw [fermat_36]; decide
      have fermat_38 : (2 : ZMod 299903536643) ^ 299903536642 = 1 := by
        calc
          (2 : ZMod 299903536643) ^ 299903536642 = (2 : ZMod 299903536643) ^ (149951768321 + 149951768321) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 149951768321 * (2 : ZMod 299903536643) ^ 149951768321 := by rw [pow_add]
          _ = 1 := by rw [fermat_37]; decide
      simpa using fermat_38
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (149951768321, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (149951768321, 1)] : List FactorBlock).map factorBlockValue).prod = 299903536643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_149951768321) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 299903536643) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 299903536643) ^ 2 = 4 := by
        calc
          (2 : ZMod 299903536643) ^ 2 = (2 : ZMod 299903536643) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 1 * (2 : ZMod 299903536643) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 299903536643) ^ 4 = 16 := by
        calc
          (2 : ZMod 299903536643) ^ 4 = (2 : ZMod 299903536643) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 2 * (2 : ZMod 299903536643) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 299903536643) ^ 8 = 256 := by
        calc
          (2 : ZMod 299903536643) ^ 8 = (2 : ZMod 299903536643) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 4 * (2 : ZMod 299903536643) ^ 4 := by rw [pow_add]
          _ = 256 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 299903536643) ^ 17 = 131072 := by
        calc
          (2 : ZMod 299903536643) ^ 17 = (2 : ZMod 299903536643) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 8 * (2 : ZMod 299903536643) ^ 8) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 131072 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 299903536643) ^ 34 = 17179869184 := by
        calc
          (2 : ZMod 299903536643) ^ 34 = (2 : ZMod 299903536643) ^ (17 + 17) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 17 * (2 : ZMod 299903536643) ^ 17 := by rw [pow_add]
          _ = 17179869184 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 299903536643) ^ 69 = 194444704056 := by
        calc
          (2 : ZMod 299903536643) ^ 69 = (2 : ZMod 299903536643) ^ (34 + 34 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 34 * (2 : ZMod 299903536643) ^ 34) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 194444704056 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 299903536643) ^ 139 = 173936475234 := by
        calc
          (2 : ZMod 299903536643) ^ 139 = (2 : ZMod 299903536643) ^ (69 + 69 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 69 * (2 : ZMod 299903536643) ^ 69) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 173936475234 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 299903536643) ^ 279 = 69906125016 := by
        calc
          (2 : ZMod 299903536643) ^ 279 = (2 : ZMod 299903536643) ^ (139 + 139 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 139 * (2 : ZMod 299903536643) ^ 139) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 69906125016 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 299903536643) ^ 558 = 72294708844 := by
        calc
          (2 : ZMod 299903536643) ^ 558 = (2 : ZMod 299903536643) ^ (279 + 279) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 279 * (2 : ZMod 299903536643) ^ 279 := by rw [pow_add]
          _ = 72294708844 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 299903536643) ^ 1117 = 107658454836 := by
        calc
          (2 : ZMod 299903536643) ^ 1117 = (2 : ZMod 299903536643) ^ (558 + 558 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 558 * (2 : ZMod 299903536643) ^ 558) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 107658454836 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 299903536643) ^ 2234 = 178496741821 := by
        calc
          (2 : ZMod 299903536643) ^ 2234 = (2 : ZMod 299903536643) ^ (1117 + 1117) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 1117 * (2 : ZMod 299903536643) ^ 1117 := by rw [pow_add]
          _ = 178496741821 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 299903536643) ^ 4468 = 199122196544 := by
        calc
          (2 : ZMod 299903536643) ^ 4468 = (2 : ZMod 299903536643) ^ (2234 + 2234) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 2234 * (2 : ZMod 299903536643) ^ 2234 := by rw [pow_add]
          _ = 199122196544 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 299903536643) ^ 8937 = 152817537458 := by
        calc
          (2 : ZMod 299903536643) ^ 8937 = (2 : ZMod 299903536643) ^ (4468 + 4468 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 4468 * (2 : ZMod 299903536643) ^ 4468) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 152817537458 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 299903536643) ^ 17875 = 290269217301 := by
        calc
          (2 : ZMod 299903536643) ^ 17875 = (2 : ZMod 299903536643) ^ (8937 + 8937 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 8937 * (2 : ZMod 299903536643) ^ 8937) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 290269217301 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 299903536643) ^ 35751 = 262391810319 := by
        calc
          (2 : ZMod 299903536643) ^ 35751 = (2 : ZMod 299903536643) ^ (17875 + 17875 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 17875 * (2 : ZMod 299903536643) ^ 17875) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 262391810319 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 299903536643) ^ 71502 = 58116726375 := by
        calc
          (2 : ZMod 299903536643) ^ 71502 = (2 : ZMod 299903536643) ^ (35751 + 35751) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 35751 * (2 : ZMod 299903536643) ^ 35751 := by rw [pow_add]
          _ = 58116726375 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 299903536643) ^ 143005 = 42090394614 := by
        calc
          (2 : ZMod 299903536643) ^ 143005 = (2 : ZMod 299903536643) ^ (71502 + 71502 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 71502 * (2 : ZMod 299903536643) ^ 71502) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 42090394614 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 299903536643) ^ 286010 = 290060661972 := by
        calc
          (2 : ZMod 299903536643) ^ 286010 = (2 : ZMod 299903536643) ^ (143005 + 143005) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 143005 * (2 : ZMod 299903536643) ^ 143005 := by rw [pow_add]
          _ = 290060661972 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 299903536643) ^ 572020 = 43918014244 := by
        calc
          (2 : ZMod 299903536643) ^ 572020 = (2 : ZMod 299903536643) ^ (286010 + 286010) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 286010 * (2 : ZMod 299903536643) ^ 286010 := by rw [pow_add]
          _ = 43918014244 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 299903536643) ^ 1144041 = 32158998770 := by
        calc
          (2 : ZMod 299903536643) ^ 1144041 = (2 : ZMod 299903536643) ^ (572020 + 572020 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 572020 * (2 : ZMod 299903536643) ^ 572020) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 32158998770 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 299903536643) ^ 2288082 = 182660578876 := by
        calc
          (2 : ZMod 299903536643) ^ 2288082 = (2 : ZMod 299903536643) ^ (1144041 + 1144041) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 1144041 * (2 : ZMod 299903536643) ^ 1144041 := by rw [pow_add]
          _ = 182660578876 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 299903536643) ^ 4576164 = 160685368270 := by
        calc
          (2 : ZMod 299903536643) ^ 4576164 = (2 : ZMod 299903536643) ^ (2288082 + 2288082) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 2288082 * (2 : ZMod 299903536643) ^ 2288082 := by rw [pow_add]
          _ = 160685368270 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 299903536643) ^ 9152329 = 186854248007 := by
        calc
          (2 : ZMod 299903536643) ^ 9152329 = (2 : ZMod 299903536643) ^ (4576164 + 4576164 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 4576164 * (2 : ZMod 299903536643) ^ 4576164) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 186854248007 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 299903536643) ^ 18304659 = 78574823404 := by
        calc
          (2 : ZMod 299903536643) ^ 18304659 = (2 : ZMod 299903536643) ^ (9152329 + 9152329 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 9152329 * (2 : ZMod 299903536643) ^ 9152329) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 78574823404 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 299903536643) ^ 36609318 = 121507255774 := by
        calc
          (2 : ZMod 299903536643) ^ 36609318 = (2 : ZMod 299903536643) ^ (18304659 + 18304659) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 18304659 * (2 : ZMod 299903536643) ^ 18304659 := by rw [pow_add]
          _ = 121507255774 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 299903536643) ^ 73218636 = 72264985114 := by
        calc
          (2 : ZMod 299903536643) ^ 73218636 = (2 : ZMod 299903536643) ^ (36609318 + 36609318) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 36609318 * (2 : ZMod 299903536643) ^ 36609318 := by rw [pow_add]
          _ = 72264985114 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 299903536643) ^ 146437273 = 235340118785 := by
        calc
          (2 : ZMod 299903536643) ^ 146437273 = (2 : ZMod 299903536643) ^ (73218636 + 73218636 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 73218636 * (2 : ZMod 299903536643) ^ 73218636) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 235340118785 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 299903536643) ^ 292874547 = 289230605810 := by
        calc
          (2 : ZMod 299903536643) ^ 292874547 = (2 : ZMod 299903536643) ^ (146437273 + 146437273 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 146437273 * (2 : ZMod 299903536643) ^ 146437273) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 289230605810 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 299903536643) ^ 585749095 = 101793604500 := by
        calc
          (2 : ZMod 299903536643) ^ 585749095 = (2 : ZMod 299903536643) ^ (292874547 + 292874547 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 292874547 * (2 : ZMod 299903536643) ^ 292874547) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 101793604500 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 299903536643) ^ 1171498190 = 165207247470 := by
        calc
          (2 : ZMod 299903536643) ^ 1171498190 = (2 : ZMod 299903536643) ^ (585749095 + 585749095) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 585749095 * (2 : ZMod 299903536643) ^ 585749095 := by rw [pow_add]
          _ = 165207247470 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 299903536643) ^ 2342996380 = 237565914284 := by
        calc
          (2 : ZMod 299903536643) ^ 2342996380 = (2 : ZMod 299903536643) ^ (1171498190 + 1171498190) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 1171498190 * (2 : ZMod 299903536643) ^ 1171498190 := by rw [pow_add]
          _ = 237565914284 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 299903536643) ^ 4685992760 = 294366171058 := by
        calc
          (2 : ZMod 299903536643) ^ 4685992760 = (2 : ZMod 299903536643) ^ (2342996380 + 2342996380) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 2342996380 * (2 : ZMod 299903536643) ^ 2342996380 := by rw [pow_add]
          _ = 294366171058 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 299903536643) ^ 9371985520 = 225562384306 := by
        calc
          (2 : ZMod 299903536643) ^ 9371985520 = (2 : ZMod 299903536643) ^ (4685992760 + 4685992760) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 4685992760 * (2 : ZMod 299903536643) ^ 4685992760 := by rw [pow_add]
          _ = 225562384306 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 299903536643) ^ 18743971040 = 168745382925 := by
        calc
          (2 : ZMod 299903536643) ^ 18743971040 = (2 : ZMod 299903536643) ^ (9371985520 + 9371985520) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 9371985520 * (2 : ZMod 299903536643) ^ 9371985520 := by rw [pow_add]
          _ = 168745382925 := by rw [factor_0_33]; decide
      have factor_0_35 : (2 : ZMod 299903536643) ^ 37487942080 = 78783416894 := by
        calc
          (2 : ZMod 299903536643) ^ 37487942080 = (2 : ZMod 299903536643) ^ (18743971040 + 18743971040) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 18743971040 * (2 : ZMod 299903536643) ^ 18743971040 := by rw [pow_add]
          _ = 78783416894 := by rw [factor_0_34]; decide
      have factor_0_36 : (2 : ZMod 299903536643) ^ 74975884160 = 286990566693 := by
        calc
          (2 : ZMod 299903536643) ^ 74975884160 = (2 : ZMod 299903536643) ^ (37487942080 + 37487942080) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 37487942080 * (2 : ZMod 299903536643) ^ 37487942080 := by rw [pow_add]
          _ = 286990566693 := by rw [factor_0_35]; decide
      have factor_0_37 : (2 : ZMod 299903536643) ^ 149951768321 = 299903536642 := by
        calc
          (2 : ZMod 299903536643) ^ 149951768321 = (2 : ZMod 299903536643) ^ (74975884160 + 74975884160 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = ((2 : ZMod 299903536643) ^ 74975884160 * (2 : ZMod 299903536643) ^ 74975884160) * (2 : ZMod 299903536643) := by rw [pow_succ, pow_add]
          _ = 299903536642 := by rw [factor_0_36]; decide
      change (2 : ZMod 299903536643) ^ 149951768321 ≠ 1
      rw [factor_0_37]
      decide
    ·
      have factor_1_0 : (2 : ZMod 299903536643) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 299903536643) ^ 2 = 4 := by
        calc
          (2 : ZMod 299903536643) ^ 2 = (2 : ZMod 299903536643) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 299903536643) ^ n) (by norm_num)
          _ = (2 : ZMod 299903536643) ^ 1 * (2 : ZMod 299903536643) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      change (2 : ZMod 299903536643) ^ 2 ≠ 1
      rw [factor_1_1]
      decide

#print axioms prime_lucas_299903536643

end TotientTailPeriodKiller
end Erdos249257
