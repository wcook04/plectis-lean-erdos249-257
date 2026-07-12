import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=43 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_245720062183 : Nat.Prime 245720062183 := by
  apply lucas_primality 245720062183 (3 : ZMod 245720062183)
  ·
      have fermat_0 : (3 : ZMod 245720062183) ^ 1 = 3 := by norm_num
      have fermat_1 : (3 : ZMod 245720062183) ^ 3 = 27 := by
        calc
          (3 : ZMod 245720062183) ^ 3 = (3 : ZMod 245720062183) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 1 * (3 : ZMod 245720062183) ^ 1) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [fermat_0]; decide
      have fermat_2 : (3 : ZMod 245720062183) ^ 7 = 2187 := by
        calc
          (3 : ZMod 245720062183) ^ 7 = (3 : ZMod 245720062183) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 3 * (3 : ZMod 245720062183) ^ 3) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [fermat_1]; decide
      have fermat_3 : (3 : ZMod 245720062183) ^ 14 = 4782969 := by
        calc
          (3 : ZMod 245720062183) ^ 14 = (3 : ZMod 245720062183) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 7 * (3 : ZMod 245720062183) ^ 7 := by rw [pow_add]
          _ = 4782969 := by rw [fermat_2]; decide
      have fermat_4 : (3 : ZMod 245720062183) ^ 28 = 24826671942 := by
        calc
          (3 : ZMod 245720062183) ^ 28 = (3 : ZMod 245720062183) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 14 * (3 : ZMod 245720062183) ^ 14 := by rw [pow_add]
          _ = 24826671942 := by rw [fermat_3]; decide
      have fermat_5 : (3 : ZMod 245720062183) ^ 57 = 218786994962 := by
        calc
          (3 : ZMod 245720062183) ^ 57 = (3 : ZMod 245720062183) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 28 * (3 : ZMod 245720062183) ^ 28) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 218786994962 := by rw [fermat_4]; decide
      have fermat_6 : (3 : ZMod 245720062183) ^ 114 = 116772064708 := by
        calc
          (3 : ZMod 245720062183) ^ 114 = (3 : ZMod 245720062183) ^ (57 + 57) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 57 * (3 : ZMod 245720062183) ^ 57 := by rw [pow_add]
          _ = 116772064708 := by rw [fermat_5]; decide
      have fermat_7 : (3 : ZMod 245720062183) ^ 228 = 16605534537 := by
        calc
          (3 : ZMod 245720062183) ^ 228 = (3 : ZMod 245720062183) ^ (114 + 114) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 114 * (3 : ZMod 245720062183) ^ 114 := by rw [pow_add]
          _ = 16605534537 := by rw [fermat_6]; decide
      have fermat_8 : (3 : ZMod 245720062183) ^ 457 = 218579181839 := by
        calc
          (3 : ZMod 245720062183) ^ 457 = (3 : ZMod 245720062183) ^ (228 + 228 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 228 * (3 : ZMod 245720062183) ^ 228) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 218579181839 := by rw [fermat_7]; decide
      have fermat_9 : (3 : ZMod 245720062183) ^ 915 = 19315348884 := by
        calc
          (3 : ZMod 245720062183) ^ 915 = (3 : ZMod 245720062183) ^ (457 + 457 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 457 * (3 : ZMod 245720062183) ^ 457) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 19315348884 := by rw [fermat_8]; decide
      have fermat_10 : (3 : ZMod 245720062183) ^ 1830 = 170169985653 := by
        calc
          (3 : ZMod 245720062183) ^ 1830 = (3 : ZMod 245720062183) ^ (915 + 915) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 915 * (3 : ZMod 245720062183) ^ 915 := by rw [pow_add]
          _ = 170169985653 := by rw [fermat_9]; decide
      have fermat_11 : (3 : ZMod 245720062183) ^ 3661 = 28593781571 := by
        calc
          (3 : ZMod 245720062183) ^ 3661 = (3 : ZMod 245720062183) ^ (1830 + 1830 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 1830 * (3 : ZMod 245720062183) ^ 1830) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 28593781571 := by rw [fermat_10]; decide
      have fermat_12 : (3 : ZMod 245720062183) ^ 7323 = 2200068175 := by
        calc
          (3 : ZMod 245720062183) ^ 7323 = (3 : ZMod 245720062183) ^ (3661 + 3661 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 3661 * (3 : ZMod 245720062183) ^ 3661) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 2200068175 := by rw [fermat_11]; decide
      have fermat_13 : (3 : ZMod 245720062183) ^ 14646 = 38700233569 := by
        calc
          (3 : ZMod 245720062183) ^ 14646 = (3 : ZMod 245720062183) ^ (7323 + 7323) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 7323 * (3 : ZMod 245720062183) ^ 7323 := by rw [pow_add]
          _ = 38700233569 := by rw [fermat_12]; decide
      have fermat_14 : (3 : ZMod 245720062183) ^ 29292 = 139798939972 := by
        calc
          (3 : ZMod 245720062183) ^ 29292 = (3 : ZMod 245720062183) ^ (14646 + 14646) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 14646 * (3 : ZMod 245720062183) ^ 14646 := by rw [pow_add]
          _ = 139798939972 := by rw [fermat_13]; decide
      have fermat_15 : (3 : ZMod 245720062183) ^ 58584 = 122555423200 := by
        calc
          (3 : ZMod 245720062183) ^ 58584 = (3 : ZMod 245720062183) ^ (29292 + 29292) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 29292 * (3 : ZMod 245720062183) ^ 29292 := by rw [pow_add]
          _ = 122555423200 := by rw [fermat_14]; decide
      have fermat_16 : (3 : ZMod 245720062183) ^ 117168 = 167753293054 := by
        calc
          (3 : ZMod 245720062183) ^ 117168 = (3 : ZMod 245720062183) ^ (58584 + 58584) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 58584 * (3 : ZMod 245720062183) ^ 58584 := by rw [pow_add]
          _ = 167753293054 := by rw [fermat_15]; decide
      have fermat_17 : (3 : ZMod 245720062183) ^ 234336 = 23790815571 := by
        calc
          (3 : ZMod 245720062183) ^ 234336 = (3 : ZMod 245720062183) ^ (117168 + 117168) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 117168 * (3 : ZMod 245720062183) ^ 117168 := by rw [pow_add]
          _ = 23790815571 := by rw [fermat_16]; decide
      have fermat_18 : (3 : ZMod 245720062183) ^ 468673 = 116531857235 := by
        calc
          (3 : ZMod 245720062183) ^ 468673 = (3 : ZMod 245720062183) ^ (234336 + 234336 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 234336 * (3 : ZMod 245720062183) ^ 234336) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 116531857235 := by rw [fermat_17]; decide
      have fermat_19 : (3 : ZMod 245720062183) ^ 937347 = 218393180712 := by
        calc
          (3 : ZMod 245720062183) ^ 937347 = (3 : ZMod 245720062183) ^ (468673 + 468673 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 468673 * (3 : ZMod 245720062183) ^ 468673) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 218393180712 := by rw [fermat_18]; decide
      have fermat_20 : (3 : ZMod 245720062183) ^ 1874695 = 179992379375 := by
        calc
          (3 : ZMod 245720062183) ^ 1874695 = (3 : ZMod 245720062183) ^ (937347 + 937347 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 937347 * (3 : ZMod 245720062183) ^ 937347) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 179992379375 := by rw [fermat_19]; decide
      have fermat_21 : (3 : ZMod 245720062183) ^ 3749390 = 197667697806 := by
        calc
          (3 : ZMod 245720062183) ^ 3749390 = (3 : ZMod 245720062183) ^ (1874695 + 1874695) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 1874695 * (3 : ZMod 245720062183) ^ 1874695 := by rw [pow_add]
          _ = 197667697806 := by rw [fermat_20]; decide
      have fermat_22 : (3 : ZMod 245720062183) ^ 7498781 = 213315081493 := by
        calc
          (3 : ZMod 245720062183) ^ 7498781 = (3 : ZMod 245720062183) ^ (3749390 + 3749390 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 3749390 * (3 : ZMod 245720062183) ^ 3749390) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 213315081493 := by rw [fermat_21]; decide
      have fermat_23 : (3 : ZMod 245720062183) ^ 14997562 = 219466346389 := by
        calc
          (3 : ZMod 245720062183) ^ 14997562 = (3 : ZMod 245720062183) ^ (7498781 + 7498781) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 7498781 * (3 : ZMod 245720062183) ^ 7498781 := by rw [pow_add]
          _ = 219466346389 := by rw [fermat_22]; decide
      have fermat_24 : (3 : ZMod 245720062183) ^ 29995124 = 90326149875 := by
        calc
          (3 : ZMod 245720062183) ^ 29995124 = (3 : ZMod 245720062183) ^ (14997562 + 14997562) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 14997562 * (3 : ZMod 245720062183) ^ 14997562 := by rw [pow_add]
          _ = 90326149875 := by rw [fermat_23]; decide
      have fermat_25 : (3 : ZMod 245720062183) ^ 59990249 = 1121605601 := by
        calc
          (3 : ZMod 245720062183) ^ 59990249 = (3 : ZMod 245720062183) ^ (29995124 + 29995124 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 29995124 * (3 : ZMod 245720062183) ^ 29995124) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 1121605601 := by rw [fermat_24]; decide
      have fermat_26 : (3 : ZMod 245720062183) ^ 119980499 = 137919369413 := by
        calc
          (3 : ZMod 245720062183) ^ 119980499 = (3 : ZMod 245720062183) ^ (59990249 + 59990249 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 59990249 * (3 : ZMod 245720062183) ^ 59990249) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 137919369413 := by rw [fermat_25]; decide
      have fermat_27 : (3 : ZMod 245720062183) ^ 239960998 = 88515005242 := by
        calc
          (3 : ZMod 245720062183) ^ 239960998 = (3 : ZMod 245720062183) ^ (119980499 + 119980499) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 119980499 * (3 : ZMod 245720062183) ^ 119980499 := by rw [pow_add]
          _ = 88515005242 := by rw [fermat_26]; decide
      have fermat_28 : (3 : ZMod 245720062183) ^ 479921996 = 7586143207 := by
        calc
          (3 : ZMod 245720062183) ^ 479921996 = (3 : ZMod 245720062183) ^ (239960998 + 239960998) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 239960998 * (3 : ZMod 245720062183) ^ 239960998 := by rw [pow_add]
          _ = 7586143207 := by rw [fermat_27]; decide
      have fermat_29 : (3 : ZMod 245720062183) ^ 959843992 = 62765197384 := by
        calc
          (3 : ZMod 245720062183) ^ 959843992 = (3 : ZMod 245720062183) ^ (479921996 + 479921996) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 479921996 * (3 : ZMod 245720062183) ^ 479921996 := by rw [pow_add]
          _ = 62765197384 := by rw [fermat_28]; decide
      have fermat_30 : (3 : ZMod 245720062183) ^ 1919687985 = 238288789620 := by
        calc
          (3 : ZMod 245720062183) ^ 1919687985 = (3 : ZMod 245720062183) ^ (959843992 + 959843992 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 959843992 * (3 : ZMod 245720062183) ^ 959843992) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 238288789620 := by rw [fermat_29]; decide
      have fermat_31 : (3 : ZMod 245720062183) ^ 3839375971 = 189167408295 := by
        calc
          (3 : ZMod 245720062183) ^ 3839375971 = (3 : ZMod 245720062183) ^ (1919687985 + 1919687985 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 1919687985 * (3 : ZMod 245720062183) ^ 1919687985) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 189167408295 := by rw [fermat_30]; decide
      have fermat_32 : (3 : ZMod 245720062183) ^ 7678751943 = 226935637614 := by
        calc
          (3 : ZMod 245720062183) ^ 7678751943 = (3 : ZMod 245720062183) ^ (3839375971 + 3839375971 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 3839375971 * (3 : ZMod 245720062183) ^ 3839375971) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 226935637614 := by rw [fermat_31]; decide
      have fermat_33 : (3 : ZMod 245720062183) ^ 15357503886 = 239631793254 := by
        calc
          (3 : ZMod 245720062183) ^ 15357503886 = (3 : ZMod 245720062183) ^ (7678751943 + 7678751943) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 7678751943 * (3 : ZMod 245720062183) ^ 7678751943 := by rw [pow_add]
          _ = 239631793254 := by rw [fermat_32]; decide
      have fermat_34 : (3 : ZMod 245720062183) ^ 30715007772 = 230924071607 := by
        calc
          (3 : ZMod 245720062183) ^ 30715007772 = (3 : ZMod 245720062183) ^ (15357503886 + 15357503886) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 15357503886 * (3 : ZMod 245720062183) ^ 15357503886 := by rw [pow_add]
          _ = 230924071607 := by rw [fermat_33]; decide
      have fermat_35 : (3 : ZMod 245720062183) ^ 61430015545 = 149052271563 := by
        calc
          (3 : ZMod 245720062183) ^ 61430015545 = (3 : ZMod 245720062183) ^ (30715007772 + 30715007772 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 30715007772 * (3 : ZMod 245720062183) ^ 30715007772) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 149052271563 := by rw [fermat_34]; decide
      have fermat_36 : (3 : ZMod 245720062183) ^ 122860031091 = 245720062182 := by
        calc
          (3 : ZMod 245720062183) ^ 122860031091 = (3 : ZMod 245720062183) ^ (61430015545 + 61430015545 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 61430015545 * (3 : ZMod 245720062183) ^ 61430015545) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 245720062182 := by rw [fermat_35]; decide
      have fermat_37 : (3 : ZMod 245720062183) ^ 245720062182 = 1 := by
        calc
          (3 : ZMod 245720062183) ^ 245720062182 = (3 : ZMod 245720062183) ^ (122860031091 + 122860031091) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 122860031091 * (3 : ZMod 245720062183) ^ 122860031091 := by rw [pow_add]
          _ = 1 := by rw [fermat_36]; decide
      simpa using fermat_37
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (30223, 1), (193577, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (30223, 1), (193577, 1)] : List FactorBlock).map factorBlockValue).prod = 245720062183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (3 : ZMod 245720062183) ^ 1 = 3 := by norm_num
      have factor_0_1 : (3 : ZMod 245720062183) ^ 3 = 27 := by
        calc
          (3 : ZMod 245720062183) ^ 3 = (3 : ZMod 245720062183) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 1 * (3 : ZMod 245720062183) ^ 1) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_0_0]; decide
      have factor_0_2 : (3 : ZMod 245720062183) ^ 7 = 2187 := by
        calc
          (3 : ZMod 245720062183) ^ 7 = (3 : ZMod 245720062183) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 3 * (3 : ZMod 245720062183) ^ 3) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_0_1]; decide
      have factor_0_3 : (3 : ZMod 245720062183) ^ 14 = 4782969 := by
        calc
          (3 : ZMod 245720062183) ^ 14 = (3 : ZMod 245720062183) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 7 * (3 : ZMod 245720062183) ^ 7 := by rw [pow_add]
          _ = 4782969 := by rw [factor_0_2]; decide
      have factor_0_4 : (3 : ZMod 245720062183) ^ 28 = 24826671942 := by
        calc
          (3 : ZMod 245720062183) ^ 28 = (3 : ZMod 245720062183) ^ (14 + 14) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 14 * (3 : ZMod 245720062183) ^ 14 := by rw [pow_add]
          _ = 24826671942 := by rw [factor_0_3]; decide
      have factor_0_5 : (3 : ZMod 245720062183) ^ 57 = 218786994962 := by
        calc
          (3 : ZMod 245720062183) ^ 57 = (3 : ZMod 245720062183) ^ (28 + 28 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 28 * (3 : ZMod 245720062183) ^ 28) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 218786994962 := by rw [factor_0_4]; decide
      have factor_0_6 : (3 : ZMod 245720062183) ^ 114 = 116772064708 := by
        calc
          (3 : ZMod 245720062183) ^ 114 = (3 : ZMod 245720062183) ^ (57 + 57) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 57 * (3 : ZMod 245720062183) ^ 57 := by rw [pow_add]
          _ = 116772064708 := by rw [factor_0_5]; decide
      have factor_0_7 : (3 : ZMod 245720062183) ^ 228 = 16605534537 := by
        calc
          (3 : ZMod 245720062183) ^ 228 = (3 : ZMod 245720062183) ^ (114 + 114) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 114 * (3 : ZMod 245720062183) ^ 114 := by rw [pow_add]
          _ = 16605534537 := by rw [factor_0_6]; decide
      have factor_0_8 : (3 : ZMod 245720062183) ^ 457 = 218579181839 := by
        calc
          (3 : ZMod 245720062183) ^ 457 = (3 : ZMod 245720062183) ^ (228 + 228 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 228 * (3 : ZMod 245720062183) ^ 228) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 218579181839 := by rw [factor_0_7]; decide
      have factor_0_9 : (3 : ZMod 245720062183) ^ 915 = 19315348884 := by
        calc
          (3 : ZMod 245720062183) ^ 915 = (3 : ZMod 245720062183) ^ (457 + 457 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 457 * (3 : ZMod 245720062183) ^ 457) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 19315348884 := by rw [factor_0_8]; decide
      have factor_0_10 : (3 : ZMod 245720062183) ^ 1830 = 170169985653 := by
        calc
          (3 : ZMod 245720062183) ^ 1830 = (3 : ZMod 245720062183) ^ (915 + 915) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 915 * (3 : ZMod 245720062183) ^ 915 := by rw [pow_add]
          _ = 170169985653 := by rw [factor_0_9]; decide
      have factor_0_11 : (3 : ZMod 245720062183) ^ 3661 = 28593781571 := by
        calc
          (3 : ZMod 245720062183) ^ 3661 = (3 : ZMod 245720062183) ^ (1830 + 1830 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 1830 * (3 : ZMod 245720062183) ^ 1830) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 28593781571 := by rw [factor_0_10]; decide
      have factor_0_12 : (3 : ZMod 245720062183) ^ 7323 = 2200068175 := by
        calc
          (3 : ZMod 245720062183) ^ 7323 = (3 : ZMod 245720062183) ^ (3661 + 3661 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 3661 * (3 : ZMod 245720062183) ^ 3661) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 2200068175 := by rw [factor_0_11]; decide
      have factor_0_13 : (3 : ZMod 245720062183) ^ 14646 = 38700233569 := by
        calc
          (3 : ZMod 245720062183) ^ 14646 = (3 : ZMod 245720062183) ^ (7323 + 7323) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 7323 * (3 : ZMod 245720062183) ^ 7323 := by rw [pow_add]
          _ = 38700233569 := by rw [factor_0_12]; decide
      have factor_0_14 : (3 : ZMod 245720062183) ^ 29292 = 139798939972 := by
        calc
          (3 : ZMod 245720062183) ^ 29292 = (3 : ZMod 245720062183) ^ (14646 + 14646) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 14646 * (3 : ZMod 245720062183) ^ 14646 := by rw [pow_add]
          _ = 139798939972 := by rw [factor_0_13]; decide
      have factor_0_15 : (3 : ZMod 245720062183) ^ 58584 = 122555423200 := by
        calc
          (3 : ZMod 245720062183) ^ 58584 = (3 : ZMod 245720062183) ^ (29292 + 29292) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 29292 * (3 : ZMod 245720062183) ^ 29292 := by rw [pow_add]
          _ = 122555423200 := by rw [factor_0_14]; decide
      have factor_0_16 : (3 : ZMod 245720062183) ^ 117168 = 167753293054 := by
        calc
          (3 : ZMod 245720062183) ^ 117168 = (3 : ZMod 245720062183) ^ (58584 + 58584) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 58584 * (3 : ZMod 245720062183) ^ 58584 := by rw [pow_add]
          _ = 167753293054 := by rw [factor_0_15]; decide
      have factor_0_17 : (3 : ZMod 245720062183) ^ 234336 = 23790815571 := by
        calc
          (3 : ZMod 245720062183) ^ 234336 = (3 : ZMod 245720062183) ^ (117168 + 117168) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 117168 * (3 : ZMod 245720062183) ^ 117168 := by rw [pow_add]
          _ = 23790815571 := by rw [factor_0_16]; decide
      have factor_0_18 : (3 : ZMod 245720062183) ^ 468673 = 116531857235 := by
        calc
          (3 : ZMod 245720062183) ^ 468673 = (3 : ZMod 245720062183) ^ (234336 + 234336 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 234336 * (3 : ZMod 245720062183) ^ 234336) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 116531857235 := by rw [factor_0_17]; decide
      have factor_0_19 : (3 : ZMod 245720062183) ^ 937347 = 218393180712 := by
        calc
          (3 : ZMod 245720062183) ^ 937347 = (3 : ZMod 245720062183) ^ (468673 + 468673 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 468673 * (3 : ZMod 245720062183) ^ 468673) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 218393180712 := by rw [factor_0_18]; decide
      have factor_0_20 : (3 : ZMod 245720062183) ^ 1874695 = 179992379375 := by
        calc
          (3 : ZMod 245720062183) ^ 1874695 = (3 : ZMod 245720062183) ^ (937347 + 937347 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 937347 * (3 : ZMod 245720062183) ^ 937347) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 179992379375 := by rw [factor_0_19]; decide
      have factor_0_21 : (3 : ZMod 245720062183) ^ 3749390 = 197667697806 := by
        calc
          (3 : ZMod 245720062183) ^ 3749390 = (3 : ZMod 245720062183) ^ (1874695 + 1874695) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 1874695 * (3 : ZMod 245720062183) ^ 1874695 := by rw [pow_add]
          _ = 197667697806 := by rw [factor_0_20]; decide
      have factor_0_22 : (3 : ZMod 245720062183) ^ 7498781 = 213315081493 := by
        calc
          (3 : ZMod 245720062183) ^ 7498781 = (3 : ZMod 245720062183) ^ (3749390 + 3749390 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 3749390 * (3 : ZMod 245720062183) ^ 3749390) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 213315081493 := by rw [factor_0_21]; decide
      have factor_0_23 : (3 : ZMod 245720062183) ^ 14997562 = 219466346389 := by
        calc
          (3 : ZMod 245720062183) ^ 14997562 = (3 : ZMod 245720062183) ^ (7498781 + 7498781) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 7498781 * (3 : ZMod 245720062183) ^ 7498781 := by rw [pow_add]
          _ = 219466346389 := by rw [factor_0_22]; decide
      have factor_0_24 : (3 : ZMod 245720062183) ^ 29995124 = 90326149875 := by
        calc
          (3 : ZMod 245720062183) ^ 29995124 = (3 : ZMod 245720062183) ^ (14997562 + 14997562) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 14997562 * (3 : ZMod 245720062183) ^ 14997562 := by rw [pow_add]
          _ = 90326149875 := by rw [factor_0_23]; decide
      have factor_0_25 : (3 : ZMod 245720062183) ^ 59990249 = 1121605601 := by
        calc
          (3 : ZMod 245720062183) ^ 59990249 = (3 : ZMod 245720062183) ^ (29995124 + 29995124 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 29995124 * (3 : ZMod 245720062183) ^ 29995124) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 1121605601 := by rw [factor_0_24]; decide
      have factor_0_26 : (3 : ZMod 245720062183) ^ 119980499 = 137919369413 := by
        calc
          (3 : ZMod 245720062183) ^ 119980499 = (3 : ZMod 245720062183) ^ (59990249 + 59990249 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 59990249 * (3 : ZMod 245720062183) ^ 59990249) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 137919369413 := by rw [factor_0_25]; decide
      have factor_0_27 : (3 : ZMod 245720062183) ^ 239960998 = 88515005242 := by
        calc
          (3 : ZMod 245720062183) ^ 239960998 = (3 : ZMod 245720062183) ^ (119980499 + 119980499) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 119980499 * (3 : ZMod 245720062183) ^ 119980499 := by rw [pow_add]
          _ = 88515005242 := by rw [factor_0_26]; decide
      have factor_0_28 : (3 : ZMod 245720062183) ^ 479921996 = 7586143207 := by
        calc
          (3 : ZMod 245720062183) ^ 479921996 = (3 : ZMod 245720062183) ^ (239960998 + 239960998) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 239960998 * (3 : ZMod 245720062183) ^ 239960998 := by rw [pow_add]
          _ = 7586143207 := by rw [factor_0_27]; decide
      have factor_0_29 : (3 : ZMod 245720062183) ^ 959843992 = 62765197384 := by
        calc
          (3 : ZMod 245720062183) ^ 959843992 = (3 : ZMod 245720062183) ^ (479921996 + 479921996) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 479921996 * (3 : ZMod 245720062183) ^ 479921996 := by rw [pow_add]
          _ = 62765197384 := by rw [factor_0_28]; decide
      have factor_0_30 : (3 : ZMod 245720062183) ^ 1919687985 = 238288789620 := by
        calc
          (3 : ZMod 245720062183) ^ 1919687985 = (3 : ZMod 245720062183) ^ (959843992 + 959843992 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 959843992 * (3 : ZMod 245720062183) ^ 959843992) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 238288789620 := by rw [factor_0_29]; decide
      have factor_0_31 : (3 : ZMod 245720062183) ^ 3839375971 = 189167408295 := by
        calc
          (3 : ZMod 245720062183) ^ 3839375971 = (3 : ZMod 245720062183) ^ (1919687985 + 1919687985 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 1919687985 * (3 : ZMod 245720062183) ^ 1919687985) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 189167408295 := by rw [factor_0_30]; decide
      have factor_0_32 : (3 : ZMod 245720062183) ^ 7678751943 = 226935637614 := by
        calc
          (3 : ZMod 245720062183) ^ 7678751943 = (3 : ZMod 245720062183) ^ (3839375971 + 3839375971 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 3839375971 * (3 : ZMod 245720062183) ^ 3839375971) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 226935637614 := by rw [factor_0_31]; decide
      have factor_0_33 : (3 : ZMod 245720062183) ^ 15357503886 = 239631793254 := by
        calc
          (3 : ZMod 245720062183) ^ 15357503886 = (3 : ZMod 245720062183) ^ (7678751943 + 7678751943) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 7678751943 * (3 : ZMod 245720062183) ^ 7678751943 := by rw [pow_add]
          _ = 239631793254 := by rw [factor_0_32]; decide
      have factor_0_34 : (3 : ZMod 245720062183) ^ 30715007772 = 230924071607 := by
        calc
          (3 : ZMod 245720062183) ^ 30715007772 = (3 : ZMod 245720062183) ^ (15357503886 + 15357503886) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 15357503886 * (3 : ZMod 245720062183) ^ 15357503886 := by rw [pow_add]
          _ = 230924071607 := by rw [factor_0_33]; decide
      have factor_0_35 : (3 : ZMod 245720062183) ^ 61430015545 = 149052271563 := by
        calc
          (3 : ZMod 245720062183) ^ 61430015545 = (3 : ZMod 245720062183) ^ (30715007772 + 30715007772 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 30715007772 * (3 : ZMod 245720062183) ^ 30715007772) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 149052271563 := by rw [factor_0_34]; decide
      have factor_0_36 : (3 : ZMod 245720062183) ^ 122860031091 = 245720062182 := by
        calc
          (3 : ZMod 245720062183) ^ 122860031091 = (3 : ZMod 245720062183) ^ (61430015545 + 61430015545 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 61430015545 * (3 : ZMod 245720062183) ^ 61430015545) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 245720062182 := by rw [factor_0_35]; decide
      change (3 : ZMod 245720062183) ^ 122860031091 ≠ 1
      rw [factor_0_36]
      decide
    ·
      have factor_1_0 : (3 : ZMod 245720062183) ^ 1 = 3 := by norm_num
      have factor_1_1 : (3 : ZMod 245720062183) ^ 2 = 9 := by
        calc
          (3 : ZMod 245720062183) ^ 2 = (3 : ZMod 245720062183) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 1 * (3 : ZMod 245720062183) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_1_0]; decide
      have factor_1_2 : (3 : ZMod 245720062183) ^ 4 = 81 := by
        calc
          (3 : ZMod 245720062183) ^ 4 = (3 : ZMod 245720062183) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 2 * (3 : ZMod 245720062183) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_1_1]; decide
      have factor_1_3 : (3 : ZMod 245720062183) ^ 9 = 19683 := by
        calc
          (3 : ZMod 245720062183) ^ 9 = (3 : ZMod 245720062183) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 4 * (3 : ZMod 245720062183) ^ 4) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_1_2]; decide
      have factor_1_4 : (3 : ZMod 245720062183) ^ 19 = 1162261467 := by
        calc
          (3 : ZMod 245720062183) ^ 19 = (3 : ZMod 245720062183) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 9 * (3 : ZMod 245720062183) ^ 9) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 1162261467 := by rw [factor_1_3]; decide
      have factor_1_5 : (3 : ZMod 245720062183) ^ 38 = 24260519380 := by
        calc
          (3 : ZMod 245720062183) ^ 38 = (3 : ZMod 245720062183) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 19 * (3 : ZMod 245720062183) ^ 19 := by rw [pow_add]
          _ = 24260519380 := by rw [factor_1_4]; decide
      have factor_1_6 : (3 : ZMod 245720062183) ^ 76 = 51333210270 := by
        calc
          (3 : ZMod 245720062183) ^ 76 = (3 : ZMod 245720062183) ^ (38 + 38) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 38 * (3 : ZMod 245720062183) ^ 38 := by rw [pow_add]
          _ = 51333210270 := by rw [factor_1_5]; decide
      have factor_1_7 : (3 : ZMod 245720062183) ^ 152 = 77979683409 := by
        calc
          (3 : ZMod 245720062183) ^ 152 = (3 : ZMod 245720062183) ^ (76 + 76) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 76 * (3 : ZMod 245720062183) ^ 76 := by rw [pow_add]
          _ = 77979683409 := by rw [factor_1_6]; decide
      have factor_1_8 : (3 : ZMod 245720062183) ^ 305 = 149213164242 := by
        calc
          (3 : ZMod 245720062183) ^ 305 = (3 : ZMod 245720062183) ^ (152 + 152 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 152 * (3 : ZMod 245720062183) ^ 152) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 149213164242 := by rw [factor_1_7]; decide
      have factor_1_9 : (3 : ZMod 245720062183) ^ 610 = 183957801292 := by
        calc
          (3 : ZMod 245720062183) ^ 610 = (3 : ZMod 245720062183) ^ (305 + 305) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 305 * (3 : ZMod 245720062183) ^ 305 := by rw [pow_add]
          _ = 183957801292 := by rw [factor_1_8]; decide
      have factor_1_10 : (3 : ZMod 245720062183) ^ 1220 = 195502829030 := by
        calc
          (3 : ZMod 245720062183) ^ 1220 = (3 : ZMod 245720062183) ^ (610 + 610) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 610 * (3 : ZMod 245720062183) ^ 610 := by rw [pow_add]
          _ = 195502829030 := by rw [factor_1_9]; decide
      have factor_1_11 : (3 : ZMod 245720062183) ^ 2441 = 124710438493 := by
        calc
          (3 : ZMod 245720062183) ^ 2441 = (3 : ZMod 245720062183) ^ (1220 + 1220 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 1220 * (3 : ZMod 245720062183) ^ 1220) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 124710438493 := by rw [factor_1_10]; decide
      have factor_1_12 : (3 : ZMod 245720062183) ^ 4882 = 28821574327 := by
        calc
          (3 : ZMod 245720062183) ^ 4882 = (3 : ZMod 245720062183) ^ (2441 + 2441) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 2441 * (3 : ZMod 245720062183) ^ 2441 := by rw [pow_add]
          _ = 28821574327 := by rw [factor_1_11]; decide
      have factor_1_13 : (3 : ZMod 245720062183) ^ 9764 = 140453784679 := by
        calc
          (3 : ZMod 245720062183) ^ 9764 = (3 : ZMod 245720062183) ^ (4882 + 4882) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 4882 * (3 : ZMod 245720062183) ^ 4882 := by rw [pow_add]
          _ = 140453784679 := by rw [factor_1_12]; decide
      have factor_1_14 : (3 : ZMod 245720062183) ^ 19528 = 37663054126 := by
        calc
          (3 : ZMod 245720062183) ^ 19528 = (3 : ZMod 245720062183) ^ (9764 + 9764) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 9764 * (3 : ZMod 245720062183) ^ 9764 := by rw [pow_add]
          _ = 37663054126 := by rw [factor_1_13]; decide
      have factor_1_15 : (3 : ZMod 245720062183) ^ 39056 = 65406016153 := by
        calc
          (3 : ZMod 245720062183) ^ 39056 = (3 : ZMod 245720062183) ^ (19528 + 19528) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 19528 * (3 : ZMod 245720062183) ^ 19528 := by rw [pow_add]
          _ = 65406016153 := by rw [factor_1_14]; decide
      have factor_1_16 : (3 : ZMod 245720062183) ^ 78112 = 39420863134 := by
        calc
          (3 : ZMod 245720062183) ^ 78112 = (3 : ZMod 245720062183) ^ (39056 + 39056) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 39056 * (3 : ZMod 245720062183) ^ 39056 := by rw [pow_add]
          _ = 39420863134 := by rw [factor_1_15]; decide
      have factor_1_17 : (3 : ZMod 245720062183) ^ 156224 = 23277172819 := by
        calc
          (3 : ZMod 245720062183) ^ 156224 = (3 : ZMod 245720062183) ^ (78112 + 78112) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 78112 * (3 : ZMod 245720062183) ^ 78112 := by rw [pow_add]
          _ = 23277172819 := by rw [factor_1_16]; decide
      have factor_1_18 : (3 : ZMod 245720062183) ^ 312449 = 535173377 := by
        calc
          (3 : ZMod 245720062183) ^ 312449 = (3 : ZMod 245720062183) ^ (156224 + 156224 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 156224 * (3 : ZMod 245720062183) ^ 156224) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 535173377 := by rw [factor_1_17]; decide
      have factor_1_19 : (3 : ZMod 245720062183) ^ 624898 = 221849328061 := by
        calc
          (3 : ZMod 245720062183) ^ 624898 = (3 : ZMod 245720062183) ^ (312449 + 312449) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 312449 * (3 : ZMod 245720062183) ^ 312449 := by rw [pow_add]
          _ = 221849328061 := by rw [factor_1_18]; decide
      have factor_1_20 : (3 : ZMod 245720062183) ^ 1249796 = 34976748816 := by
        calc
          (3 : ZMod 245720062183) ^ 1249796 = (3 : ZMod 245720062183) ^ (624898 + 624898) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 624898 * (3 : ZMod 245720062183) ^ 624898 := by rw [pow_add]
          _ = 34976748816 := by rw [factor_1_19]; decide
      have factor_1_21 : (3 : ZMod 245720062183) ^ 2499593 = 12443188373 := by
        calc
          (3 : ZMod 245720062183) ^ 2499593 = (3 : ZMod 245720062183) ^ (1249796 + 1249796 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 1249796 * (3 : ZMod 245720062183) ^ 1249796) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 12443188373 := by rw [factor_1_20]; decide
      have factor_1_22 : (3 : ZMod 245720062183) ^ 4999187 = 48654551019 := by
        calc
          (3 : ZMod 245720062183) ^ 4999187 = (3 : ZMod 245720062183) ^ (2499593 + 2499593 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 2499593 * (3 : ZMod 245720062183) ^ 2499593) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 48654551019 := by rw [factor_1_21]; decide
      have factor_1_23 : (3 : ZMod 245720062183) ^ 9998374 = 156173375478 := by
        calc
          (3 : ZMod 245720062183) ^ 9998374 = (3 : ZMod 245720062183) ^ (4999187 + 4999187) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 4999187 * (3 : ZMod 245720062183) ^ 4999187 := by rw [pow_add]
          _ = 156173375478 := by rw [factor_1_22]; decide
      have factor_1_24 : (3 : ZMod 245720062183) ^ 19996749 = 204059474717 := by
        calc
          (3 : ZMod 245720062183) ^ 19996749 = (3 : ZMod 245720062183) ^ (9998374 + 9998374 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 9998374 * (3 : ZMod 245720062183) ^ 9998374) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 204059474717 := by rw [factor_1_23]; decide
      have factor_1_25 : (3 : ZMod 245720062183) ^ 39993499 = 134740407798 := by
        calc
          (3 : ZMod 245720062183) ^ 39993499 = (3 : ZMod 245720062183) ^ (19996749 + 19996749 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 19996749 * (3 : ZMod 245720062183) ^ 19996749) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 134740407798 := by rw [factor_1_24]; decide
      have factor_1_26 : (3 : ZMod 245720062183) ^ 79986999 = 132381506857 := by
        calc
          (3 : ZMod 245720062183) ^ 79986999 = (3 : ZMod 245720062183) ^ (39993499 + 39993499 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 39993499 * (3 : ZMod 245720062183) ^ 39993499) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 132381506857 := by rw [factor_1_25]; decide
      have factor_1_27 : (3 : ZMod 245720062183) ^ 159973998 = 81474772133 := by
        calc
          (3 : ZMod 245720062183) ^ 159973998 = (3 : ZMod 245720062183) ^ (79986999 + 79986999) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 79986999 * (3 : ZMod 245720062183) ^ 79986999 := by rw [pow_add]
          _ = 81474772133 := by rw [factor_1_26]; decide
      have factor_1_28 : (3 : ZMod 245720062183) ^ 319947997 = 37663174508 := by
        calc
          (3 : ZMod 245720062183) ^ 319947997 = (3 : ZMod 245720062183) ^ (159973998 + 159973998 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 159973998 * (3 : ZMod 245720062183) ^ 159973998) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 37663174508 := by rw [factor_1_27]; decide
      have factor_1_29 : (3 : ZMod 245720062183) ^ 639895995 = 48579960910 := by
        calc
          (3 : ZMod 245720062183) ^ 639895995 = (3 : ZMod 245720062183) ^ (319947997 + 319947997 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 319947997 * (3 : ZMod 245720062183) ^ 319947997) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 48579960910 := by rw [factor_1_28]; decide
      have factor_1_30 : (3 : ZMod 245720062183) ^ 1279791990 = 132475941503 := by
        calc
          (3 : ZMod 245720062183) ^ 1279791990 = (3 : ZMod 245720062183) ^ (639895995 + 639895995) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 639895995 * (3 : ZMod 245720062183) ^ 639895995 := by rw [pow_add]
          _ = 132475941503 := by rw [factor_1_29]; decide
      have factor_1_31 : (3 : ZMod 245720062183) ^ 2559583981 = 164916698984 := by
        calc
          (3 : ZMod 245720062183) ^ 2559583981 = (3 : ZMod 245720062183) ^ (1279791990 + 1279791990 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 1279791990 * (3 : ZMod 245720062183) ^ 1279791990) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 164916698984 := by rw [factor_1_30]; decide
      have factor_1_32 : (3 : ZMod 245720062183) ^ 5119167962 = 35444296227 := by
        calc
          (3 : ZMod 245720062183) ^ 5119167962 = (3 : ZMod 245720062183) ^ (2559583981 + 2559583981) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 2559583981 * (3 : ZMod 245720062183) ^ 2559583981 := by rw [pow_add]
          _ = 35444296227 := by rw [factor_1_31]; decide
      have factor_1_33 : (3 : ZMod 245720062183) ^ 10238335924 = 205553259013 := by
        calc
          (3 : ZMod 245720062183) ^ 10238335924 = (3 : ZMod 245720062183) ^ (5119167962 + 5119167962) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 5119167962 * (3 : ZMod 245720062183) ^ 5119167962 := by rw [pow_add]
          _ = 205553259013 := by rw [factor_1_32]; decide
      have factor_1_34 : (3 : ZMod 245720062183) ^ 20476671848 = 74526135781 := by
        calc
          (3 : ZMod 245720062183) ^ 20476671848 = (3 : ZMod 245720062183) ^ (10238335924 + 10238335924) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 10238335924 * (3 : ZMod 245720062183) ^ 10238335924 := by rw [pow_add]
          _ = 74526135781 := by rw [factor_1_33]; decide
      have factor_1_35 : (3 : ZMod 245720062183) ^ 40953343697 = 22141654839 := by
        calc
          (3 : ZMod 245720062183) ^ 40953343697 = (3 : ZMod 245720062183) ^ (20476671848 + 20476671848 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 20476671848 * (3 : ZMod 245720062183) ^ 20476671848) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 22141654839 := by rw [factor_1_34]; decide
      have factor_1_36 : (3 : ZMod 245720062183) ^ 81906687394 = 22141654838 := by
        calc
          (3 : ZMod 245720062183) ^ 81906687394 = (3 : ZMod 245720062183) ^ (40953343697 + 40953343697) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 40953343697 * (3 : ZMod 245720062183) ^ 40953343697 := by rw [pow_add]
          _ = 22141654838 := by rw [factor_1_35]; decide
      change (3 : ZMod 245720062183) ^ 81906687394 ≠ 1
      rw [factor_1_36]
      decide
    ·
      have factor_2_0 : (3 : ZMod 245720062183) ^ 1 = 3 := by norm_num
      have factor_2_1 : (3 : ZMod 245720062183) ^ 2 = 9 := by
        calc
          (3 : ZMod 245720062183) ^ 2 = (3 : ZMod 245720062183) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 1 * (3 : ZMod 245720062183) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_2_0]; decide
      have factor_2_2 : (3 : ZMod 245720062183) ^ 4 = 81 := by
        calc
          (3 : ZMod 245720062183) ^ 4 = (3 : ZMod 245720062183) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 2 * (3 : ZMod 245720062183) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_2_1]; decide
      have factor_2_3 : (3 : ZMod 245720062183) ^ 8 = 6561 := by
        calc
          (3 : ZMod 245720062183) ^ 8 = (3 : ZMod 245720062183) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 4 * (3 : ZMod 245720062183) ^ 4 := by rw [pow_add]
          _ = 6561 := by rw [factor_2_2]; decide
      have factor_2_4 : (3 : ZMod 245720062183) ^ 16 = 43046721 := by
        calc
          (3 : ZMod 245720062183) ^ 16 = (3 : ZMod 245720062183) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 8 * (3 : ZMod 245720062183) ^ 8 := by rw [pow_add]
          _ = 43046721 := by rw [factor_2_3]; decide
      have factor_2_5 : (3 : ZMod 245720062183) ^ 32 = 45199929838 := by
        calc
          (3 : ZMod 245720062183) ^ 32 = (3 : ZMod 245720062183) ^ (16 + 16) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 16 * (3 : ZMod 245720062183) ^ 16 := by rw [pow_add]
          _ = 45199929838 := by rw [factor_2_4]; decide
      have factor_2_6 : (3 : ZMod 245720062183) ^ 65 = 210590734779 := by
        calc
          (3 : ZMod 245720062183) ^ 65 = (3 : ZMod 245720062183) ^ (32 + 32 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 32 * (3 : ZMod 245720062183) ^ 32) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 210590734779 := by rw [factor_2_5]; decide
      have factor_2_7 : (3 : ZMod 245720062183) ^ 130 = 213251976029 := by
        calc
          (3 : ZMod 245720062183) ^ 130 = (3 : ZMod 245720062183) ^ (65 + 65) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 65 * (3 : ZMod 245720062183) ^ 65 := by rw [pow_add]
          _ = 213251976029 := by rw [factor_2_6]; decide
      have factor_2_8 : (3 : ZMod 245720062183) ^ 261 = 184300557321 := by
        calc
          (3 : ZMod 245720062183) ^ 261 = (3 : ZMod 245720062183) ^ (130 + 130 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 130 * (3 : ZMod 245720062183) ^ 130) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 184300557321 := by rw [factor_2_7]; decide
      have factor_2_9 : (3 : ZMod 245720062183) ^ 523 = 115987335426 := by
        calc
          (3 : ZMod 245720062183) ^ 523 = (3 : ZMod 245720062183) ^ (261 + 261 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 261 * (3 : ZMod 245720062183) ^ 261) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 115987335426 := by rw [factor_2_8]; decide
      have factor_2_10 : (3 : ZMod 245720062183) ^ 1046 = 152182415571 := by
        calc
          (3 : ZMod 245720062183) ^ 1046 = (3 : ZMod 245720062183) ^ (523 + 523) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 523 * (3 : ZMod 245720062183) ^ 523 := by rw [pow_add]
          _ = 152182415571 := by rw [factor_2_9]; decide
      have factor_2_11 : (3 : ZMod 245720062183) ^ 2092 = 114757030622 := by
        calc
          (3 : ZMod 245720062183) ^ 2092 = (3 : ZMod 245720062183) ^ (1046 + 1046) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 1046 * (3 : ZMod 245720062183) ^ 1046 := by rw [pow_add]
          _ = 114757030622 := by rw [factor_2_10]; decide
      have factor_2_12 : (3 : ZMod 245720062183) ^ 4184 = 151328869682 := by
        calc
          (3 : ZMod 245720062183) ^ 4184 = (3 : ZMod 245720062183) ^ (2092 + 2092) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 2092 * (3 : ZMod 245720062183) ^ 2092 := by rw [pow_add]
          _ = 151328869682 := by rw [factor_2_11]; decide
      have factor_2_13 : (3 : ZMod 245720062183) ^ 8369 = 159582471668 := by
        calc
          (3 : ZMod 245720062183) ^ 8369 = (3 : ZMod 245720062183) ^ (4184 + 4184 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 4184 * (3 : ZMod 245720062183) ^ 4184) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 159582471668 := by rw [factor_2_12]; decide
      have factor_2_14 : (3 : ZMod 245720062183) ^ 16738 = 28735008588 := by
        calc
          (3 : ZMod 245720062183) ^ 16738 = (3 : ZMod 245720062183) ^ (8369 + 8369) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 8369 * (3 : ZMod 245720062183) ^ 8369 := by rw [pow_add]
          _ = 28735008588 := by rw [factor_2_13]; decide
      have factor_2_15 : (3 : ZMod 245720062183) ^ 33476 = 111817212495 := by
        calc
          (3 : ZMod 245720062183) ^ 33476 = (3 : ZMod 245720062183) ^ (16738 + 16738) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 16738 * (3 : ZMod 245720062183) ^ 16738 := by rw [pow_add]
          _ = 111817212495 := by rw [factor_2_14]; decide
      have factor_2_16 : (3 : ZMod 245720062183) ^ 66953 = 218172850154 := by
        calc
          (3 : ZMod 245720062183) ^ 66953 = (3 : ZMod 245720062183) ^ (33476 + 33476 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 33476 * (3 : ZMod 245720062183) ^ 33476) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 218172850154 := by rw [factor_2_15]; decide
      have factor_2_17 : (3 : ZMod 245720062183) ^ 133906 = 110723464043 := by
        calc
          (3 : ZMod 245720062183) ^ 133906 = (3 : ZMod 245720062183) ^ (66953 + 66953) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 66953 * (3 : ZMod 245720062183) ^ 66953 := by rw [pow_add]
          _ = 110723464043 := by rw [factor_2_16]; decide
      have factor_2_18 : (3 : ZMod 245720062183) ^ 267813 = 27379431624 := by
        calc
          (3 : ZMod 245720062183) ^ 267813 = (3 : ZMod 245720062183) ^ (133906 + 133906 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 133906 * (3 : ZMod 245720062183) ^ 133906) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 27379431624 := by rw [factor_2_17]; decide
      have factor_2_19 : (3 : ZMod 245720062183) ^ 535627 = 162589154508 := by
        calc
          (3 : ZMod 245720062183) ^ 535627 = (3 : ZMod 245720062183) ^ (267813 + 267813 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 267813 * (3 : ZMod 245720062183) ^ 267813) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 162589154508 := by rw [factor_2_18]; decide
      have factor_2_20 : (3 : ZMod 245720062183) ^ 1071254 = 135048564313 := by
        calc
          (3 : ZMod 245720062183) ^ 1071254 = (3 : ZMod 245720062183) ^ (535627 + 535627) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 535627 * (3 : ZMod 245720062183) ^ 535627 := by rw [pow_add]
          _ = 135048564313 := by rw [factor_2_19]; decide
      have factor_2_21 : (3 : ZMod 245720062183) ^ 2142508 = 90105418718 := by
        calc
          (3 : ZMod 245720062183) ^ 2142508 = (3 : ZMod 245720062183) ^ (1071254 + 1071254) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 1071254 * (3 : ZMod 245720062183) ^ 1071254 := by rw [pow_add]
          _ = 90105418718 := by rw [factor_2_20]; decide
      have factor_2_22 : (3 : ZMod 245720062183) ^ 4285017 = 26276347214 := by
        calc
          (3 : ZMod 245720062183) ^ 4285017 = (3 : ZMod 245720062183) ^ (2142508 + 2142508 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 2142508 * (3 : ZMod 245720062183) ^ 2142508) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 26276347214 := by rw [factor_2_21]; decide
      have factor_2_23 : (3 : ZMod 245720062183) ^ 8570035 = 190148374636 := by
        calc
          (3 : ZMod 245720062183) ^ 8570035 = (3 : ZMod 245720062183) ^ (4285017 + 4285017 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 4285017 * (3 : ZMod 245720062183) ^ 4285017) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 190148374636 := by rw [factor_2_22]; decide
      have factor_2_24 : (3 : ZMod 245720062183) ^ 17140071 = 50571202994 := by
        calc
          (3 : ZMod 245720062183) ^ 17140071 = (3 : ZMod 245720062183) ^ (8570035 + 8570035 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 8570035 * (3 : ZMod 245720062183) ^ 8570035) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 50571202994 := by rw [factor_2_23]; decide
      have factor_2_25 : (3 : ZMod 245720062183) ^ 34280142 = 89593331174 := by
        calc
          (3 : ZMod 245720062183) ^ 34280142 = (3 : ZMod 245720062183) ^ (17140071 + 17140071) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 17140071 * (3 : ZMod 245720062183) ^ 17140071 := by rw [pow_add]
          _ = 89593331174 := by rw [factor_2_24]; decide
      have factor_2_26 : (3 : ZMod 245720062183) ^ 68560285 = 16733186504 := by
        calc
          (3 : ZMod 245720062183) ^ 68560285 = (3 : ZMod 245720062183) ^ (34280142 + 34280142 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 34280142 * (3 : ZMod 245720062183) ^ 34280142) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 16733186504 := by rw [factor_2_25]; decide
      have factor_2_27 : (3 : ZMod 245720062183) ^ 137120570 = 187254702344 := by
        calc
          (3 : ZMod 245720062183) ^ 137120570 = (3 : ZMod 245720062183) ^ (68560285 + 68560285) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 68560285 * (3 : ZMod 245720062183) ^ 68560285 := by rw [pow_add]
          _ = 187254702344 := by rw [factor_2_26]; decide
      have factor_2_28 : (3 : ZMod 245720062183) ^ 274241140 = 210173460229 := by
        calc
          (3 : ZMod 245720062183) ^ 274241140 = (3 : ZMod 245720062183) ^ (137120570 + 137120570) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 137120570 * (3 : ZMod 245720062183) ^ 137120570 := by rw [pow_add]
          _ = 210173460229 := by rw [factor_2_27]; decide
      have factor_2_29 : (3 : ZMod 245720062183) ^ 548482281 = 30100451763 := by
        calc
          (3 : ZMod 245720062183) ^ 548482281 = (3 : ZMod 245720062183) ^ (274241140 + 274241140 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 274241140 * (3 : ZMod 245720062183) ^ 274241140) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 30100451763 := by rw [factor_2_28]; decide
      have factor_2_30 : (3 : ZMod 245720062183) ^ 1096964563 = 49952185056 := by
        calc
          (3 : ZMod 245720062183) ^ 1096964563 = (3 : ZMod 245720062183) ^ (548482281 + 548482281 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 548482281 * (3 : ZMod 245720062183) ^ 548482281) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 49952185056 := by rw [factor_2_29]; decide
      have factor_2_31 : (3 : ZMod 245720062183) ^ 2193929126 = 156678260140 := by
        calc
          (3 : ZMod 245720062183) ^ 2193929126 = (3 : ZMod 245720062183) ^ (1096964563 + 1096964563) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 1096964563 * (3 : ZMod 245720062183) ^ 1096964563 := by rw [pow_add]
          _ = 156678260140 := by rw [factor_2_30]; decide
      have factor_2_32 : (3 : ZMod 245720062183) ^ 4387858253 = 100686052135 := by
        calc
          (3 : ZMod 245720062183) ^ 4387858253 = (3 : ZMod 245720062183) ^ (2193929126 + 2193929126 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 2193929126 * (3 : ZMod 245720062183) ^ 2193929126) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 100686052135 := by rw [factor_2_31]; decide
      have factor_2_33 : (3 : ZMod 245720062183) ^ 8775716506 = 156918822124 := by
        calc
          (3 : ZMod 245720062183) ^ 8775716506 = (3 : ZMod 245720062183) ^ (4387858253 + 4387858253) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 4387858253 * (3 : ZMod 245720062183) ^ 4387858253 := by rw [pow_add]
          _ = 156918822124 := by rw [factor_2_32]; decide
      have factor_2_34 : (3 : ZMod 245720062183) ^ 17551433013 = 134460352564 := by
        calc
          (3 : ZMod 245720062183) ^ 17551433013 = (3 : ZMod 245720062183) ^ (8775716506 + 8775716506 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 8775716506 * (3 : ZMod 245720062183) ^ 8775716506) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 134460352564 := by rw [factor_2_33]; decide
      have factor_2_35 : (3 : ZMod 245720062183) ^ 35102866026 = 24621546164 := by
        calc
          (3 : ZMod 245720062183) ^ 35102866026 = (3 : ZMod 245720062183) ^ (17551433013 + 17551433013) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 17551433013 * (3 : ZMod 245720062183) ^ 17551433013 := by rw [pow_add]
          _ = 24621546164 := by rw [factor_2_34]; decide
      change (3 : ZMod 245720062183) ^ 35102866026 ≠ 1
      rw [factor_2_35]
      decide
    ·
      have factor_3_0 : (3 : ZMod 245720062183) ^ 1 = 3 := by norm_num
      have factor_3_1 : (3 : ZMod 245720062183) ^ 3 = 27 := by
        calc
          (3 : ZMod 245720062183) ^ 3 = (3 : ZMod 245720062183) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 1 * (3 : ZMod 245720062183) ^ 1) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 27 := by rw [factor_3_0]; decide
      have factor_3_2 : (3 : ZMod 245720062183) ^ 7 = 2187 := by
        calc
          (3 : ZMod 245720062183) ^ 7 = (3 : ZMod 245720062183) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 3 * (3 : ZMod 245720062183) ^ 3) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 2187 := by rw [factor_3_1]; decide
      have factor_3_3 : (3 : ZMod 245720062183) ^ 15 = 14348907 := by
        calc
          (3 : ZMod 245720062183) ^ 15 = (3 : ZMod 245720062183) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 7 * (3 : ZMod 245720062183) ^ 7) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 14348907 := by rw [factor_3_2]; decide
      have factor_3_4 : (3 : ZMod 245720062183) ^ 31 = 178880018068 := by
        calc
          (3 : ZMod 245720062183) ^ 31 = (3 : ZMod 245720062183) ^ (15 + 15 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 15 * (3 : ZMod 245720062183) ^ 15) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 178880018068 := by rw [factor_3_3]; decide
      have factor_3_5 : (3 : ZMod 245720062183) ^ 62 = 89706344238 := by
        calc
          (3 : ZMod 245720062183) ^ 62 = (3 : ZMod 245720062183) ^ (31 + 31) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 31 * (3 : ZMod 245720062183) ^ 31 := by rw [pow_add]
          _ = 89706344238 := by rw [factor_3_4]; decide
      have factor_3_6 : (3 : ZMod 245720062183) ^ 124 = 122984025529 := by
        calc
          (3 : ZMod 245720062183) ^ 124 = (3 : ZMod 245720062183) ^ (62 + 62) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 62 * (3 : ZMod 245720062183) ^ 62 := by rw [pow_add]
          _ = 122984025529 := by rw [factor_3_5]; decide
      have factor_3_7 : (3 : ZMod 245720062183) ^ 248 = 223390228825 := by
        calc
          (3 : ZMod 245720062183) ^ 248 = (3 : ZMod 245720062183) ^ (124 + 124) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 124 * (3 : ZMod 245720062183) ^ 124 := by rw [pow_add]
          _ = 223390228825 := by rw [factor_3_6]; decide
      have factor_3_8 : (3 : ZMod 245720062183) ^ 496 = 226029780737 := by
        calc
          (3 : ZMod 245720062183) ^ 496 = (3 : ZMod 245720062183) ^ (248 + 248) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 248 * (3 : ZMod 245720062183) ^ 248 := by rw [pow_add]
          _ = 226029780737 := by rw [factor_3_7]; decide
      have factor_3_9 : (3 : ZMod 245720062183) ^ 992 = 193646315942 := by
        calc
          (3 : ZMod 245720062183) ^ 992 = (3 : ZMod 245720062183) ^ (496 + 496) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 496 * (3 : ZMod 245720062183) ^ 496 := by rw [pow_add]
          _ = 193646315942 := by rw [factor_3_8]; decide
      have factor_3_10 : (3 : ZMod 245720062183) ^ 1984 = 55723886443 := by
        calc
          (3 : ZMod 245720062183) ^ 1984 = (3 : ZMod 245720062183) ^ (992 + 992) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 992 * (3 : ZMod 245720062183) ^ 992 := by rw [pow_add]
          _ = 55723886443 := by rw [factor_3_9]; decide
      have factor_3_11 : (3 : ZMod 245720062183) ^ 3969 = 153242378959 := by
        calc
          (3 : ZMod 245720062183) ^ 3969 = (3 : ZMod 245720062183) ^ (1984 + 1984 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 1984 * (3 : ZMod 245720062183) ^ 1984) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 153242378959 := by rw [factor_3_10]; decide
      have factor_3_12 : (3 : ZMod 245720062183) ^ 7939 = 19256138862 := by
        calc
          (3 : ZMod 245720062183) ^ 7939 = (3 : ZMod 245720062183) ^ (3969 + 3969 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 3969 * (3 : ZMod 245720062183) ^ 3969) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 19256138862 := by rw [factor_3_11]; decide
      have factor_3_13 : (3 : ZMod 245720062183) ^ 15879 = 91329256748 := by
        calc
          (3 : ZMod 245720062183) ^ 15879 = (3 : ZMod 245720062183) ^ (7939 + 7939 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 7939 * (3 : ZMod 245720062183) ^ 7939) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 91329256748 := by rw [factor_3_12]; decide
      have factor_3_14 : (3 : ZMod 245720062183) ^ 31758 = 180240637681 := by
        calc
          (3 : ZMod 245720062183) ^ 31758 = (3 : ZMod 245720062183) ^ (15879 + 15879) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 15879 * (3 : ZMod 245720062183) ^ 15879 := by rw [pow_add]
          _ = 180240637681 := by rw [factor_3_13]; decide
      have factor_3_15 : (3 : ZMod 245720062183) ^ 63517 = 96613563169 := by
        calc
          (3 : ZMod 245720062183) ^ 63517 = (3 : ZMod 245720062183) ^ (31758 + 31758 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 31758 * (3 : ZMod 245720062183) ^ 31758) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 96613563169 := by rw [factor_3_14]; decide
      have factor_3_16 : (3 : ZMod 245720062183) ^ 127034 = 37427247118 := by
        calc
          (3 : ZMod 245720062183) ^ 127034 = (3 : ZMod 245720062183) ^ (63517 + 63517) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 63517 * (3 : ZMod 245720062183) ^ 63517 := by rw [pow_add]
          _ = 37427247118 := by rw [factor_3_15]; decide
      have factor_3_17 : (3 : ZMod 245720062183) ^ 254069 = 91055825944 := by
        calc
          (3 : ZMod 245720062183) ^ 254069 = (3 : ZMod 245720062183) ^ (127034 + 127034 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 127034 * (3 : ZMod 245720062183) ^ 127034) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 91055825944 := by rw [factor_3_16]; decide
      have factor_3_18 : (3 : ZMod 245720062183) ^ 508139 = 23938558397 := by
        calc
          (3 : ZMod 245720062183) ^ 508139 = (3 : ZMod 245720062183) ^ (254069 + 254069 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 254069 * (3 : ZMod 245720062183) ^ 254069) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 23938558397 := by rw [factor_3_17]; decide
      have factor_3_19 : (3 : ZMod 245720062183) ^ 1016279 = 22799421782 := by
        calc
          (3 : ZMod 245720062183) ^ 1016279 = (3 : ZMod 245720062183) ^ (508139 + 508139 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 508139 * (3 : ZMod 245720062183) ^ 508139) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 22799421782 := by rw [factor_3_18]; decide
      have factor_3_20 : (3 : ZMod 245720062183) ^ 2032558 = 116531008497 := by
        calc
          (3 : ZMod 245720062183) ^ 2032558 = (3 : ZMod 245720062183) ^ (1016279 + 1016279) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 1016279 * (3 : ZMod 245720062183) ^ 1016279 := by rw [pow_add]
          _ = 116531008497 := by rw [factor_3_19]; decide
      have factor_3_21 : (3 : ZMod 245720062183) ^ 4065117 = 243001731495 := by
        calc
          (3 : ZMod 245720062183) ^ 4065117 = (3 : ZMod 245720062183) ^ (2032558 + 2032558 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 2032558 * (3 : ZMod 245720062183) ^ 2032558) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 243001731495 := by rw [factor_3_20]; decide
      have factor_3_22 : (3 : ZMod 245720062183) ^ 8130234 = 7268288482 := by
        calc
          (3 : ZMod 245720062183) ^ 8130234 = (3 : ZMod 245720062183) ^ (4065117 + 4065117) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 4065117 * (3 : ZMod 245720062183) ^ 4065117 := by rw [pow_add]
          _ = 7268288482 := by rw [factor_3_21]; decide
      change (3 : ZMod 245720062183) ^ 8130234 ≠ 1
      rw [factor_3_22]
      decide
    ·
      have factor_4_0 : (3 : ZMod 245720062183) ^ 1 = 3 := by norm_num
      have factor_4_1 : (3 : ZMod 245720062183) ^ 2 = 9 := by
        calc
          (3 : ZMod 245720062183) ^ 2 = (3 : ZMod 245720062183) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 1 * (3 : ZMod 245720062183) ^ 1 := by rw [pow_add]
          _ = 9 := by rw [factor_4_0]; decide
      have factor_4_2 : (3 : ZMod 245720062183) ^ 4 = 81 := by
        calc
          (3 : ZMod 245720062183) ^ 4 = (3 : ZMod 245720062183) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 2 * (3 : ZMod 245720062183) ^ 2 := by rw [pow_add]
          _ = 81 := by rw [factor_4_1]; decide
      have factor_4_3 : (3 : ZMod 245720062183) ^ 9 = 19683 := by
        calc
          (3 : ZMod 245720062183) ^ 9 = (3 : ZMod 245720062183) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 4 * (3 : ZMod 245720062183) ^ 4) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 19683 := by rw [factor_4_2]; decide
      have factor_4_4 : (3 : ZMod 245720062183) ^ 19 = 1162261467 := by
        calc
          (3 : ZMod 245720062183) ^ 19 = (3 : ZMod 245720062183) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 9 * (3 : ZMod 245720062183) ^ 9) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 1162261467 := by rw [factor_4_3]; decide
      have factor_4_5 : (3 : ZMod 245720062183) ^ 38 = 24260519380 := by
        calc
          (3 : ZMod 245720062183) ^ 38 = (3 : ZMod 245720062183) ^ (19 + 19) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 19 * (3 : ZMod 245720062183) ^ 19 := by rw [pow_add]
          _ = 24260519380 := by rw [factor_4_4]; decide
      have factor_4_6 : (3 : ZMod 245720062183) ^ 77 = 153999630810 := by
        calc
          (3 : ZMod 245720062183) ^ 77 = (3 : ZMod 245720062183) ^ (38 + 38 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 38 * (3 : ZMod 245720062183) ^ 38) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 153999630810 := by rw [factor_4_5]; decide
      have factor_4_7 : (3 : ZMod 245720062183) ^ 154 = 210377026315 := by
        calc
          (3 : ZMod 245720062183) ^ 154 = (3 : ZMod 245720062183) ^ (77 + 77) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 77 * (3 : ZMod 245720062183) ^ 77 := by rw [pow_add]
          _ = 210377026315 := by rw [factor_4_6]; decide
      have factor_4_8 : (3 : ZMod 245720062183) ^ 309 = 45983256635 := by
        calc
          (3 : ZMod 245720062183) ^ 309 = (3 : ZMod 245720062183) ^ (154 + 154 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 154 * (3 : ZMod 245720062183) ^ 154) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 45983256635 := by rw [factor_4_7]; decide
      have factor_4_9 : (3 : ZMod 245720062183) ^ 619 = 156286563931 := by
        calc
          (3 : ZMod 245720062183) ^ 619 = (3 : ZMod 245720062183) ^ (309 + 309 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 309 * (3 : ZMod 245720062183) ^ 309) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 156286563931 := by rw [factor_4_8]; decide
      have factor_4_10 : (3 : ZMod 245720062183) ^ 1239 = 66597351865 := by
        calc
          (3 : ZMod 245720062183) ^ 1239 = (3 : ZMod 245720062183) ^ (619 + 619 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 619 * (3 : ZMod 245720062183) ^ 619) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 66597351865 := by rw [factor_4_9]; decide
      have factor_4_11 : (3 : ZMod 245720062183) ^ 2479 = 172618528894 := by
        calc
          (3 : ZMod 245720062183) ^ 2479 = (3 : ZMod 245720062183) ^ (1239 + 1239 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 1239 * (3 : ZMod 245720062183) ^ 1239) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 172618528894 := by rw [factor_4_10]; decide
      have factor_4_12 : (3 : ZMod 245720062183) ^ 4958 = 125429728822 := by
        calc
          (3 : ZMod 245720062183) ^ 4958 = (3 : ZMod 245720062183) ^ (2479 + 2479) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 2479 * (3 : ZMod 245720062183) ^ 2479 := by rw [pow_add]
          _ = 125429728822 := by rw [factor_4_11]; decide
      have factor_4_13 : (3 : ZMod 245720062183) ^ 9916 = 191055000460 := by
        calc
          (3 : ZMod 245720062183) ^ 9916 = (3 : ZMod 245720062183) ^ (4958 + 4958) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 4958 * (3 : ZMod 245720062183) ^ 4958 := by rw [pow_add]
          _ = 191055000460 := by rw [factor_4_12]; decide
      have factor_4_14 : (3 : ZMod 245720062183) ^ 19833 = 186838830080 := by
        calc
          (3 : ZMod 245720062183) ^ 19833 = (3 : ZMod 245720062183) ^ (9916 + 9916 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 9916 * (3 : ZMod 245720062183) ^ 9916) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 186838830080 := by rw [factor_4_13]; decide
      have factor_4_15 : (3 : ZMod 245720062183) ^ 39667 = 37437608872 := by
        calc
          (3 : ZMod 245720062183) ^ 39667 = (3 : ZMod 245720062183) ^ (19833 + 19833 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 19833 * (3 : ZMod 245720062183) ^ 19833) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 37437608872 := by rw [factor_4_14]; decide
      have factor_4_16 : (3 : ZMod 245720062183) ^ 79335 = 177087400062 := by
        calc
          (3 : ZMod 245720062183) ^ 79335 = (3 : ZMod 245720062183) ^ (39667 + 39667 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 39667 * (3 : ZMod 245720062183) ^ 39667) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 177087400062 := by rw [factor_4_15]; decide
      have factor_4_17 : (3 : ZMod 245720062183) ^ 158670 = 3893351086 := by
        calc
          (3 : ZMod 245720062183) ^ 158670 = (3 : ZMod 245720062183) ^ (79335 + 79335) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 79335 * (3 : ZMod 245720062183) ^ 79335 := by rw [pow_add]
          _ = 3893351086 := by rw [factor_4_16]; decide
      have factor_4_18 : (3 : ZMod 245720062183) ^ 317341 = 80102963616 := by
        calc
          (3 : ZMod 245720062183) ^ 317341 = (3 : ZMod 245720062183) ^ (158670 + 158670 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 158670 * (3 : ZMod 245720062183) ^ 158670) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 80102963616 := by rw [factor_4_17]; decide
      have factor_4_19 : (3 : ZMod 245720062183) ^ 634683 = 184854674413 := by
        calc
          (3 : ZMod 245720062183) ^ 634683 = (3 : ZMod 245720062183) ^ (317341 + 317341 + 1) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = ((3 : ZMod 245720062183) ^ 317341 * (3 : ZMod 245720062183) ^ 317341) * (3 : ZMod 245720062183) := by rw [pow_succ, pow_add]
          _ = 184854674413 := by rw [factor_4_18]; decide
      have factor_4_20 : (3 : ZMod 245720062183) ^ 1269366 = 83087837576 := by
        calc
          (3 : ZMod 245720062183) ^ 1269366 = (3 : ZMod 245720062183) ^ (634683 + 634683) :=
            congrArg (fun n : ℕ => (3 : ZMod 245720062183) ^ n) (by norm_num)
          _ = (3 : ZMod 245720062183) ^ 634683 * (3 : ZMod 245720062183) ^ 634683 := by rw [pow_add]
          _ = 83087837576 := by rw [factor_4_19]; decide
      change (3 : ZMod 245720062183) ^ 1269366 ≠ 1
      rw [factor_4_20]
      decide

#print axioms prime_lucas_245720062183

end TotientTailPeriodKiller
end Erdos249257
