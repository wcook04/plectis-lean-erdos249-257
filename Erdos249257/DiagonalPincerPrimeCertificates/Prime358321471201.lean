import Erdos249257.DiagonalPincerCertificates

/-! A bounded Lucas certificate for one t=29 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_358321471201 : Nat.Prime 358321471201 := by
  apply lucas_primality 358321471201 (37 : ZMod 358321471201)
  ·
      have fermat_0 : (37 : ZMod 358321471201) ^ 1 = 37 := by norm_num
      have fermat_1 : (37 : ZMod 358321471201) ^ 2 = 1369 := by
        calc
          (37 : ZMod 358321471201) ^ 2 = (37 : ZMod 358321471201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 1 * (37 : ZMod 358321471201) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [fermat_0]; decide
      have fermat_2 : (37 : ZMod 358321471201) ^ 5 = 69343957 := by
        calc
          (37 : ZMod 358321471201) ^ 5 = (37 : ZMod 358321471201) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 2 * (37 : ZMod 358321471201) ^ 2) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 69343957 := by rw [fermat_1]; decide
      have fermat_3 : (37 : ZMod 358321471201) ^ 10 = 268550371630 := by
        calc
          (37 : ZMod 358321471201) ^ 10 = (37 : ZMod 358321471201) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 5 * (37 : ZMod 358321471201) ^ 5 := by rw [pow_add]
          _ = 268550371630 := by rw [fermat_2]; decide
      have fermat_4 : (37 : ZMod 358321471201) ^ 20 = 177775392681 := by
        calc
          (37 : ZMod 358321471201) ^ 20 = (37 : ZMod 358321471201) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 10 * (37 : ZMod 358321471201) ^ 10 := by rw [pow_add]
          _ = 177775392681 := by rw [fermat_3]; decide
      have fermat_5 : (37 : ZMod 358321471201) ^ 41 = 71470014032 := by
        calc
          (37 : ZMod 358321471201) ^ 41 = (37 : ZMod 358321471201) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 20 * (37 : ZMod 358321471201) ^ 20) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 71470014032 := by rw [fermat_4]; decide
      have fermat_6 : (37 : ZMod 358321471201) ^ 83 = 41348858093 := by
        calc
          (37 : ZMod 358321471201) ^ 83 = (37 : ZMod 358321471201) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 41 * (37 : ZMod 358321471201) ^ 41) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 41348858093 := by rw [fermat_5]; decide
      have fermat_7 : (37 : ZMod 358321471201) ^ 166 = 82317296559 := by
        calc
          (37 : ZMod 358321471201) ^ 166 = (37 : ZMod 358321471201) ^ (83 + 83) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 83 * (37 : ZMod 358321471201) ^ 83 := by rw [pow_add]
          _ = 82317296559 := by rw [fermat_6]; decide
      have fermat_8 : (37 : ZMod 358321471201) ^ 333 = 216671334341 := by
        calc
          (37 : ZMod 358321471201) ^ 333 = (37 : ZMod 358321471201) ^ (166 + 166 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 166 * (37 : ZMod 358321471201) ^ 166) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 216671334341 := by rw [fermat_7]; decide
      have fermat_9 : (37 : ZMod 358321471201) ^ 667 = 266936576162 := by
        calc
          (37 : ZMod 358321471201) ^ 667 = (37 : ZMod 358321471201) ^ (333 + 333 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 333 * (37 : ZMod 358321471201) ^ 333) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 266936576162 := by rw [fermat_8]; decide
      have fermat_10 : (37 : ZMod 358321471201) ^ 1334 = 320001544251 := by
        calc
          (37 : ZMod 358321471201) ^ 1334 = (37 : ZMod 358321471201) ^ (667 + 667) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 667 * (37 : ZMod 358321471201) ^ 667 := by rw [pow_add]
          _ = 320001544251 := by rw [fermat_9]; decide
      have fermat_11 : (37 : ZMod 358321471201) ^ 2669 = 353951696221 := by
        calc
          (37 : ZMod 358321471201) ^ 2669 = (37 : ZMod 358321471201) ^ (1334 + 1334 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 1334 * (37 : ZMod 358321471201) ^ 1334) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 353951696221 := by rw [fermat_10]; decide
      have fermat_12 : (37 : ZMod 358321471201) ^ 5339 = 164538765841 := by
        calc
          (37 : ZMod 358321471201) ^ 5339 = (37 : ZMod 358321471201) ^ (2669 + 2669 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 2669 * (37 : ZMod 358321471201) ^ 2669) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 164538765841 := by rw [fermat_11]; decide
      have fermat_13 : (37 : ZMod 358321471201) ^ 10678 = 38695999545 := by
        calc
          (37 : ZMod 358321471201) ^ 10678 = (37 : ZMod 358321471201) ^ (5339 + 5339) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 5339 * (37 : ZMod 358321471201) ^ 5339 := by rw [pow_add]
          _ = 38695999545 := by rw [fermat_12]; decide
      have fermat_14 : (37 : ZMod 358321471201) ^ 21357 = 341079969882 := by
        calc
          (37 : ZMod 358321471201) ^ 21357 = (37 : ZMod 358321471201) ^ (10678 + 10678 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 10678 * (37 : ZMod 358321471201) ^ 10678) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 341079969882 := by rw [fermat_13]; decide
      have fermat_15 : (37 : ZMod 358321471201) ^ 42715 = 69723189286 := by
        calc
          (37 : ZMod 358321471201) ^ 42715 = (37 : ZMod 358321471201) ^ (21357 + 21357 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 21357 * (37 : ZMod 358321471201) ^ 21357) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 69723189286 := by rw [fermat_14]; decide
      have fermat_16 : (37 : ZMod 358321471201) ^ 85430 = 348770586345 := by
        calc
          (37 : ZMod 358321471201) ^ 85430 = (37 : ZMod 358321471201) ^ (42715 + 42715) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 42715 * (37 : ZMod 358321471201) ^ 42715 := by rw [pow_add]
          _ = 348770586345 := by rw [fermat_15]; decide
      have fermat_17 : (37 : ZMod 358321471201) ^ 170860 = 17073997737 := by
        calc
          (37 : ZMod 358321471201) ^ 170860 = (37 : ZMod 358321471201) ^ (85430 + 85430) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 85430 * (37 : ZMod 358321471201) ^ 85430 := by rw [pow_add]
          _ = 17073997737 := by rw [fermat_16]; decide
      have fermat_18 : (37 : ZMod 358321471201) ^ 341721 = 166456362649 := by
        calc
          (37 : ZMod 358321471201) ^ 341721 = (37 : ZMod 358321471201) ^ (170860 + 170860 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 170860 * (37 : ZMod 358321471201) ^ 170860) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 166456362649 := by rw [fermat_17]; decide
      have fermat_19 : (37 : ZMod 358321471201) ^ 683443 = 230744834187 := by
        calc
          (37 : ZMod 358321471201) ^ 683443 = (37 : ZMod 358321471201) ^ (341721 + 341721 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 341721 * (37 : ZMod 358321471201) ^ 341721) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 230744834187 := by rw [fermat_18]; decide
      have fermat_20 : (37 : ZMod 358321471201) ^ 1366887 = 164132945997 := by
        calc
          (37 : ZMod 358321471201) ^ 1366887 = (37 : ZMod 358321471201) ^ (683443 + 683443 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 683443 * (37 : ZMod 358321471201) ^ 683443) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 164132945997 := by rw [fermat_19]; decide
      have fermat_21 : (37 : ZMod 358321471201) ^ 2733775 = 161782976470 := by
        calc
          (37 : ZMod 358321471201) ^ 2733775 = (37 : ZMod 358321471201) ^ (1366887 + 1366887 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 1366887 * (37 : ZMod 358321471201) ^ 1366887) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 161782976470 := by rw [fermat_20]; decide
      have fermat_22 : (37 : ZMod 358321471201) ^ 5467551 = 81290251512 := by
        calc
          (37 : ZMod 358321471201) ^ 5467551 = (37 : ZMod 358321471201) ^ (2733775 + 2733775 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 2733775 * (37 : ZMod 358321471201) ^ 2733775) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 81290251512 := by rw [fermat_21]; decide
      have fermat_23 : (37 : ZMod 358321471201) ^ 10935103 = 74656316417 := by
        calc
          (37 : ZMod 358321471201) ^ 10935103 = (37 : ZMod 358321471201) ^ (5467551 + 5467551 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 5467551 * (37 : ZMod 358321471201) ^ 5467551) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 74656316417 := by rw [fermat_22]; decide
      have fermat_24 : (37 : ZMod 358321471201) ^ 21870206 = 122099962469 := by
        calc
          (37 : ZMod 358321471201) ^ 21870206 = (37 : ZMod 358321471201) ^ (10935103 + 10935103) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 10935103 * (37 : ZMod 358321471201) ^ 10935103 := by rw [pow_add]
          _ = 122099962469 := by rw [fermat_23]; decide
      have fermat_25 : (37 : ZMod 358321471201) ^ 43740413 = 30063982887 := by
        calc
          (37 : ZMod 358321471201) ^ 43740413 = (37 : ZMod 358321471201) ^ (21870206 + 21870206 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 21870206 * (37 : ZMod 358321471201) ^ 21870206) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 30063982887 := by rw [fermat_24]; decide
      have fermat_26 : (37 : ZMod 358321471201) ^ 87480827 = 138535259715 := by
        calc
          (37 : ZMod 358321471201) ^ 87480827 = (37 : ZMod 358321471201) ^ (43740413 + 43740413 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 43740413 * (37 : ZMod 358321471201) ^ 43740413) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 138535259715 := by rw [fermat_25]; decide
      have fermat_27 : (37 : ZMod 358321471201) ^ 174961655 = 268849055085 := by
        calc
          (37 : ZMod 358321471201) ^ 174961655 = (37 : ZMod 358321471201) ^ (87480827 + 87480827 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 87480827 * (37 : ZMod 358321471201) ^ 87480827) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 268849055085 := by rw [fermat_26]; decide
      have fermat_28 : (37 : ZMod 358321471201) ^ 349923311 = 350733175341 := by
        calc
          (37 : ZMod 358321471201) ^ 349923311 = (37 : ZMod 358321471201) ^ (174961655 + 174961655 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 174961655 * (37 : ZMod 358321471201) ^ 174961655) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 350733175341 := by rw [fermat_27]; decide
      have fermat_29 : (37 : ZMod 358321471201) ^ 699846623 = 274386345523 := by
        calc
          (37 : ZMod 358321471201) ^ 699846623 = (37 : ZMod 358321471201) ^ (349923311 + 349923311 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 349923311 * (37 : ZMod 358321471201) ^ 349923311) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 274386345523 := by rw [fermat_28]; decide
      have fermat_30 : (37 : ZMod 358321471201) ^ 1399693246 = 252784256181 := by
        calc
          (37 : ZMod 358321471201) ^ 1399693246 = (37 : ZMod 358321471201) ^ (699846623 + 699846623) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 699846623 * (37 : ZMod 358321471201) ^ 699846623 := by rw [pow_add]
          _ = 252784256181 := by rw [fermat_29]; decide
      have fermat_31 : (37 : ZMod 358321471201) ^ 2799386493 = 323068767287 := by
        calc
          (37 : ZMod 358321471201) ^ 2799386493 = (37 : ZMod 358321471201) ^ (1399693246 + 1399693246 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 1399693246 * (37 : ZMod 358321471201) ^ 1399693246) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 323068767287 := by rw [fermat_30]; decide
      have fermat_32 : (37 : ZMod 358321471201) ^ 5598772987 = 282703437689 := by
        calc
          (37 : ZMod 358321471201) ^ 5598772987 = (37 : ZMod 358321471201) ^ (2799386493 + 2799386493 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 2799386493 * (37 : ZMod 358321471201) ^ 2799386493) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 282703437689 := by rw [fermat_31]; decide
      have fermat_33 : (37 : ZMod 358321471201) ^ 11197545975 = 245524720411 := by
        calc
          (37 : ZMod 358321471201) ^ 11197545975 = (37 : ZMod 358321471201) ^ (5598772987 + 5598772987 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 5598772987 * (37 : ZMod 358321471201) ^ 5598772987) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 245524720411 := by rw [fermat_32]; decide
      have fermat_34 : (37 : ZMod 358321471201) ^ 22395091950 = 221840849188 := by
        calc
          (37 : ZMod 358321471201) ^ 22395091950 = (37 : ZMod 358321471201) ^ (11197545975 + 11197545975) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 11197545975 * (37 : ZMod 358321471201) ^ 11197545975 := by rw [pow_add]
          _ = 221840849188 := by rw [fermat_33]; decide
      have fermat_35 : (37 : ZMod 358321471201) ^ 44790183900 = 225424625643 := by
        calc
          (37 : ZMod 358321471201) ^ 44790183900 = (37 : ZMod 358321471201) ^ (22395091950 + 22395091950) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 22395091950 * (37 : ZMod 358321471201) ^ 22395091950 := by rw [pow_add]
          _ = 225424625643 := by rw [fermat_34]; decide
      have fermat_36 : (37 : ZMod 358321471201) ^ 89580367800 = 15839957818 := by
        calc
          (37 : ZMod 358321471201) ^ 89580367800 = (37 : ZMod 358321471201) ^ (44790183900 + 44790183900) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 44790183900 * (37 : ZMod 358321471201) ^ 44790183900 := by rw [pow_add]
          _ = 15839957818 := by rw [fermat_35]; decide
      have fermat_37 : (37 : ZMod 358321471201) ^ 179160735600 = 358321471200 := by
        calc
          (37 : ZMod 358321471201) ^ 179160735600 = (37 : ZMod 358321471201) ^ (89580367800 + 89580367800) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 89580367800 * (37 : ZMod 358321471201) ^ 89580367800 := by rw [pow_add]
          _ = 358321471200 := by rw [fermat_36]; decide
      have fermat_38 : (37 : ZMod 358321471201) ^ 358321471200 = 1 := by
        calc
          (37 : ZMod 358321471201) ^ 358321471200 = (37 : ZMod 358321471201) ^ (179160735600 + 179160735600) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 179160735600 * (37 : ZMod 358321471201) ^ 179160735600 := by rw [pow_add]
          _ = 1 := by rw [fermat_37]; decide
      simpa using fermat_38
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 3), (5, 2), (7, 1), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 3), (5, 2), (7, 1), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1)] : List FactorBlock).map factorBlockValue).prod = 358321471201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (37 : ZMod 358321471201) ^ 1 = 37 := by norm_num
      have factor_0_1 : (37 : ZMod 358321471201) ^ 2 = 1369 := by
        calc
          (37 : ZMod 358321471201) ^ 2 = (37 : ZMod 358321471201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 1 * (37 : ZMod 358321471201) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_0_0]; decide
      have factor_0_2 : (37 : ZMod 358321471201) ^ 5 = 69343957 := by
        calc
          (37 : ZMod 358321471201) ^ 5 = (37 : ZMod 358321471201) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 2 * (37 : ZMod 358321471201) ^ 2) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 69343957 := by rw [factor_0_1]; decide
      have factor_0_3 : (37 : ZMod 358321471201) ^ 10 = 268550371630 := by
        calc
          (37 : ZMod 358321471201) ^ 10 = (37 : ZMod 358321471201) ^ (5 + 5) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 5 * (37 : ZMod 358321471201) ^ 5 := by rw [pow_add]
          _ = 268550371630 := by rw [factor_0_2]; decide
      have factor_0_4 : (37 : ZMod 358321471201) ^ 20 = 177775392681 := by
        calc
          (37 : ZMod 358321471201) ^ 20 = (37 : ZMod 358321471201) ^ (10 + 10) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 10 * (37 : ZMod 358321471201) ^ 10 := by rw [pow_add]
          _ = 177775392681 := by rw [factor_0_3]; decide
      have factor_0_5 : (37 : ZMod 358321471201) ^ 41 = 71470014032 := by
        calc
          (37 : ZMod 358321471201) ^ 41 = (37 : ZMod 358321471201) ^ (20 + 20 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 20 * (37 : ZMod 358321471201) ^ 20) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 71470014032 := by rw [factor_0_4]; decide
      have factor_0_6 : (37 : ZMod 358321471201) ^ 83 = 41348858093 := by
        calc
          (37 : ZMod 358321471201) ^ 83 = (37 : ZMod 358321471201) ^ (41 + 41 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 41 * (37 : ZMod 358321471201) ^ 41) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 41348858093 := by rw [factor_0_5]; decide
      have factor_0_7 : (37 : ZMod 358321471201) ^ 166 = 82317296559 := by
        calc
          (37 : ZMod 358321471201) ^ 166 = (37 : ZMod 358321471201) ^ (83 + 83) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 83 * (37 : ZMod 358321471201) ^ 83 := by rw [pow_add]
          _ = 82317296559 := by rw [factor_0_6]; decide
      have factor_0_8 : (37 : ZMod 358321471201) ^ 333 = 216671334341 := by
        calc
          (37 : ZMod 358321471201) ^ 333 = (37 : ZMod 358321471201) ^ (166 + 166 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 166 * (37 : ZMod 358321471201) ^ 166) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 216671334341 := by rw [factor_0_7]; decide
      have factor_0_9 : (37 : ZMod 358321471201) ^ 667 = 266936576162 := by
        calc
          (37 : ZMod 358321471201) ^ 667 = (37 : ZMod 358321471201) ^ (333 + 333 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 333 * (37 : ZMod 358321471201) ^ 333) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 266936576162 := by rw [factor_0_8]; decide
      have factor_0_10 : (37 : ZMod 358321471201) ^ 1334 = 320001544251 := by
        calc
          (37 : ZMod 358321471201) ^ 1334 = (37 : ZMod 358321471201) ^ (667 + 667) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 667 * (37 : ZMod 358321471201) ^ 667 := by rw [pow_add]
          _ = 320001544251 := by rw [factor_0_9]; decide
      have factor_0_11 : (37 : ZMod 358321471201) ^ 2669 = 353951696221 := by
        calc
          (37 : ZMod 358321471201) ^ 2669 = (37 : ZMod 358321471201) ^ (1334 + 1334 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 1334 * (37 : ZMod 358321471201) ^ 1334) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 353951696221 := by rw [factor_0_10]; decide
      have factor_0_12 : (37 : ZMod 358321471201) ^ 5339 = 164538765841 := by
        calc
          (37 : ZMod 358321471201) ^ 5339 = (37 : ZMod 358321471201) ^ (2669 + 2669 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 2669 * (37 : ZMod 358321471201) ^ 2669) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 164538765841 := by rw [factor_0_11]; decide
      have factor_0_13 : (37 : ZMod 358321471201) ^ 10678 = 38695999545 := by
        calc
          (37 : ZMod 358321471201) ^ 10678 = (37 : ZMod 358321471201) ^ (5339 + 5339) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 5339 * (37 : ZMod 358321471201) ^ 5339 := by rw [pow_add]
          _ = 38695999545 := by rw [factor_0_12]; decide
      have factor_0_14 : (37 : ZMod 358321471201) ^ 21357 = 341079969882 := by
        calc
          (37 : ZMod 358321471201) ^ 21357 = (37 : ZMod 358321471201) ^ (10678 + 10678 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 10678 * (37 : ZMod 358321471201) ^ 10678) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 341079969882 := by rw [factor_0_13]; decide
      have factor_0_15 : (37 : ZMod 358321471201) ^ 42715 = 69723189286 := by
        calc
          (37 : ZMod 358321471201) ^ 42715 = (37 : ZMod 358321471201) ^ (21357 + 21357 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 21357 * (37 : ZMod 358321471201) ^ 21357) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 69723189286 := by rw [factor_0_14]; decide
      have factor_0_16 : (37 : ZMod 358321471201) ^ 85430 = 348770586345 := by
        calc
          (37 : ZMod 358321471201) ^ 85430 = (37 : ZMod 358321471201) ^ (42715 + 42715) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 42715 * (37 : ZMod 358321471201) ^ 42715 := by rw [pow_add]
          _ = 348770586345 := by rw [factor_0_15]; decide
      have factor_0_17 : (37 : ZMod 358321471201) ^ 170860 = 17073997737 := by
        calc
          (37 : ZMod 358321471201) ^ 170860 = (37 : ZMod 358321471201) ^ (85430 + 85430) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 85430 * (37 : ZMod 358321471201) ^ 85430 := by rw [pow_add]
          _ = 17073997737 := by rw [factor_0_16]; decide
      have factor_0_18 : (37 : ZMod 358321471201) ^ 341721 = 166456362649 := by
        calc
          (37 : ZMod 358321471201) ^ 341721 = (37 : ZMod 358321471201) ^ (170860 + 170860 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 170860 * (37 : ZMod 358321471201) ^ 170860) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 166456362649 := by rw [factor_0_17]; decide
      have factor_0_19 : (37 : ZMod 358321471201) ^ 683443 = 230744834187 := by
        calc
          (37 : ZMod 358321471201) ^ 683443 = (37 : ZMod 358321471201) ^ (341721 + 341721 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 341721 * (37 : ZMod 358321471201) ^ 341721) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 230744834187 := by rw [factor_0_18]; decide
      have factor_0_20 : (37 : ZMod 358321471201) ^ 1366887 = 164132945997 := by
        calc
          (37 : ZMod 358321471201) ^ 1366887 = (37 : ZMod 358321471201) ^ (683443 + 683443 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 683443 * (37 : ZMod 358321471201) ^ 683443) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 164132945997 := by rw [factor_0_19]; decide
      have factor_0_21 : (37 : ZMod 358321471201) ^ 2733775 = 161782976470 := by
        calc
          (37 : ZMod 358321471201) ^ 2733775 = (37 : ZMod 358321471201) ^ (1366887 + 1366887 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 1366887 * (37 : ZMod 358321471201) ^ 1366887) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 161782976470 := by rw [factor_0_20]; decide
      have factor_0_22 : (37 : ZMod 358321471201) ^ 5467551 = 81290251512 := by
        calc
          (37 : ZMod 358321471201) ^ 5467551 = (37 : ZMod 358321471201) ^ (2733775 + 2733775 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 2733775 * (37 : ZMod 358321471201) ^ 2733775) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 81290251512 := by rw [factor_0_21]; decide
      have factor_0_23 : (37 : ZMod 358321471201) ^ 10935103 = 74656316417 := by
        calc
          (37 : ZMod 358321471201) ^ 10935103 = (37 : ZMod 358321471201) ^ (5467551 + 5467551 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 5467551 * (37 : ZMod 358321471201) ^ 5467551) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 74656316417 := by rw [factor_0_22]; decide
      have factor_0_24 : (37 : ZMod 358321471201) ^ 21870206 = 122099962469 := by
        calc
          (37 : ZMod 358321471201) ^ 21870206 = (37 : ZMod 358321471201) ^ (10935103 + 10935103) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 10935103 * (37 : ZMod 358321471201) ^ 10935103 := by rw [pow_add]
          _ = 122099962469 := by rw [factor_0_23]; decide
      have factor_0_25 : (37 : ZMod 358321471201) ^ 43740413 = 30063982887 := by
        calc
          (37 : ZMod 358321471201) ^ 43740413 = (37 : ZMod 358321471201) ^ (21870206 + 21870206 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 21870206 * (37 : ZMod 358321471201) ^ 21870206) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 30063982887 := by rw [factor_0_24]; decide
      have factor_0_26 : (37 : ZMod 358321471201) ^ 87480827 = 138535259715 := by
        calc
          (37 : ZMod 358321471201) ^ 87480827 = (37 : ZMod 358321471201) ^ (43740413 + 43740413 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 43740413 * (37 : ZMod 358321471201) ^ 43740413) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 138535259715 := by rw [factor_0_25]; decide
      have factor_0_27 : (37 : ZMod 358321471201) ^ 174961655 = 268849055085 := by
        calc
          (37 : ZMod 358321471201) ^ 174961655 = (37 : ZMod 358321471201) ^ (87480827 + 87480827 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 87480827 * (37 : ZMod 358321471201) ^ 87480827) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 268849055085 := by rw [factor_0_26]; decide
      have factor_0_28 : (37 : ZMod 358321471201) ^ 349923311 = 350733175341 := by
        calc
          (37 : ZMod 358321471201) ^ 349923311 = (37 : ZMod 358321471201) ^ (174961655 + 174961655 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 174961655 * (37 : ZMod 358321471201) ^ 174961655) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 350733175341 := by rw [factor_0_27]; decide
      have factor_0_29 : (37 : ZMod 358321471201) ^ 699846623 = 274386345523 := by
        calc
          (37 : ZMod 358321471201) ^ 699846623 = (37 : ZMod 358321471201) ^ (349923311 + 349923311 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 349923311 * (37 : ZMod 358321471201) ^ 349923311) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 274386345523 := by rw [factor_0_28]; decide
      have factor_0_30 : (37 : ZMod 358321471201) ^ 1399693246 = 252784256181 := by
        calc
          (37 : ZMod 358321471201) ^ 1399693246 = (37 : ZMod 358321471201) ^ (699846623 + 699846623) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 699846623 * (37 : ZMod 358321471201) ^ 699846623 := by rw [pow_add]
          _ = 252784256181 := by rw [factor_0_29]; decide
      have factor_0_31 : (37 : ZMod 358321471201) ^ 2799386493 = 323068767287 := by
        calc
          (37 : ZMod 358321471201) ^ 2799386493 = (37 : ZMod 358321471201) ^ (1399693246 + 1399693246 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 1399693246 * (37 : ZMod 358321471201) ^ 1399693246) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 323068767287 := by rw [factor_0_30]; decide
      have factor_0_32 : (37 : ZMod 358321471201) ^ 5598772987 = 282703437689 := by
        calc
          (37 : ZMod 358321471201) ^ 5598772987 = (37 : ZMod 358321471201) ^ (2799386493 + 2799386493 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 2799386493 * (37 : ZMod 358321471201) ^ 2799386493) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 282703437689 := by rw [factor_0_31]; decide
      have factor_0_33 : (37 : ZMod 358321471201) ^ 11197545975 = 245524720411 := by
        calc
          (37 : ZMod 358321471201) ^ 11197545975 = (37 : ZMod 358321471201) ^ (5598772987 + 5598772987 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 5598772987 * (37 : ZMod 358321471201) ^ 5598772987) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 245524720411 := by rw [factor_0_32]; decide
      have factor_0_34 : (37 : ZMod 358321471201) ^ 22395091950 = 221840849188 := by
        calc
          (37 : ZMod 358321471201) ^ 22395091950 = (37 : ZMod 358321471201) ^ (11197545975 + 11197545975) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 11197545975 * (37 : ZMod 358321471201) ^ 11197545975 := by rw [pow_add]
          _ = 221840849188 := by rw [factor_0_33]; decide
      have factor_0_35 : (37 : ZMod 358321471201) ^ 44790183900 = 225424625643 := by
        calc
          (37 : ZMod 358321471201) ^ 44790183900 = (37 : ZMod 358321471201) ^ (22395091950 + 22395091950) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 22395091950 * (37 : ZMod 358321471201) ^ 22395091950 := by rw [pow_add]
          _ = 225424625643 := by rw [factor_0_34]; decide
      have factor_0_36 : (37 : ZMod 358321471201) ^ 89580367800 = 15839957818 := by
        calc
          (37 : ZMod 358321471201) ^ 89580367800 = (37 : ZMod 358321471201) ^ (44790183900 + 44790183900) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 44790183900 * (37 : ZMod 358321471201) ^ 44790183900 := by rw [pow_add]
          _ = 15839957818 := by rw [factor_0_35]; decide
      have factor_0_37 : (37 : ZMod 358321471201) ^ 179160735600 = 358321471200 := by
        calc
          (37 : ZMod 358321471201) ^ 179160735600 = (37 : ZMod 358321471201) ^ (89580367800 + 89580367800) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 89580367800 * (37 : ZMod 358321471201) ^ 89580367800 := by rw [pow_add]
          _ = 358321471200 := by rw [factor_0_36]; decide
      change (37 : ZMod 358321471201) ^ 179160735600 ≠ 1
      rw [factor_0_37]
      decide
    ·
      have factor_1_0 : (37 : ZMod 358321471201) ^ 1 = 37 := by norm_num
      have factor_1_1 : (37 : ZMod 358321471201) ^ 3 = 50653 := by
        calc
          (37 : ZMod 358321471201) ^ 3 = (37 : ZMod 358321471201) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 1 * (37 : ZMod 358321471201) ^ 1) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 50653 := by rw [factor_1_0]; decide
      have factor_1_2 : (37 : ZMod 358321471201) ^ 6 = 2565726409 := by
        calc
          (37 : ZMod 358321471201) ^ 6 = (37 : ZMod 358321471201) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 3 * (37 : ZMod 358321471201) ^ 3 := by rw [pow_add]
          _ = 2565726409 := by rw [factor_1_1]; decide
      have factor_1_3 : (37 : ZMod 358321471201) ^ 13 = 282284442028 := by
        calc
          (37 : ZMod 358321471201) ^ 13 = (37 : ZMod 358321471201) ^ (6 + 6 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 6 * (37 : ZMod 358321471201) ^ 6) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 282284442028 := by rw [factor_1_2]; decide
      have factor_1_4 : (37 : ZMod 358321471201) ^ 27 = 200193881949 := by
        calc
          (37 : ZMod 358321471201) ^ 27 = (37 : ZMod 358321471201) ^ (13 + 13 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 13 * (37 : ZMod 358321471201) ^ 13) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 200193881949 := by rw [factor_1_3]; decide
      have factor_1_5 : (37 : ZMod 358321471201) ^ 55 = 146750769088 := by
        calc
          (37 : ZMod 358321471201) ^ 55 = (37 : ZMod 358321471201) ^ (27 + 27 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 27 * (37 : ZMod 358321471201) ^ 27) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 146750769088 := by rw [factor_1_4]; decide
      have factor_1_6 : (37 : ZMod 358321471201) ^ 111 = 248004166711 := by
        calc
          (37 : ZMod 358321471201) ^ 111 = (37 : ZMod 358321471201) ^ (55 + 55 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 55 * (37 : ZMod 358321471201) ^ 55) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 248004166711 := by rw [factor_1_5]; decide
      have factor_1_7 : (37 : ZMod 358321471201) ^ 222 = 204074240348 := by
        calc
          (37 : ZMod 358321471201) ^ 222 = (37 : ZMod 358321471201) ^ (111 + 111) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 111 * (37 : ZMod 358321471201) ^ 111 := by rw [pow_add]
          _ = 204074240348 := by rw [factor_1_6]; decide
      have factor_1_8 : (37 : ZMod 358321471201) ^ 444 = 217351612595 := by
        calc
          (37 : ZMod 358321471201) ^ 444 = (37 : ZMod 358321471201) ^ (222 + 222) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 222 * (37 : ZMod 358321471201) ^ 222 := by rw [pow_add]
          _ = 217351612595 := by rw [factor_1_7]; decide
      have factor_1_9 : (37 : ZMod 358321471201) ^ 889 = 218842520757 := by
        calc
          (37 : ZMod 358321471201) ^ 889 = (37 : ZMod 358321471201) ^ (444 + 444 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 444 * (37 : ZMod 358321471201) ^ 444) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 218842520757 := by rw [factor_1_8]; decide
      have factor_1_10 : (37 : ZMod 358321471201) ^ 1779 = 206195485413 := by
        calc
          (37 : ZMod 358321471201) ^ 1779 = (37 : ZMod 358321471201) ^ (889 + 889 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 889 * (37 : ZMod 358321471201) ^ 889) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 206195485413 := by rw [factor_1_9]; decide
      have factor_1_11 : (37 : ZMod 358321471201) ^ 3559 = 16056184307 := by
        calc
          (37 : ZMod 358321471201) ^ 3559 = (37 : ZMod 358321471201) ^ (1779 + 1779 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 1779 * (37 : ZMod 358321471201) ^ 1779) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 16056184307 := by rw [factor_1_10]; decide
      have factor_1_12 : (37 : ZMod 358321471201) ^ 7119 = 79780020263 := by
        calc
          (37 : ZMod 358321471201) ^ 7119 = (37 : ZMod 358321471201) ^ (3559 + 3559 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 3559 * (37 : ZMod 358321471201) ^ 3559) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 79780020263 := by rw [factor_1_11]; decide
      have factor_1_13 : (37 : ZMod 358321471201) ^ 14238 = 77226591700 := by
        calc
          (37 : ZMod 358321471201) ^ 14238 = (37 : ZMod 358321471201) ^ (7119 + 7119) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 7119 * (37 : ZMod 358321471201) ^ 7119 := by rw [pow_add]
          _ = 77226591700 := by rw [factor_1_12]; decide
      have factor_1_14 : (37 : ZMod 358321471201) ^ 28476 = 248985113088 := by
        calc
          (37 : ZMod 358321471201) ^ 28476 = (37 : ZMod 358321471201) ^ (14238 + 14238) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 14238 * (37 : ZMod 358321471201) ^ 14238 := by rw [pow_add]
          _ = 248985113088 := by rw [factor_1_13]; decide
      have factor_1_15 : (37 : ZMod 358321471201) ^ 56953 = 27936745020 := by
        calc
          (37 : ZMod 358321471201) ^ 56953 = (37 : ZMod 358321471201) ^ (28476 + 28476 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 28476 * (37 : ZMod 358321471201) ^ 28476) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 27936745020 := by rw [factor_1_14]; decide
      have factor_1_16 : (37 : ZMod 358321471201) ^ 113907 = 12409299786 := by
        calc
          (37 : ZMod 358321471201) ^ 113907 = (37 : ZMod 358321471201) ^ (56953 + 56953 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 56953 * (37 : ZMod 358321471201) ^ 56953) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 12409299786 := by rw [factor_1_15]; decide
      have factor_1_17 : (37 : ZMod 358321471201) ^ 227814 = 340336652423 := by
        calc
          (37 : ZMod 358321471201) ^ 227814 = (37 : ZMod 358321471201) ^ (113907 + 113907) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 113907 * (37 : ZMod 358321471201) ^ 113907 := by rw [pow_add]
          _ = 340336652423 := by rw [factor_1_16]; decide
      have factor_1_18 : (37 : ZMod 358321471201) ^ 455629 = 296819098123 := by
        calc
          (37 : ZMod 358321471201) ^ 455629 = (37 : ZMod 358321471201) ^ (227814 + 227814 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 227814 * (37 : ZMod 358321471201) ^ 227814) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 296819098123 := by rw [factor_1_17]; decide
      have factor_1_19 : (37 : ZMod 358321471201) ^ 911258 = 269579072166 := by
        calc
          (37 : ZMod 358321471201) ^ 911258 = (37 : ZMod 358321471201) ^ (455629 + 455629) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 455629 * (37 : ZMod 358321471201) ^ 455629 := by rw [pow_add]
          _ = 269579072166 := by rw [factor_1_18]; decide
      have factor_1_20 : (37 : ZMod 358321471201) ^ 1822517 = 354062099560 := by
        calc
          (37 : ZMod 358321471201) ^ 1822517 = (37 : ZMod 358321471201) ^ (911258 + 911258 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 911258 * (37 : ZMod 358321471201) ^ 911258) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 354062099560 := by rw [factor_1_19]; decide
      have factor_1_21 : (37 : ZMod 358321471201) ^ 3645034 = 345161490480 := by
        calc
          (37 : ZMod 358321471201) ^ 3645034 = (37 : ZMod 358321471201) ^ (1822517 + 1822517) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 1822517 * (37 : ZMod 358321471201) ^ 1822517 := by rw [pow_add]
          _ = 345161490480 := by rw [factor_1_20]; decide
      have factor_1_22 : (37 : ZMod 358321471201) ^ 7290068 = 304586495807 := by
        calc
          (37 : ZMod 358321471201) ^ 7290068 = (37 : ZMod 358321471201) ^ (3645034 + 3645034) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 3645034 * (37 : ZMod 358321471201) ^ 3645034 := by rw [pow_add]
          _ = 304586495807 := by rw [factor_1_21]; decide
      have factor_1_23 : (37 : ZMod 358321471201) ^ 14580137 = 42967386718 := by
        calc
          (37 : ZMod 358321471201) ^ 14580137 = (37 : ZMod 358321471201) ^ (7290068 + 7290068 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 7290068 * (37 : ZMod 358321471201) ^ 7290068) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 42967386718 := by rw [factor_1_22]; decide
      have factor_1_24 : (37 : ZMod 358321471201) ^ 29160275 = 25352660537 := by
        calc
          (37 : ZMod 358321471201) ^ 29160275 = (37 : ZMod 358321471201) ^ (14580137 + 14580137 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 14580137 * (37 : ZMod 358321471201) ^ 14580137) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 25352660537 := by rw [factor_1_23]; decide
      have factor_1_25 : (37 : ZMod 358321471201) ^ 58320551 = 236120968815 := by
        calc
          (37 : ZMod 358321471201) ^ 58320551 = (37 : ZMod 358321471201) ^ (29160275 + 29160275 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 29160275 * (37 : ZMod 358321471201) ^ 29160275) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 236120968815 := by rw [factor_1_24]; decide
      have factor_1_26 : (37 : ZMod 358321471201) ^ 116641103 = 201655208443 := by
        calc
          (37 : ZMod 358321471201) ^ 116641103 = (37 : ZMod 358321471201) ^ (58320551 + 58320551 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 58320551 * (37 : ZMod 358321471201) ^ 58320551) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 201655208443 := by rw [factor_1_25]; decide
      have factor_1_27 : (37 : ZMod 358321471201) ^ 233282207 = 350941210024 := by
        calc
          (37 : ZMod 358321471201) ^ 233282207 = (37 : ZMod 358321471201) ^ (116641103 + 116641103 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 116641103 * (37 : ZMod 358321471201) ^ 116641103) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 350941210024 := by rw [factor_1_26]; decide
      have factor_1_28 : (37 : ZMod 358321471201) ^ 466564415 = 85105502978 := by
        calc
          (37 : ZMod 358321471201) ^ 466564415 = (37 : ZMod 358321471201) ^ (233282207 + 233282207 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 233282207 * (37 : ZMod 358321471201) ^ 233282207) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 85105502978 := by rw [factor_1_27]; decide
      have factor_1_29 : (37 : ZMod 358321471201) ^ 933128831 = 117947422831 := by
        calc
          (37 : ZMod 358321471201) ^ 933128831 = (37 : ZMod 358321471201) ^ (466564415 + 466564415 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 466564415 * (37 : ZMod 358321471201) ^ 466564415) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 117947422831 := by rw [factor_1_28]; decide
      have factor_1_30 : (37 : ZMod 358321471201) ^ 1866257662 = 156055195570 := by
        calc
          (37 : ZMod 358321471201) ^ 1866257662 = (37 : ZMod 358321471201) ^ (933128831 + 933128831) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 933128831 * (37 : ZMod 358321471201) ^ 933128831 := by rw [pow_add]
          _ = 156055195570 := by rw [factor_1_29]; decide
      have factor_1_31 : (37 : ZMod 358321471201) ^ 3732515325 = 60473117012 := by
        calc
          (37 : ZMod 358321471201) ^ 3732515325 = (37 : ZMod 358321471201) ^ (1866257662 + 1866257662 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 1866257662 * (37 : ZMod 358321471201) ^ 1866257662) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 60473117012 := by rw [factor_1_30]; decide
      have factor_1_32 : (37 : ZMod 358321471201) ^ 7465030650 = 358260914010 := by
        calc
          (37 : ZMod 358321471201) ^ 7465030650 = (37 : ZMod 358321471201) ^ (3732515325 + 3732515325) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 3732515325 * (37 : ZMod 358321471201) ^ 3732515325 := by rw [pow_add]
          _ = 358260914010 := by rw [factor_1_31]; decide
      have factor_1_33 : (37 : ZMod 358321471201) ^ 14930061300 = 111445539447 := by
        calc
          (37 : ZMod 358321471201) ^ 14930061300 = (37 : ZMod 358321471201) ^ (7465030650 + 7465030650) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 7465030650 * (37 : ZMod 358321471201) ^ 7465030650 := by rw [pow_add]
          _ = 111445539447 := by rw [factor_1_32]; decide
      have factor_1_34 : (37 : ZMod 358321471201) ^ 29860122600 = 210015406330 := by
        calc
          (37 : ZMod 358321471201) ^ 29860122600 = (37 : ZMod 358321471201) ^ (14930061300 + 14930061300) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 14930061300 * (37 : ZMod 358321471201) ^ 14930061300 := by rw [pow_add]
          _ = 210015406330 := by rw [factor_1_33]; decide
      have factor_1_35 : (37 : ZMod 358321471201) ^ 59720245200 = 101751835556 := by
        calc
          (37 : ZMod 358321471201) ^ 59720245200 = (37 : ZMod 358321471201) ^ (29860122600 + 29860122600) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 29860122600 * (37 : ZMod 358321471201) ^ 29860122600 := by rw [pow_add]
          _ = 101751835556 := by rw [factor_1_34]; decide
      have factor_1_36 : (37 : ZMod 358321471201) ^ 119440490400 = 101751835555 := by
        calc
          (37 : ZMod 358321471201) ^ 119440490400 = (37 : ZMod 358321471201) ^ (59720245200 + 59720245200) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 59720245200 * (37 : ZMod 358321471201) ^ 59720245200 := by rw [pow_add]
          _ = 101751835555 := by rw [factor_1_35]; decide
      change (37 : ZMod 358321471201) ^ 119440490400 ≠ 1
      rw [factor_1_36]
      decide
    ·
      have factor_2_0 : (37 : ZMod 358321471201) ^ 1 = 37 := by norm_num
      have factor_2_1 : (37 : ZMod 358321471201) ^ 2 = 1369 := by
        calc
          (37 : ZMod 358321471201) ^ 2 = (37 : ZMod 358321471201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 1 * (37 : ZMod 358321471201) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_2_0]; decide
      have factor_2_2 : (37 : ZMod 358321471201) ^ 4 = 1874161 := by
        calc
          (37 : ZMod 358321471201) ^ 4 = (37 : ZMod 358321471201) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 2 * (37 : ZMod 358321471201) ^ 2 := by rw [pow_add]
          _ = 1874161 := by rw [factor_2_1]; decide
      have factor_2_3 : (37 : ZMod 358321471201) ^ 8 = 287586213112 := by
        calc
          (37 : ZMod 358321471201) ^ 8 = (37 : ZMod 358321471201) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 4 * (37 : ZMod 358321471201) ^ 4 := by rw [pow_add]
          _ = 287586213112 := by rw [factor_2_2]; decide
      have factor_2_4 : (37 : ZMod 358321471201) ^ 16 = 93855239580 := by
        calc
          (37 : ZMod 358321471201) ^ 16 = (37 : ZMod 358321471201) ^ (8 + 8) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 8 * (37 : ZMod 358321471201) ^ 8 := by rw [pow_add]
          _ = 93855239580 := by rw [factor_2_3]; decide
      have factor_2_5 : (37 : ZMod 358321471201) ^ 33 = 236036113317 := by
        calc
          (37 : ZMod 358321471201) ^ 33 = (37 : ZMod 358321471201) ^ (16 + 16 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 16 * (37 : ZMod 358321471201) ^ 16) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 236036113317 := by rw [factor_2_4]; decide
      have factor_2_6 : (37 : ZMod 358321471201) ^ 66 = 290833465314 := by
        calc
          (37 : ZMod 358321471201) ^ 66 = (37 : ZMod 358321471201) ^ (33 + 33) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 33 * (37 : ZMod 358321471201) ^ 33 := by rw [pow_add]
          _ = 290833465314 := by rw [factor_2_5]; decide
      have factor_2_7 : (37 : ZMod 358321471201) ^ 133 = 305489512341 := by
        calc
          (37 : ZMod 358321471201) ^ 133 = (37 : ZMod 358321471201) ^ (66 + 66 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 66 * (37 : ZMod 358321471201) ^ 66) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 305489512341 := by rw [factor_2_6]; decide
      have factor_2_8 : (37 : ZMod 358321471201) ^ 266 = 332586964477 := by
        calc
          (37 : ZMod 358321471201) ^ 266 = (37 : ZMod 358321471201) ^ (133 + 133) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 133 * (37 : ZMod 358321471201) ^ 133 := by rw [pow_add]
          _ = 332586964477 := by rw [factor_2_7]; decide
      have factor_2_9 : (37 : ZMod 358321471201) ^ 533 = 290449681595 := by
        calc
          (37 : ZMod 358321471201) ^ 533 = (37 : ZMod 358321471201) ^ (266 + 266 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 266 * (37 : ZMod 358321471201) ^ 266) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 290449681595 := by rw [factor_2_8]; decide
      have factor_2_10 : (37 : ZMod 358321471201) ^ 1067 = 39953668766 := by
        calc
          (37 : ZMod 358321471201) ^ 1067 = (37 : ZMod 358321471201) ^ (533 + 533 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 533 * (37 : ZMod 358321471201) ^ 533) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 39953668766 := by rw [factor_2_9]; decide
      have factor_2_11 : (37 : ZMod 358321471201) ^ 2135 = 347905538997 := by
        calc
          (37 : ZMod 358321471201) ^ 2135 = (37 : ZMod 358321471201) ^ (1067 + 1067 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 1067 * (37 : ZMod 358321471201) ^ 1067) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 347905538997 := by rw [factor_2_10]; decide
      have factor_2_12 : (37 : ZMod 358321471201) ^ 4271 = 90013965565 := by
        calc
          (37 : ZMod 358321471201) ^ 4271 = (37 : ZMod 358321471201) ^ (2135 + 2135 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 2135 * (37 : ZMod 358321471201) ^ 2135) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 90013965565 := by rw [factor_2_11]; decide
      have factor_2_13 : (37 : ZMod 358321471201) ^ 8543 = 317942775065 := by
        calc
          (37 : ZMod 358321471201) ^ 8543 = (37 : ZMod 358321471201) ^ (4271 + 4271 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 4271 * (37 : ZMod 358321471201) ^ 4271) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 317942775065 := by rw [factor_2_12]; decide
      have factor_2_14 : (37 : ZMod 358321471201) ^ 17086 = 283316842859 := by
        calc
          (37 : ZMod 358321471201) ^ 17086 = (37 : ZMod 358321471201) ^ (8543 + 8543) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 8543 * (37 : ZMod 358321471201) ^ 8543 := by rw [pow_add]
          _ = 283316842859 := by rw [factor_2_13]; decide
      have factor_2_15 : (37 : ZMod 358321471201) ^ 34172 = 52558701309 := by
        calc
          (37 : ZMod 358321471201) ^ 34172 = (37 : ZMod 358321471201) ^ (17086 + 17086) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 17086 * (37 : ZMod 358321471201) ^ 17086 := by rw [pow_add]
          _ = 52558701309 := by rw [factor_2_14]; decide
      have factor_2_16 : (37 : ZMod 358321471201) ^ 68344 = 268837704145 := by
        calc
          (37 : ZMod 358321471201) ^ 68344 = (37 : ZMod 358321471201) ^ (34172 + 34172) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 34172 * (37 : ZMod 358321471201) ^ 34172 := by rw [pow_add]
          _ = 268837704145 := by rw [factor_2_15]; decide
      have factor_2_17 : (37 : ZMod 358321471201) ^ 136688 = 273641545516 := by
        calc
          (37 : ZMod 358321471201) ^ 136688 = (37 : ZMod 358321471201) ^ (68344 + 68344) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 68344 * (37 : ZMod 358321471201) ^ 68344 := by rw [pow_add]
          _ = 273641545516 := by rw [factor_2_16]; decide
      have factor_2_18 : (37 : ZMod 358321471201) ^ 273377 = 4029166725 := by
        calc
          (37 : ZMod 358321471201) ^ 273377 = (37 : ZMod 358321471201) ^ (136688 + 136688 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 136688 * (37 : ZMod 358321471201) ^ 136688) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 4029166725 := by rw [factor_2_17]; decide
      have factor_2_19 : (37 : ZMod 358321471201) ^ 546755 = 278499487499 := by
        calc
          (37 : ZMod 358321471201) ^ 546755 = (37 : ZMod 358321471201) ^ (273377 + 273377 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 273377 * (37 : ZMod 358321471201) ^ 273377) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 278499487499 := by rw [factor_2_18]; decide
      have factor_2_20 : (37 : ZMod 358321471201) ^ 1093510 = 68735747361 := by
        calc
          (37 : ZMod 358321471201) ^ 1093510 = (37 : ZMod 358321471201) ^ (546755 + 546755) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 546755 * (37 : ZMod 358321471201) ^ 546755 := by rw [pow_add]
          _ = 68735747361 := by rw [factor_2_19]; decide
      have factor_2_21 : (37 : ZMod 358321471201) ^ 2187020 = 163226330130 := by
        calc
          (37 : ZMod 358321471201) ^ 2187020 = (37 : ZMod 358321471201) ^ (1093510 + 1093510) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 1093510 * (37 : ZMod 358321471201) ^ 1093510 := by rw [pow_add]
          _ = 163226330130 := by rw [factor_2_20]; decide
      have factor_2_22 : (37 : ZMod 358321471201) ^ 4374041 = 192555650271 := by
        calc
          (37 : ZMod 358321471201) ^ 4374041 = (37 : ZMod 358321471201) ^ (2187020 + 2187020 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 2187020 * (37 : ZMod 358321471201) ^ 2187020) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 192555650271 := by rw [factor_2_21]; decide
      have factor_2_23 : (37 : ZMod 358321471201) ^ 8748082 = 38213347383 := by
        calc
          (37 : ZMod 358321471201) ^ 8748082 = (37 : ZMod 358321471201) ^ (4374041 + 4374041) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 4374041 * (37 : ZMod 358321471201) ^ 4374041 := by rw [pow_add]
          _ = 38213347383 := by rw [factor_2_22]; decide
      have factor_2_24 : (37 : ZMod 358321471201) ^ 17496165 = 165943078714 := by
        calc
          (37 : ZMod 358321471201) ^ 17496165 = (37 : ZMod 358321471201) ^ (8748082 + 8748082 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 8748082 * (37 : ZMod 358321471201) ^ 8748082) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 165943078714 := by rw [factor_2_23]; decide
      have factor_2_25 : (37 : ZMod 358321471201) ^ 34992331 = 58229013186 := by
        calc
          (37 : ZMod 358321471201) ^ 34992331 = (37 : ZMod 358321471201) ^ (17496165 + 17496165 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 17496165 * (37 : ZMod 358321471201) ^ 17496165) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 58229013186 := by rw [factor_2_24]; decide
      have factor_2_26 : (37 : ZMod 358321471201) ^ 69984662 = 119166683651 := by
        calc
          (37 : ZMod 358321471201) ^ 69984662 = (37 : ZMod 358321471201) ^ (34992331 + 34992331) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 34992331 * (37 : ZMod 358321471201) ^ 34992331 := by rw [pow_add]
          _ = 119166683651 := by rw [factor_2_25]; decide
      have factor_2_27 : (37 : ZMod 358321471201) ^ 139969324 = 47473980008 := by
        calc
          (37 : ZMod 358321471201) ^ 139969324 = (37 : ZMod 358321471201) ^ (69984662 + 69984662) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 69984662 * (37 : ZMod 358321471201) ^ 69984662 := by rw [pow_add]
          _ = 47473980008 := by rw [factor_2_26]; decide
      have factor_2_28 : (37 : ZMod 358321471201) ^ 279938649 = 77093690605 := by
        calc
          (37 : ZMod 358321471201) ^ 279938649 = (37 : ZMod 358321471201) ^ (139969324 + 139969324 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 139969324 * (37 : ZMod 358321471201) ^ 139969324) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 77093690605 := by rw [factor_2_27]; decide
      have factor_2_29 : (37 : ZMod 358321471201) ^ 559877298 = 302476512760 := by
        calc
          (37 : ZMod 358321471201) ^ 559877298 = (37 : ZMod 358321471201) ^ (279938649 + 279938649) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 279938649 * (37 : ZMod 358321471201) ^ 279938649 := by rw [pow_add]
          _ = 302476512760 := by rw [factor_2_28]; decide
      have factor_2_30 : (37 : ZMod 358321471201) ^ 1119754597 = 254685151161 := by
        calc
          (37 : ZMod 358321471201) ^ 1119754597 = (37 : ZMod 358321471201) ^ (559877298 + 559877298 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 559877298 * (37 : ZMod 358321471201) ^ 559877298) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 254685151161 := by rw [factor_2_29]; decide
      have factor_2_31 : (37 : ZMod 358321471201) ^ 2239509195 = 88460065842 := by
        calc
          (37 : ZMod 358321471201) ^ 2239509195 = (37 : ZMod 358321471201) ^ (1119754597 + 1119754597 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 1119754597 * (37 : ZMod 358321471201) ^ 1119754597) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 88460065842 := by rw [factor_2_30]; decide
      have factor_2_32 : (37 : ZMod 358321471201) ^ 4479018390 = 320875625339 := by
        calc
          (37 : ZMod 358321471201) ^ 4479018390 = (37 : ZMod 358321471201) ^ (2239509195 + 2239509195) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 2239509195 * (37 : ZMod 358321471201) ^ 2239509195 := by rw [pow_add]
          _ = 320875625339 := by rw [factor_2_31]; decide
      have factor_2_33 : (37 : ZMod 358321471201) ^ 8958036780 = 233160999701 := by
        calc
          (37 : ZMod 358321471201) ^ 8958036780 = (37 : ZMod 358321471201) ^ (4479018390 + 4479018390) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 4479018390 * (37 : ZMod 358321471201) ^ 4479018390 := by rw [pow_add]
          _ = 233160999701 := by rw [factor_2_32]; decide
      have factor_2_34 : (37 : ZMod 358321471201) ^ 17916073560 = 103182534885 := by
        calc
          (37 : ZMod 358321471201) ^ 17916073560 = (37 : ZMod 358321471201) ^ (8958036780 + 8958036780) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 8958036780 * (37 : ZMod 358321471201) ^ 8958036780 := by rw [pow_add]
          _ = 103182534885 := by rw [factor_2_33]; decide
      have factor_2_35 : (37 : ZMod 358321471201) ^ 35832147120 = 100590604288 := by
        calc
          (37 : ZMod 358321471201) ^ 35832147120 = (37 : ZMod 358321471201) ^ (17916073560 + 17916073560) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 17916073560 * (37 : ZMod 358321471201) ^ 17916073560 := by rw [pow_add]
          _ = 100590604288 := by rw [factor_2_34]; decide
      have factor_2_36 : (37 : ZMod 358321471201) ^ 71664294240 = 48767779967 := by
        calc
          (37 : ZMod 358321471201) ^ 71664294240 = (37 : ZMod 358321471201) ^ (35832147120 + 35832147120) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 35832147120 * (37 : ZMod 358321471201) ^ 35832147120 := by rw [pow_add]
          _ = 48767779967 := by rw [factor_2_35]; decide
      change (37 : ZMod 358321471201) ^ 71664294240 ≠ 1
      rw [factor_2_36]
      decide
    ·
      have factor_3_0 : (37 : ZMod 358321471201) ^ 1 = 37 := by norm_num
      have factor_3_1 : (37 : ZMod 358321471201) ^ 2 = 1369 := by
        calc
          (37 : ZMod 358321471201) ^ 2 = (37 : ZMod 358321471201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 1 * (37 : ZMod 358321471201) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_3_0]; decide
      have factor_3_2 : (37 : ZMod 358321471201) ^ 5 = 69343957 := by
        calc
          (37 : ZMod 358321471201) ^ 5 = (37 : ZMod 358321471201) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 2 * (37 : ZMod 358321471201) ^ 2) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 69343957 := by rw [factor_3_1]; decide
      have factor_3_3 : (37 : ZMod 358321471201) ^ 11 = 261684027883 := by
        calc
          (37 : ZMod 358321471201) ^ 11 = (37 : ZMod 358321471201) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 5 * (37 : ZMod 358321471201) ^ 5) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 261684027883 := by rw [factor_3_2]; decide
      have factor_3_4 : (37 : ZMod 358321471201) ^ 23 = 238394189563 := by
        calc
          (37 : ZMod 358321471201) ^ 23 = (37 : ZMod 358321471201) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 11 * (37 : ZMod 358321471201) ^ 11) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 238394189563 := by rw [factor_3_3]; decide
      have factor_3_5 : (37 : ZMod 358321471201) ^ 47 = 24035438531 := by
        calc
          (37 : ZMod 358321471201) ^ 47 = (37 : ZMod 358321471201) ^ (23 + 23 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 23 * (37 : ZMod 358321471201) ^ 23) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 24035438531 := by rw [factor_3_4]; decide
      have factor_3_6 : (37 : ZMod 358321471201) ^ 95 = 108158250459 := by
        calc
          (37 : ZMod 358321471201) ^ 95 = (37 : ZMod 358321471201) ^ (47 + 47 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 47 * (37 : ZMod 358321471201) ^ 47) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 108158250459 := by rw [factor_3_5]; decide
      have factor_3_7 : (37 : ZMod 358321471201) ^ 190 = 10450989672 := by
        calc
          (37 : ZMod 358321471201) ^ 190 = (37 : ZMod 358321471201) ^ (95 + 95) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 95 * (37 : ZMod 358321471201) ^ 95 := by rw [pow_add]
          _ = 10450989672 := by rw [factor_3_6]; decide
      have factor_3_8 : (37 : ZMod 358321471201) ^ 381 = 102548266373 := by
        calc
          (37 : ZMod 358321471201) ^ 381 = (37 : ZMod 358321471201) ^ (190 + 190 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 190 * (37 : ZMod 358321471201) ^ 190) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 102548266373 := by rw [factor_3_7]; decide
      have factor_3_9 : (37 : ZMod 358321471201) ^ 762 = 176431764794 := by
        calc
          (37 : ZMod 358321471201) ^ 762 = (37 : ZMod 358321471201) ^ (381 + 381) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 381 * (37 : ZMod 358321471201) ^ 381 := by rw [pow_add]
          _ = 176431764794 := by rw [factor_3_8]; decide
      have factor_3_10 : (37 : ZMod 358321471201) ^ 1525 = 101451144777 := by
        calc
          (37 : ZMod 358321471201) ^ 1525 = (37 : ZMod 358321471201) ^ (762 + 762 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 762 * (37 : ZMod 358321471201) ^ 762) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 101451144777 := by rw [factor_3_9]; decide
      have factor_3_11 : (37 : ZMod 358321471201) ^ 3051 = 288780742514 := by
        calc
          (37 : ZMod 358321471201) ^ 3051 = (37 : ZMod 358321471201) ^ (1525 + 1525 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 1525 * (37 : ZMod 358321471201) ^ 1525) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 288780742514 := by rw [factor_3_10]; decide
      have factor_3_12 : (37 : ZMod 358321471201) ^ 6102 = 34490790189 := by
        calc
          (37 : ZMod 358321471201) ^ 6102 = (37 : ZMod 358321471201) ^ (3051 + 3051) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 3051 * (37 : ZMod 358321471201) ^ 3051 := by rw [pow_add]
          _ = 34490790189 := by rw [factor_3_11]; decide
      have factor_3_13 : (37 : ZMod 358321471201) ^ 12204 = 171306804699 := by
        calc
          (37 : ZMod 358321471201) ^ 12204 = (37 : ZMod 358321471201) ^ (6102 + 6102) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 6102 * (37 : ZMod 358321471201) ^ 6102 := by rw [pow_add]
          _ = 171306804699 := by rw [factor_3_12]; decide
      have factor_3_14 : (37 : ZMod 358321471201) ^ 24408 = 130193412765 := by
        calc
          (37 : ZMod 358321471201) ^ 24408 = (37 : ZMod 358321471201) ^ (12204 + 12204) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 12204 * (37 : ZMod 358321471201) ^ 12204 := by rw [pow_add]
          _ = 130193412765 := by rw [factor_3_13]; decide
      have factor_3_15 : (37 : ZMod 358321471201) ^ 48817 = 57385035491 := by
        calc
          (37 : ZMod 358321471201) ^ 48817 = (37 : ZMod 358321471201) ^ (24408 + 24408 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 24408 * (37 : ZMod 358321471201) ^ 24408) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 57385035491 := by rw [factor_3_14]; decide
      have factor_3_16 : (37 : ZMod 358321471201) ^ 97634 = 83195126969 := by
        calc
          (37 : ZMod 358321471201) ^ 97634 = (37 : ZMod 358321471201) ^ (48817 + 48817) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 48817 * (37 : ZMod 358321471201) ^ 48817 := by rw [pow_add]
          _ = 83195126969 := by rw [factor_3_15]; decide
      have factor_3_17 : (37 : ZMod 358321471201) ^ 195269 = 62321499200 := by
        calc
          (37 : ZMod 358321471201) ^ 195269 = (37 : ZMod 358321471201) ^ (97634 + 97634 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 97634 * (37 : ZMod 358321471201) ^ 97634) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 62321499200 := by rw [factor_3_16]; decide
      have factor_3_18 : (37 : ZMod 358321471201) ^ 390539 = 163511332030 := by
        calc
          (37 : ZMod 358321471201) ^ 390539 = (37 : ZMod 358321471201) ^ (195269 + 195269 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 195269 * (37 : ZMod 358321471201) ^ 195269) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 163511332030 := by rw [factor_3_17]; decide
      have factor_3_19 : (37 : ZMod 358321471201) ^ 781078 = 354150960691 := by
        calc
          (37 : ZMod 358321471201) ^ 781078 = (37 : ZMod 358321471201) ^ (390539 + 390539) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 390539 * (37 : ZMod 358321471201) ^ 390539 := by rw [pow_add]
          _ = 354150960691 := by rw [factor_3_18]; decide
      have factor_3_20 : (37 : ZMod 358321471201) ^ 1562157 = 315763492369 := by
        calc
          (37 : ZMod 358321471201) ^ 1562157 = (37 : ZMod 358321471201) ^ (781078 + 781078 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 781078 * (37 : ZMod 358321471201) ^ 781078) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 315763492369 := by rw [factor_3_19]; decide
      have factor_3_21 : (37 : ZMod 358321471201) ^ 3124315 = 176422657979 := by
        calc
          (37 : ZMod 358321471201) ^ 3124315 = (37 : ZMod 358321471201) ^ (1562157 + 1562157 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 1562157 * (37 : ZMod 358321471201) ^ 1562157) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 176422657979 := by rw [factor_3_20]; decide
      have factor_3_22 : (37 : ZMod 358321471201) ^ 6248630 = 201815362717 := by
        calc
          (37 : ZMod 358321471201) ^ 6248630 = (37 : ZMod 358321471201) ^ (3124315 + 3124315) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 3124315 * (37 : ZMod 358321471201) ^ 3124315 := by rw [pow_add]
          _ = 201815362717 := by rw [factor_3_21]; decide
      have factor_3_23 : (37 : ZMod 358321471201) ^ 12497261 = 109640726507 := by
        calc
          (37 : ZMod 358321471201) ^ 12497261 = (37 : ZMod 358321471201) ^ (6248630 + 6248630 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 6248630 * (37 : ZMod 358321471201) ^ 6248630) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 109640726507 := by rw [factor_3_22]; decide
      have factor_3_24 : (37 : ZMod 358321471201) ^ 24994522 = 285575056016 := by
        calc
          (37 : ZMod 358321471201) ^ 24994522 = (37 : ZMod 358321471201) ^ (12497261 + 12497261) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 12497261 * (37 : ZMod 358321471201) ^ 12497261 := by rw [pow_add]
          _ = 285575056016 := by rw [factor_3_23]; decide
      have factor_3_25 : (37 : ZMod 358321471201) ^ 49989044 = 114993897824 := by
        calc
          (37 : ZMod 358321471201) ^ 49989044 = (37 : ZMod 358321471201) ^ (24994522 + 24994522) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 24994522 * (37 : ZMod 358321471201) ^ 24994522 := by rw [pow_add]
          _ = 114993897824 := by rw [factor_3_24]; decide
      have factor_3_26 : (37 : ZMod 358321471201) ^ 99978089 = 55406735893 := by
        calc
          (37 : ZMod 358321471201) ^ 99978089 = (37 : ZMod 358321471201) ^ (49989044 + 49989044 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 49989044 * (37 : ZMod 358321471201) ^ 49989044) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 55406735893 := by rw [factor_3_25]; decide
      have factor_3_27 : (37 : ZMod 358321471201) ^ 199956178 = 335933935234 := by
        calc
          (37 : ZMod 358321471201) ^ 199956178 = (37 : ZMod 358321471201) ^ (99978089 + 99978089) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 99978089 * (37 : ZMod 358321471201) ^ 99978089 := by rw [pow_add]
          _ = 335933935234 := by rw [factor_3_26]; decide
      have factor_3_28 : (37 : ZMod 358321471201) ^ 399912356 = 118366426581 := by
        calc
          (37 : ZMod 358321471201) ^ 399912356 = (37 : ZMod 358321471201) ^ (199956178 + 199956178) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 199956178 * (37 : ZMod 358321471201) ^ 199956178 := by rw [pow_add]
          _ = 118366426581 := by rw [factor_3_27]; decide
      have factor_3_29 : (37 : ZMod 358321471201) ^ 799824712 = 296549031816 := by
        calc
          (37 : ZMod 358321471201) ^ 799824712 = (37 : ZMod 358321471201) ^ (399912356 + 399912356) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 399912356 * (37 : ZMod 358321471201) ^ 399912356 := by rw [pow_add]
          _ = 296549031816 := by rw [factor_3_28]; decide
      have factor_3_30 : (37 : ZMod 358321471201) ^ 1599649425 = 52474552821 := by
        calc
          (37 : ZMod 358321471201) ^ 1599649425 = (37 : ZMod 358321471201) ^ (799824712 + 799824712 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 799824712 * (37 : ZMod 358321471201) ^ 799824712) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 52474552821 := by rw [factor_3_29]; decide
      have factor_3_31 : (37 : ZMod 358321471201) ^ 3199298850 = 43333251594 := by
        calc
          (37 : ZMod 358321471201) ^ 3199298850 = (37 : ZMod 358321471201) ^ (1599649425 + 1599649425) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 1599649425 * (37 : ZMod 358321471201) ^ 1599649425 := by rw [pow_add]
          _ = 43333251594 := by rw [factor_3_30]; decide
      have factor_3_32 : (37 : ZMod 358321471201) ^ 6398597700 = 133821113850 := by
        calc
          (37 : ZMod 358321471201) ^ 6398597700 = (37 : ZMod 358321471201) ^ (3199298850 + 3199298850) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 3199298850 * (37 : ZMod 358321471201) ^ 3199298850 := by rw [pow_add]
          _ = 133821113850 := by rw [factor_3_31]; decide
      have factor_3_33 : (37 : ZMod 358321471201) ^ 12797195400 = 3085084711 := by
        calc
          (37 : ZMod 358321471201) ^ 12797195400 = (37 : ZMod 358321471201) ^ (6398597700 + 6398597700) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 6398597700 * (37 : ZMod 358321471201) ^ 6398597700 := by rw [pow_add]
          _ = 3085084711 := by rw [factor_3_32]; decide
      have factor_3_34 : (37 : ZMod 358321471201) ^ 25594390800 = 214753499486 := by
        calc
          (37 : ZMod 358321471201) ^ 25594390800 = (37 : ZMod 358321471201) ^ (12797195400 + 12797195400) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 12797195400 * (37 : ZMod 358321471201) ^ 12797195400 := by rw [pow_add]
          _ = 214753499486 := by rw [factor_3_33]; decide
      have factor_3_35 : (37 : ZMod 358321471201) ^ 51188781600 = 72715774521 := by
        calc
          (37 : ZMod 358321471201) ^ 51188781600 = (37 : ZMod 358321471201) ^ (25594390800 + 25594390800) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 25594390800 * (37 : ZMod 358321471201) ^ 25594390800 := by rw [pow_add]
          _ = 72715774521 := by rw [factor_3_34]; decide
      change (37 : ZMod 358321471201) ^ 51188781600 ≠ 1
      rw [factor_3_35]
      decide
    ·
      have factor_4_0 : (37 : ZMod 358321471201) ^ 1 = 37 := by norm_num
      have factor_4_1 : (37 : ZMod 358321471201) ^ 3 = 50653 := by
        calc
          (37 : ZMod 358321471201) ^ 3 = (37 : ZMod 358321471201) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 1 * (37 : ZMod 358321471201) ^ 1) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 50653 := by rw [factor_4_0]; decide
      have factor_4_2 : (37 : ZMod 358321471201) ^ 7 = 94931877133 := by
        calc
          (37 : ZMod 358321471201) ^ 7 = (37 : ZMod 358321471201) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 3 * (37 : ZMod 358321471201) ^ 3) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 94931877133 := by rw [factor_4_1]; decide
      have factor_4_3 : (37 : ZMod 358321471201) ^ 15 = 176855181654 := by
        calc
          (37 : ZMod 358321471201) ^ 15 = (37 : ZMod 358321471201) ^ (7 + 7 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 7 * (37 : ZMod 358321471201) ^ 7) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 176855181654 := by rw [factor_4_2]; decide
      have factor_4_4 : (37 : ZMod 358321471201) ^ 30 = 281388845598 := by
        calc
          (37 : ZMod 358321471201) ^ 30 = (37 : ZMod 358321471201) ^ (15 + 15) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 15 * (37 : ZMod 358321471201) ^ 15 := by rw [pow_add]
          _ = 281388845598 := by rw [factor_4_3]; decide
      have factor_4_5 : (37 : ZMod 358321471201) ^ 60 = 120895711758 := by
        calc
          (37 : ZMod 358321471201) ^ 60 = (37 : ZMod 358321471201) ^ (30 + 30) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 30 * (37 : ZMod 358321471201) ^ 30 := by rw [pow_add]
          _ = 120895711758 := by rw [factor_4_4]; decide
      have factor_4_6 : (37 : ZMod 358321471201) ^ 121 = 190830524213 := by
        calc
          (37 : ZMod 358321471201) ^ 121 = (37 : ZMod 358321471201) ^ (60 + 60 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 60 * (37 : ZMod 358321471201) ^ 60) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 190830524213 := by rw [factor_4_5]; decide
      have factor_4_7 : (37 : ZMod 358321471201) ^ 242 = 28058485697 := by
        calc
          (37 : ZMod 358321471201) ^ 242 = (37 : ZMod 358321471201) ^ (121 + 121) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 121 * (37 : ZMod 358321471201) ^ 121 := by rw [pow_add]
          _ = 28058485697 := by rw [factor_4_6]; decide
      have factor_4_8 : (37 : ZMod 358321471201) ^ 485 = 318848386339 := by
        calc
          (37 : ZMod 358321471201) ^ 485 = (37 : ZMod 358321471201) ^ (242 + 242 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 242 * (37 : ZMod 358321471201) ^ 242) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 318848386339 := by rw [factor_4_7]; decide
      have factor_4_9 : (37 : ZMod 358321471201) ^ 970 = 313803341678 := by
        calc
          (37 : ZMod 358321471201) ^ 970 = (37 : ZMod 358321471201) ^ (485 + 485) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 485 * (37 : ZMod 358321471201) ^ 485 := by rw [pow_add]
          _ = 313803341678 := by rw [factor_4_8]; decide
      have factor_4_10 : (37 : ZMod 358321471201) ^ 1941 = 193623326438 := by
        calc
          (37 : ZMod 358321471201) ^ 1941 = (37 : ZMod 358321471201) ^ (970 + 970 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 970 * (37 : ZMod 358321471201) ^ 970) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 193623326438 := by rw [factor_4_9]; decide
      have factor_4_11 : (37 : ZMod 358321471201) ^ 3883 = 252947927355 := by
        calc
          (37 : ZMod 358321471201) ^ 3883 = (37 : ZMod 358321471201) ^ (1941 + 1941 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 1941 * (37 : ZMod 358321471201) ^ 1941) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 252947927355 := by rw [factor_4_10]; decide
      have factor_4_12 : (37 : ZMod 358321471201) ^ 7766 = 331802888581 := by
        calc
          (37 : ZMod 358321471201) ^ 7766 = (37 : ZMod 358321471201) ^ (3883 + 3883) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 3883 * (37 : ZMod 358321471201) ^ 3883 := by rw [pow_add]
          _ = 331802888581 := by rw [factor_4_11]; decide
      have factor_4_13 : (37 : ZMod 358321471201) ^ 15532 = 87991924927 := by
        calc
          (37 : ZMod 358321471201) ^ 15532 = (37 : ZMod 358321471201) ^ (7766 + 7766) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 7766 * (37 : ZMod 358321471201) ^ 7766 := by rw [pow_add]
          _ = 87991924927 := by rw [factor_4_12]; decide
      have factor_4_14 : (37 : ZMod 358321471201) ^ 31065 = 205734181166 := by
        calc
          (37 : ZMod 358321471201) ^ 31065 = (37 : ZMod 358321471201) ^ (15532 + 15532 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 15532 * (37 : ZMod 358321471201) ^ 15532) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 205734181166 := by rw [factor_4_13]; decide
      have factor_4_15 : (37 : ZMod 358321471201) ^ 62131 = 202743779782 := by
        calc
          (37 : ZMod 358321471201) ^ 62131 = (37 : ZMod 358321471201) ^ (31065 + 31065 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 31065 * (37 : ZMod 358321471201) ^ 31065) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 202743779782 := by rw [factor_4_14]; decide
      have factor_4_16 : (37 : ZMod 358321471201) ^ 124262 = 222724833819 := by
        calc
          (37 : ZMod 358321471201) ^ 124262 = (37 : ZMod 358321471201) ^ (62131 + 62131) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 62131 * (37 : ZMod 358321471201) ^ 62131 := by rw [pow_add]
          _ = 222724833819 := by rw [factor_4_15]; decide
      have factor_4_17 : (37 : ZMod 358321471201) ^ 248525 = 48996073312 := by
        calc
          (37 : ZMod 358321471201) ^ 248525 = (37 : ZMod 358321471201) ^ (124262 + 124262 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 124262 * (37 : ZMod 358321471201) ^ 124262) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 48996073312 := by rw [factor_4_16]; decide
      have factor_4_18 : (37 : ZMod 358321471201) ^ 497050 = 99639001907 := by
        calc
          (37 : ZMod 358321471201) ^ 497050 = (37 : ZMod 358321471201) ^ (248525 + 248525) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 248525 * (37 : ZMod 358321471201) ^ 248525 := by rw [pow_add]
          _ = 99639001907 := by rw [factor_4_17]; decide
      have factor_4_19 : (37 : ZMod 358321471201) ^ 994100 = 240798380736 := by
        calc
          (37 : ZMod 358321471201) ^ 994100 = (37 : ZMod 358321471201) ^ (497050 + 497050) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 497050 * (37 : ZMod 358321471201) ^ 497050 := by rw [pow_add]
          _ = 240798380736 := by rw [factor_4_18]; decide
      have factor_4_20 : (37 : ZMod 358321471201) ^ 1988200 = 343020537126 := by
        calc
          (37 : ZMod 358321471201) ^ 1988200 = (37 : ZMod 358321471201) ^ (994100 + 994100) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 994100 * (37 : ZMod 358321471201) ^ 994100 := by rw [pow_add]
          _ = 343020537126 := by rw [factor_4_19]; decide
      have factor_4_21 : (37 : ZMod 358321471201) ^ 3976401 = 321794302141 := by
        calc
          (37 : ZMod 358321471201) ^ 3976401 = (37 : ZMod 358321471201) ^ (1988200 + 1988200 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 1988200 * (37 : ZMod 358321471201) ^ 1988200) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 321794302141 := by rw [factor_4_20]; decide
      have factor_4_22 : (37 : ZMod 358321471201) ^ 7952802 = 168104249194 := by
        calc
          (37 : ZMod 358321471201) ^ 7952802 = (37 : ZMod 358321471201) ^ (3976401 + 3976401) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 3976401 * (37 : ZMod 358321471201) ^ 3976401 := by rw [pow_add]
          _ = 168104249194 := by rw [factor_4_21]; decide
      have factor_4_23 : (37 : ZMod 358321471201) ^ 15905605 = 320889160851 := by
        calc
          (37 : ZMod 358321471201) ^ 15905605 = (37 : ZMod 358321471201) ^ (7952802 + 7952802 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 7952802 * (37 : ZMod 358321471201) ^ 7952802) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 320889160851 := by rw [factor_4_22]; decide
      have factor_4_24 : (37 : ZMod 358321471201) ^ 31811210 = 124114983662 := by
        calc
          (37 : ZMod 358321471201) ^ 31811210 = (37 : ZMod 358321471201) ^ (15905605 + 15905605) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 15905605 * (37 : ZMod 358321471201) ^ 15905605 := by rw [pow_add]
          _ = 124114983662 := by rw [factor_4_23]; decide
      have factor_4_25 : (37 : ZMod 358321471201) ^ 63622420 = 58854267364 := by
        calc
          (37 : ZMod 358321471201) ^ 63622420 = (37 : ZMod 358321471201) ^ (31811210 + 31811210) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 31811210 * (37 : ZMod 358321471201) ^ 31811210 := by rw [pow_add]
          _ = 58854267364 := by rw [factor_4_24]; decide
      have factor_4_26 : (37 : ZMod 358321471201) ^ 127244840 = 331358351113 := by
        calc
          (37 : ZMod 358321471201) ^ 127244840 = (37 : ZMod 358321471201) ^ (63622420 + 63622420) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 63622420 * (37 : ZMod 358321471201) ^ 63622420 := by rw [pow_add]
          _ = 331358351113 := by rw [factor_4_25]; decide
      have factor_4_27 : (37 : ZMod 358321471201) ^ 254489681 = 88959880138 := by
        calc
          (37 : ZMod 358321471201) ^ 254489681 = (37 : ZMod 358321471201) ^ (127244840 + 127244840 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 127244840 * (37 : ZMod 358321471201) ^ 127244840) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 88959880138 := by rw [factor_4_26]; decide
      have factor_4_28 : (37 : ZMod 358321471201) ^ 508979362 = 320412453258 := by
        calc
          (37 : ZMod 358321471201) ^ 508979362 = (37 : ZMod 358321471201) ^ (254489681 + 254489681) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 254489681 * (37 : ZMod 358321471201) ^ 254489681 := by rw [pow_add]
          _ = 320412453258 := by rw [factor_4_27]; decide
      have factor_4_29 : (37 : ZMod 358321471201) ^ 1017958725 = 293041443791 := by
        calc
          (37 : ZMod 358321471201) ^ 1017958725 = (37 : ZMod 358321471201) ^ (508979362 + 508979362 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 508979362 * (37 : ZMod 358321471201) ^ 508979362) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 293041443791 := by rw [factor_4_28]; decide
      have factor_4_30 : (37 : ZMod 358321471201) ^ 2035917450 = 197305402555 := by
        calc
          (37 : ZMod 358321471201) ^ 2035917450 = (37 : ZMod 358321471201) ^ (1017958725 + 1017958725) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 1017958725 * (37 : ZMod 358321471201) ^ 1017958725 := by rw [pow_add]
          _ = 197305402555 := by rw [factor_4_29]; decide
      have factor_4_31 : (37 : ZMod 358321471201) ^ 4071834900 = 273966479621 := by
        calc
          (37 : ZMod 358321471201) ^ 4071834900 = (37 : ZMod 358321471201) ^ (2035917450 + 2035917450) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 2035917450 * (37 : ZMod 358321471201) ^ 2035917450 := by rw [pow_add]
          _ = 273966479621 := by rw [factor_4_30]; decide
      have factor_4_32 : (37 : ZMod 358321471201) ^ 8143669800 = 72152391275 := by
        calc
          (37 : ZMod 358321471201) ^ 8143669800 = (37 : ZMod 358321471201) ^ (4071834900 + 4071834900) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 4071834900 * (37 : ZMod 358321471201) ^ 4071834900 := by rw [pow_add]
          _ = 72152391275 := by rw [factor_4_31]; decide
      have factor_4_33 : (37 : ZMod 358321471201) ^ 16287339600 = 71204399889 := by
        calc
          (37 : ZMod 358321471201) ^ 16287339600 = (37 : ZMod 358321471201) ^ (8143669800 + 8143669800) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 8143669800 * (37 : ZMod 358321471201) ^ 8143669800 := by rw [pow_add]
          _ = 71204399889 := by rw [factor_4_32]; decide
      have factor_4_34 : (37 : ZMod 358321471201) ^ 32574679200 = 183334590554 := by
        calc
          (37 : ZMod 358321471201) ^ 32574679200 = (37 : ZMod 358321471201) ^ (16287339600 + 16287339600) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 16287339600 * (37 : ZMod 358321471201) ^ 16287339600 := by rw [pow_add]
          _ = 183334590554 := by rw [factor_4_33]; decide
      change (37 : ZMod 358321471201) ^ 32574679200 ≠ 1
      rw [factor_4_34]
      decide
    ·
      have factor_5_0 : (37 : ZMod 358321471201) ^ 1 = 37 := by norm_num
      have factor_5_1 : (37 : ZMod 358321471201) ^ 2 = 1369 := by
        calc
          (37 : ZMod 358321471201) ^ 2 = (37 : ZMod 358321471201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 1 * (37 : ZMod 358321471201) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_5_0]; decide
      have factor_5_2 : (37 : ZMod 358321471201) ^ 4 = 1874161 := by
        calc
          (37 : ZMod 358321471201) ^ 4 = (37 : ZMod 358321471201) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 2 * (37 : ZMod 358321471201) ^ 2 := by rw [pow_add]
          _ = 1874161 := by rw [factor_5_1]; decide
      have factor_5_3 : (37 : ZMod 358321471201) ^ 9 = 249367220315 := by
        calc
          (37 : ZMod 358321471201) ^ 9 = (37 : ZMod 358321471201) ^ (4 + 4 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 4 * (37 : ZMod 358321471201) ^ 4) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 249367220315 := by rw [factor_5_2]; decide
      have factor_5_4 : (37 : ZMod 358321471201) ^ 19 = 198492022073 := by
        calc
          (37 : ZMod 358321471201) ^ 19 = (37 : ZMod 358321471201) ^ (9 + 9 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 9 * (37 : ZMod 358321471201) ^ 9) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 198492022073 := by rw [factor_5_3]; decide
      have factor_5_5 : (37 : ZMod 358321471201) ^ 39 = 302884888381 := by
        calc
          (37 : ZMod 358321471201) ^ 39 = (37 : ZMod 358321471201) ^ (19 + 19 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 19 * (37 : ZMod 358321471201) ^ 19) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 302884888381 := by rw [factor_5_4]; decide
      have factor_5_6 : (37 : ZMod 358321471201) ^ 78 = 82762772923 := by
        calc
          (37 : ZMod 358321471201) ^ 78 = (37 : ZMod 358321471201) ^ (39 + 39) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 39 * (37 : ZMod 358321471201) ^ 39 := by rw [pow_add]
          _ = 82762772923 := by rw [factor_5_5]; decide
      have factor_5_7 : (37 : ZMod 358321471201) ^ 157 = 100083843050 := by
        calc
          (37 : ZMod 358321471201) ^ 157 = (37 : ZMod 358321471201) ^ (78 + 78 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 78 * (37 : ZMod 358321471201) ^ 78) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 100083843050 := by rw [factor_5_6]; decide
      have factor_5_8 : (37 : ZMod 358321471201) ^ 314 = 94926172615 := by
        calc
          (37 : ZMod 358321471201) ^ 314 = (37 : ZMod 358321471201) ^ (157 + 157) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 157 * (37 : ZMod 358321471201) ^ 157 := by rw [pow_add]
          _ = 94926172615 := by rw [factor_5_7]; decide
      have factor_5_9 : (37 : ZMod 358321471201) ^ 628 = 253605565705 := by
        calc
          (37 : ZMod 358321471201) ^ 628 = (37 : ZMod 358321471201) ^ (314 + 314) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 314 * (37 : ZMod 358321471201) ^ 314 := by rw [pow_add]
          _ = 253605565705 := by rw [factor_5_8]; decide
      have factor_5_10 : (37 : ZMod 358321471201) ^ 1256 = 37241672069 := by
        calc
          (37 : ZMod 358321471201) ^ 1256 = (37 : ZMod 358321471201) ^ (628 + 628) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 628 * (37 : ZMod 358321471201) ^ 628 := by rw [pow_add]
          _ = 37241672069 := by rw [factor_5_9]; decide
      have factor_5_11 : (37 : ZMod 358321471201) ^ 2512 = 169137366828 := by
        calc
          (37 : ZMod 358321471201) ^ 2512 = (37 : ZMod 358321471201) ^ (1256 + 1256) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 1256 * (37 : ZMod 358321471201) ^ 1256 := by rw [pow_add]
          _ = 169137366828 := by rw [factor_5_10]; decide
      have factor_5_12 : (37 : ZMod 358321471201) ^ 5025 = 189251863741 := by
        calc
          (37 : ZMod 358321471201) ^ 5025 = (37 : ZMod 358321471201) ^ (2512 + 2512 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 2512 * (37 : ZMod 358321471201) ^ 2512) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 189251863741 := by rw [factor_5_11]; decide
      have factor_5_13 : (37 : ZMod 358321471201) ^ 10050 = 199180776169 := by
        calc
          (37 : ZMod 358321471201) ^ 10050 = (37 : ZMod 358321471201) ^ (5025 + 5025) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 5025 * (37 : ZMod 358321471201) ^ 5025 := by rw [pow_add]
          _ = 199180776169 := by rw [factor_5_12]; decide
      have factor_5_14 : (37 : ZMod 358321471201) ^ 20101 = 67861267410 := by
        calc
          (37 : ZMod 358321471201) ^ 20101 = (37 : ZMod 358321471201) ^ (10050 + 10050 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 10050 * (37 : ZMod 358321471201) ^ 10050) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 67861267410 := by rw [factor_5_13]; decide
      have factor_5_15 : (37 : ZMod 358321471201) ^ 40202 = 25899447951 := by
        calc
          (37 : ZMod 358321471201) ^ 40202 = (37 : ZMod 358321471201) ^ (20101 + 20101) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 20101 * (37 : ZMod 358321471201) ^ 20101 := by rw [pow_add]
          _ = 25899447951 := by rw [factor_5_14]; decide
      have factor_5_16 : (37 : ZMod 358321471201) ^ 80405 = 326801630464 := by
        calc
          (37 : ZMod 358321471201) ^ 80405 = (37 : ZMod 358321471201) ^ (40202 + 40202 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 40202 * (37 : ZMod 358321471201) ^ 40202) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 326801630464 := by rw [factor_5_15]; decide
      have factor_5_17 : (37 : ZMod 358321471201) ^ 160810 = 79745307440 := by
        calc
          (37 : ZMod 358321471201) ^ 160810 = (37 : ZMod 358321471201) ^ (80405 + 80405) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 80405 * (37 : ZMod 358321471201) ^ 80405 := by rw [pow_add]
          _ = 79745307440 := by rw [factor_5_16]; decide
      have factor_5_18 : (37 : ZMod 358321471201) ^ 321620 = 159461619939 := by
        calc
          (37 : ZMod 358321471201) ^ 321620 = (37 : ZMod 358321471201) ^ (160810 + 160810) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 160810 * (37 : ZMod 358321471201) ^ 160810 := by rw [pow_add]
          _ = 159461619939 := by rw [factor_5_17]; decide
      have factor_5_19 : (37 : ZMod 358321471201) ^ 643241 = 125625816490 := by
        calc
          (37 : ZMod 358321471201) ^ 643241 = (37 : ZMod 358321471201) ^ (321620 + 321620 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 321620 * (37 : ZMod 358321471201) ^ 321620) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 125625816490 := by rw [factor_5_18]; decide
      have factor_5_20 : (37 : ZMod 358321471201) ^ 1286482 = 5236497805 := by
        calc
          (37 : ZMod 358321471201) ^ 1286482 = (37 : ZMod 358321471201) ^ (643241 + 643241) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 643241 * (37 : ZMod 358321471201) ^ 643241 := by rw [pow_add]
          _ = 5236497805 := by rw [factor_5_19]; decide
      have factor_5_21 : (37 : ZMod 358321471201) ^ 2572965 = 296184441689 := by
        calc
          (37 : ZMod 358321471201) ^ 2572965 = (37 : ZMod 358321471201) ^ (1286482 + 1286482 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 1286482 * (37 : ZMod 358321471201) ^ 1286482) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 296184441689 := by rw [factor_5_20]; decide
      have factor_5_22 : (37 : ZMod 358321471201) ^ 5145931 = 134301973299 := by
        calc
          (37 : ZMod 358321471201) ^ 5145931 = (37 : ZMod 358321471201) ^ (2572965 + 2572965 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 2572965 * (37 : ZMod 358321471201) ^ 2572965) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 134301973299 := by rw [factor_5_21]; decide
      have factor_5_23 : (37 : ZMod 358321471201) ^ 10291862 = 246177783990 := by
        calc
          (37 : ZMod 358321471201) ^ 10291862 = (37 : ZMod 358321471201) ^ (5145931 + 5145931) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 5145931 * (37 : ZMod 358321471201) ^ 5145931 := by rw [pow_add]
          _ = 246177783990 := by rw [factor_5_22]; decide
      have factor_5_24 : (37 : ZMod 358321471201) ^ 20583724 = 213741578206 := by
        calc
          (37 : ZMod 358321471201) ^ 20583724 = (37 : ZMod 358321471201) ^ (10291862 + 10291862) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 10291862 * (37 : ZMod 358321471201) ^ 10291862 := by rw [pow_add]
          _ = 213741578206 := by rw [factor_5_23]; decide
      have factor_5_25 : (37 : ZMod 358321471201) ^ 41167448 = 223397828506 := by
        calc
          (37 : ZMod 358321471201) ^ 41167448 = (37 : ZMod 358321471201) ^ (20583724 + 20583724) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 20583724 * (37 : ZMod 358321471201) ^ 20583724 := by rw [pow_add]
          _ = 223397828506 := by rw [factor_5_24]; decide
      have factor_5_26 : (37 : ZMod 358321471201) ^ 82334896 = 77078988562 := by
        calc
          (37 : ZMod 358321471201) ^ 82334896 = (37 : ZMod 358321471201) ^ (41167448 + 41167448) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 41167448 * (37 : ZMod 358321471201) ^ 41167448 := by rw [pow_add]
          _ = 77078988562 := by rw [factor_5_25]; decide
      have factor_5_27 : (37 : ZMod 358321471201) ^ 164669793 = 268103088278 := by
        calc
          (37 : ZMod 358321471201) ^ 164669793 = (37 : ZMod 358321471201) ^ (82334896 + 82334896 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 82334896 * (37 : ZMod 358321471201) ^ 82334896) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 268103088278 := by rw [factor_5_26]; decide
      have factor_5_28 : (37 : ZMod 358321471201) ^ 329339587 = 244105191207 := by
        calc
          (37 : ZMod 358321471201) ^ 329339587 = (37 : ZMod 358321471201) ^ (164669793 + 164669793 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 164669793 * (37 : ZMod 358321471201) ^ 164669793) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 244105191207 := by rw [factor_5_27]; decide
      have factor_5_29 : (37 : ZMod 358321471201) ^ 658679175 = 39051132395 := by
        calc
          (37 : ZMod 358321471201) ^ 658679175 = (37 : ZMod 358321471201) ^ (329339587 + 329339587 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 329339587 * (37 : ZMod 358321471201) ^ 329339587) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 39051132395 := by rw [factor_5_28]; decide
      have factor_5_30 : (37 : ZMod 358321471201) ^ 1317358350 = 64793834465 := by
        calc
          (37 : ZMod 358321471201) ^ 1317358350 = (37 : ZMod 358321471201) ^ (658679175 + 658679175) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 658679175 * (37 : ZMod 358321471201) ^ 658679175 := by rw [pow_add]
          _ = 64793834465 := by rw [factor_5_29]; decide
      have factor_5_31 : (37 : ZMod 358321471201) ^ 2634716700 = 74318617417 := by
        calc
          (37 : ZMod 358321471201) ^ 2634716700 = (37 : ZMod 358321471201) ^ (1317358350 + 1317358350) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 1317358350 * (37 : ZMod 358321471201) ^ 1317358350 := by rw [pow_add]
          _ = 74318617417 := by rw [factor_5_30]; decide
      have factor_5_32 : (37 : ZMod 358321471201) ^ 5269433400 = 11275644650 := by
        calc
          (37 : ZMod 358321471201) ^ 5269433400 = (37 : ZMod 358321471201) ^ (2634716700 + 2634716700) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 2634716700 * (37 : ZMod 358321471201) ^ 2634716700 := by rw [pow_add]
          _ = 11275644650 := by rw [factor_5_31]; decide
      have factor_5_33 : (37 : ZMod 358321471201) ^ 10538866800 = 21006529799 := by
        calc
          (37 : ZMod 358321471201) ^ 10538866800 = (37 : ZMod 358321471201) ^ (5269433400 + 5269433400) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 5269433400 * (37 : ZMod 358321471201) ^ 5269433400 := by rw [pow_add]
          _ = 21006529799 := by rw [factor_5_32]; decide
      have factor_5_34 : (37 : ZMod 358321471201) ^ 21077733600 = 300326670888 := by
        calc
          (37 : ZMod 358321471201) ^ 21077733600 = (37 : ZMod 358321471201) ^ (10538866800 + 10538866800) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 10538866800 * (37 : ZMod 358321471201) ^ 10538866800 := by rw [pow_add]
          _ = 300326670888 := by rw [factor_5_33]; decide
      change (37 : ZMod 358321471201) ^ 21077733600 ≠ 1
      rw [factor_5_34]
      decide
    ·
      have factor_6_0 : (37 : ZMod 358321471201) ^ 1 = 37 := by norm_num
      have factor_6_1 : (37 : ZMod 358321471201) ^ 2 = 1369 := by
        calc
          (37 : ZMod 358321471201) ^ 2 = (37 : ZMod 358321471201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 1 * (37 : ZMod 358321471201) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_6_0]; decide
      have factor_6_2 : (37 : ZMod 358321471201) ^ 4 = 1874161 := by
        calc
          (37 : ZMod 358321471201) ^ 4 = (37 : ZMod 358321471201) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 2 * (37 : ZMod 358321471201) ^ 2 := by rw [pow_add]
          _ = 1874161 := by rw [factor_6_1]; decide
      have factor_6_3 : (37 : ZMod 358321471201) ^ 8 = 287586213112 := by
        calc
          (37 : ZMod 358321471201) ^ 8 = (37 : ZMod 358321471201) ^ (4 + 4) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 4 * (37 : ZMod 358321471201) ^ 4 := by rw [pow_add]
          _ = 287586213112 := by rw [factor_6_2]; decide
      have factor_6_4 : (37 : ZMod 358321471201) ^ 17 = 247750623651 := by
        calc
          (37 : ZMod 358321471201) ^ 17 = (37 : ZMod 358321471201) ^ (8 + 8 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 8 * (37 : ZMod 358321471201) ^ 8) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 247750623651 := by rw [factor_6_3]; decide
      have factor_6_5 : (37 : ZMod 358321471201) ^ 35 = 285793578872 := by
        calc
          (37 : ZMod 358321471201) ^ 35 = (37 : ZMod 358321471201) ^ (17 + 17 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 17 * (37 : ZMod 358321471201) ^ 17) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 285793578872 := by rw [factor_6_4]; decide
      have factor_6_6 : (37 : ZMod 358321471201) ^ 70 = 149196583982 := by
        calc
          (37 : ZMod 358321471201) ^ 70 = (37 : ZMod 358321471201) ^ (35 + 35) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 35 * (37 : ZMod 358321471201) ^ 35 := by rw [pow_add]
          _ = 149196583982 := by rw [factor_6_5]; decide
      have factor_6_7 : (37 : ZMod 358321471201) ^ 140 = 188271914621 := by
        calc
          (37 : ZMod 358321471201) ^ 140 = (37 : ZMod 358321471201) ^ (70 + 70) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 70 * (37 : ZMod 358321471201) ^ 70 := by rw [pow_add]
          _ = 188271914621 := by rw [factor_6_6]; decide
      have factor_6_8 : (37 : ZMod 358321471201) ^ 281 = 9439382291 := by
        calc
          (37 : ZMod 358321471201) ^ 281 = (37 : ZMod 358321471201) ^ (140 + 140 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 140 * (37 : ZMod 358321471201) ^ 140) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 9439382291 := by rw [factor_6_7]; decide
      have factor_6_9 : (37 : ZMod 358321471201) ^ 562 = 347099041479 := by
        calc
          (37 : ZMod 358321471201) ^ 562 = (37 : ZMod 358321471201) ^ (281 + 281) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 281 * (37 : ZMod 358321471201) ^ 281 := by rw [pow_add]
          _ = 347099041479 := by rw [factor_6_8]; decide
      have factor_6_10 : (37 : ZMod 358321471201) ^ 1124 = 345739879411 := by
        calc
          (37 : ZMod 358321471201) ^ 1124 = (37 : ZMod 358321471201) ^ (562 + 562) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 562 * (37 : ZMod 358321471201) ^ 562 := by rw [pow_add]
          _ = 345739879411 := by rw [factor_6_9]; decide
      have factor_6_11 : (37 : ZMod 358321471201) ^ 2248 = 230065955136 := by
        calc
          (37 : ZMod 358321471201) ^ 2248 = (37 : ZMod 358321471201) ^ (1124 + 1124) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 1124 * (37 : ZMod 358321471201) ^ 1124 := by rw [pow_add]
          _ = 230065955136 := by rw [factor_6_10]; decide
      have factor_6_12 : (37 : ZMod 358321471201) ^ 4496 = 9473964607 := by
        calc
          (37 : ZMod 358321471201) ^ 4496 = (37 : ZMod 358321471201) ^ (2248 + 2248) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 2248 * (37 : ZMod 358321471201) ^ 2248 := by rw [pow_add]
          _ = 9473964607 := by rw [factor_6_11]; decide
      have factor_6_13 : (37 : ZMod 358321471201) ^ 8992 = 213864483882 := by
        calc
          (37 : ZMod 358321471201) ^ 8992 = (37 : ZMod 358321471201) ^ (4496 + 4496) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 4496 * (37 : ZMod 358321471201) ^ 4496 := by rw [pow_add]
          _ = 213864483882 := by rw [factor_6_12]; decide
      have factor_6_14 : (37 : ZMod 358321471201) ^ 17985 = 143207168903 := by
        calc
          (37 : ZMod 358321471201) ^ 17985 = (37 : ZMod 358321471201) ^ (8992 + 8992 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 8992 * (37 : ZMod 358321471201) ^ 8992) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 143207168903 := by rw [factor_6_13]; decide
      have factor_6_15 : (37 : ZMod 358321471201) ^ 35970 = 21162053735 := by
        calc
          (37 : ZMod 358321471201) ^ 35970 = (37 : ZMod 358321471201) ^ (17985 + 17985) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 17985 * (37 : ZMod 358321471201) ^ 17985 := by rw [pow_add]
          _ = 21162053735 := by rw [factor_6_14]; decide
      have factor_6_16 : (37 : ZMod 358321471201) ^ 71941 = 308229772330 := by
        calc
          (37 : ZMod 358321471201) ^ 71941 = (37 : ZMod 358321471201) ^ (35970 + 35970 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 35970 * (37 : ZMod 358321471201) ^ 35970) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 308229772330 := by rw [factor_6_15]; decide
      have factor_6_17 : (37 : ZMod 358321471201) ^ 143882 = 305360120796 := by
        calc
          (37 : ZMod 358321471201) ^ 143882 = (37 : ZMod 358321471201) ^ (71941 + 71941) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 71941 * (37 : ZMod 358321471201) ^ 71941 := by rw [pow_add]
          _ = 305360120796 := by rw [factor_6_16]; decide
      have factor_6_18 : (37 : ZMod 358321471201) ^ 287765 = 220342873720 := by
        calc
          (37 : ZMod 358321471201) ^ 287765 = (37 : ZMod 358321471201) ^ (143882 + 143882 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 143882 * (37 : ZMod 358321471201) ^ 143882) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 220342873720 := by rw [factor_6_17]; decide
      have factor_6_19 : (37 : ZMod 358321471201) ^ 575531 = 16605456600 := by
        calc
          (37 : ZMod 358321471201) ^ 575531 = (37 : ZMod 358321471201) ^ (287765 + 287765 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 287765 * (37 : ZMod 358321471201) ^ 287765) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 16605456600 := by rw [factor_6_18]; decide
      have factor_6_20 : (37 : ZMod 358321471201) ^ 1151063 = 170594842947 := by
        calc
          (37 : ZMod 358321471201) ^ 1151063 = (37 : ZMod 358321471201) ^ (575531 + 575531 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 575531 * (37 : ZMod 358321471201) ^ 575531) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 170594842947 := by rw [factor_6_19]; decide
      have factor_6_21 : (37 : ZMod 358321471201) ^ 2302127 = 287386515620 := by
        calc
          (37 : ZMod 358321471201) ^ 2302127 = (37 : ZMod 358321471201) ^ (1151063 + 1151063 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 1151063 * (37 : ZMod 358321471201) ^ 1151063) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 287386515620 := by rw [factor_6_20]; decide
      have factor_6_22 : (37 : ZMod 358321471201) ^ 4604254 = 335015017259 := by
        calc
          (37 : ZMod 358321471201) ^ 4604254 = (37 : ZMod 358321471201) ^ (2302127 + 2302127) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 2302127 * (37 : ZMod 358321471201) ^ 2302127 := by rw [pow_add]
          _ = 335015017259 := by rw [factor_6_21]; decide
      have factor_6_23 : (37 : ZMod 358321471201) ^ 9208508 = 63629801492 := by
        calc
          (37 : ZMod 358321471201) ^ 9208508 = (37 : ZMod 358321471201) ^ (4604254 + 4604254) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 4604254 * (37 : ZMod 358321471201) ^ 4604254 := by rw [pow_add]
          _ = 63629801492 := by rw [factor_6_22]; decide
      have factor_6_24 : (37 : ZMod 358321471201) ^ 18417016 = 79704470239 := by
        calc
          (37 : ZMod 358321471201) ^ 18417016 = (37 : ZMod 358321471201) ^ (9208508 + 9208508) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 9208508 * (37 : ZMod 358321471201) ^ 9208508 := by rw [pow_add]
          _ = 79704470239 := by rw [factor_6_23]; decide
      have factor_6_25 : (37 : ZMod 358321471201) ^ 36834032 = 169829842841 := by
        calc
          (37 : ZMod 358321471201) ^ 36834032 = (37 : ZMod 358321471201) ^ (18417016 + 18417016) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 18417016 * (37 : ZMod 358321471201) ^ 18417016 := by rw [pow_add]
          _ = 169829842841 := by rw [factor_6_24]; decide
      have factor_6_26 : (37 : ZMod 358321471201) ^ 73668065 = 21772164444 := by
        calc
          (37 : ZMod 358321471201) ^ 73668065 = (37 : ZMod 358321471201) ^ (36834032 + 36834032 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 36834032 * (37 : ZMod 358321471201) ^ 36834032) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 21772164444 := by rw [factor_6_25]; decide
      have factor_6_27 : (37 : ZMod 358321471201) ^ 147336131 = 329016026238 := by
        calc
          (37 : ZMod 358321471201) ^ 147336131 = (37 : ZMod 358321471201) ^ (73668065 + 73668065 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 73668065 * (37 : ZMod 358321471201) ^ 73668065) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 329016026238 := by rw [factor_6_26]; decide
      have factor_6_28 : (37 : ZMod 358321471201) ^ 294672262 = 340209052258 := by
        calc
          (37 : ZMod 358321471201) ^ 294672262 = (37 : ZMod 358321471201) ^ (147336131 + 147336131) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 147336131 * (37 : ZMod 358321471201) ^ 147336131 := by rw [pow_add]
          _ = 340209052258 := by rw [factor_6_27]; decide
      have factor_6_29 : (37 : ZMod 358321471201) ^ 589344525 = 96465881011 := by
        calc
          (37 : ZMod 358321471201) ^ 589344525 = (37 : ZMod 358321471201) ^ (294672262 + 294672262 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 294672262 * (37 : ZMod 358321471201) ^ 294672262) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 96465881011 := by rw [factor_6_28]; decide
      have factor_6_30 : (37 : ZMod 358321471201) ^ 1178689050 = 203338658994 := by
        calc
          (37 : ZMod 358321471201) ^ 1178689050 = (37 : ZMod 358321471201) ^ (589344525 + 589344525) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 589344525 * (37 : ZMod 358321471201) ^ 589344525 := by rw [pow_add]
          _ = 203338658994 := by rw [factor_6_29]; decide
      have factor_6_31 : (37 : ZMod 358321471201) ^ 2357378100 = 232988137573 := by
        calc
          (37 : ZMod 358321471201) ^ 2357378100 = (37 : ZMod 358321471201) ^ (1178689050 + 1178689050) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 1178689050 * (37 : ZMod 358321471201) ^ 1178689050 := by rw [pow_add]
          _ = 232988137573 := by rw [factor_6_30]; decide
      have factor_6_32 : (37 : ZMod 358321471201) ^ 4714756200 = 297375114770 := by
        calc
          (37 : ZMod 358321471201) ^ 4714756200 = (37 : ZMod 358321471201) ^ (2357378100 + 2357378100) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 2357378100 * (37 : ZMod 358321471201) ^ 2357378100 := by rw [pow_add]
          _ = 297375114770 := by rw [factor_6_31]; decide
      have factor_6_33 : (37 : ZMod 358321471201) ^ 9429512400 = 138913835487 := by
        calc
          (37 : ZMod 358321471201) ^ 9429512400 = (37 : ZMod 358321471201) ^ (4714756200 + 4714756200) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 4714756200 * (37 : ZMod 358321471201) ^ 4714756200 := by rw [pow_add]
          _ = 138913835487 := by rw [factor_6_32]; decide
      have factor_6_34 : (37 : ZMod 358321471201) ^ 18859024800 = 171197299951 := by
        calc
          (37 : ZMod 358321471201) ^ 18859024800 = (37 : ZMod 358321471201) ^ (9429512400 + 9429512400) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 9429512400 * (37 : ZMod 358321471201) ^ 9429512400 := by rw [pow_add]
          _ = 171197299951 := by rw [factor_6_33]; decide
      change (37 : ZMod 358321471201) ^ 18859024800 ≠ 1
      rw [factor_6_34]
      decide
    ·
      have factor_7_0 : (37 : ZMod 358321471201) ^ 1 = 37 := by norm_num
      have factor_7_1 : (37 : ZMod 358321471201) ^ 3 = 50653 := by
        calc
          (37 : ZMod 358321471201) ^ 3 = (37 : ZMod 358321471201) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 1 * (37 : ZMod 358321471201) ^ 1) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 50653 := by rw [factor_7_0]; decide
      have factor_7_2 : (37 : ZMod 358321471201) ^ 7 = 94931877133 := by
        calc
          (37 : ZMod 358321471201) ^ 7 = (37 : ZMod 358321471201) ^ (3 + 3 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 3 * (37 : ZMod 358321471201) ^ 3) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 94931877133 := by rw [factor_7_1]; decide
      have factor_7_3 : (37 : ZMod 358321471201) ^ 14 = 53201690207 := by
        calc
          (37 : ZMod 358321471201) ^ 14 = (37 : ZMod 358321471201) ^ (7 + 7) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 7 * (37 : ZMod 358321471201) ^ 7 := by rw [pow_add]
          _ = 53201690207 := by rw [factor_7_2]; decide
      have factor_7_4 : (37 : ZMod 358321471201) ^ 29 = 307820390617 := by
        calc
          (37 : ZMod 358321471201) ^ 29 = (37 : ZMod 358321471201) ^ (14 + 14 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 14 * (37 : ZMod 358321471201) ^ 14) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 307820390617 := by rw [factor_7_3]; decide
      have factor_7_5 : (37 : ZMod 358321471201) ^ 58 = 346108020920 := by
        calc
          (37 : ZMod 358321471201) ^ 58 = (37 : ZMod 358321471201) ^ (29 + 29) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 29 * (37 : ZMod 358321471201) ^ 29 := by rw [pow_add]
          _ = 346108020920 := by rw [factor_7_4]; decide
      have factor_7_6 : (37 : ZMod 358321471201) ^ 116 = 351977974964 := by
        calc
          (37 : ZMod 358321471201) ^ 116 = (37 : ZMod 358321471201) ^ (58 + 58) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 58 * (37 : ZMod 358321471201) ^ 58 := by rw [pow_add]
          _ = 351977974964 := by rw [factor_7_5]; decide
      have factor_7_7 : (37 : ZMod 358321471201) ^ 232 = 49300984532 := by
        calc
          (37 : ZMod 358321471201) ^ 232 = (37 : ZMod 358321471201) ^ (116 + 116) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 116 * (37 : ZMod 358321471201) ^ 116 := by rw [pow_add]
          _ = 49300984532 := by rw [factor_7_6]; decide
      have factor_7_8 : (37 : ZMod 358321471201) ^ 464 = 148182600774 := by
        calc
          (37 : ZMod 358321471201) ^ 464 = (37 : ZMod 358321471201) ^ (232 + 232) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 232 * (37 : ZMod 358321471201) ^ 232 := by rw [pow_add]
          _ = 148182600774 := by rw [factor_7_7]; decide
      have factor_7_9 : (37 : ZMod 358321471201) ^ 928 = 213823083630 := by
        calc
          (37 : ZMod 358321471201) ^ 928 = (37 : ZMod 358321471201) ^ (464 + 464) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 464 * (37 : ZMod 358321471201) ^ 464 := by rw [pow_add]
          _ = 213823083630 := by rw [factor_7_8]; decide
      have factor_7_10 : (37 : ZMod 358321471201) ^ 1857 = 273109050304 := by
        calc
          (37 : ZMod 358321471201) ^ 1857 = (37 : ZMod 358321471201) ^ (928 + 928 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 928 * (37 : ZMod 358321471201) ^ 928) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 273109050304 := by rw [factor_7_9]; decide
      have factor_7_11 : (37 : ZMod 358321471201) ^ 3714 = 276692376739 := by
        calc
          (37 : ZMod 358321471201) ^ 3714 = (37 : ZMod 358321471201) ^ (1857 + 1857) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 1857 * (37 : ZMod 358321471201) ^ 1857 := by rw [pow_add]
          _ = 276692376739 := by rw [factor_7_10]; decide
      have factor_7_12 : (37 : ZMod 358321471201) ^ 7428 = 273584017548 := by
        calc
          (37 : ZMod 358321471201) ^ 7428 = (37 : ZMod 358321471201) ^ (3714 + 3714) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 3714 * (37 : ZMod 358321471201) ^ 3714 := by rw [pow_add]
          _ = 273584017548 := by rw [factor_7_11]; decide
      have factor_7_13 : (37 : ZMod 358321471201) ^ 14857 = 55044768724 := by
        calc
          (37 : ZMod 358321471201) ^ 14857 = (37 : ZMod 358321471201) ^ (7428 + 7428 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 7428 * (37 : ZMod 358321471201) ^ 7428) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 55044768724 := by rw [factor_7_12]; decide
      have factor_7_14 : (37 : ZMod 358321471201) ^ 29714 = 18870056040 := by
        calc
          (37 : ZMod 358321471201) ^ 29714 = (37 : ZMod 358321471201) ^ (14857 + 14857) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 14857 * (37 : ZMod 358321471201) ^ 14857 := by rw [pow_add]
          _ = 18870056040 := by rw [factor_7_13]; decide
      have factor_7_15 : (37 : ZMod 358321471201) ^ 59429 = 194851716711 := by
        calc
          (37 : ZMod 358321471201) ^ 59429 = (37 : ZMod 358321471201) ^ (29714 + 29714 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 29714 * (37 : ZMod 358321471201) ^ 29714) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 194851716711 := by rw [factor_7_14]; decide
      have factor_7_16 : (37 : ZMod 358321471201) ^ 118859 = 265611698739 := by
        calc
          (37 : ZMod 358321471201) ^ 118859 = (37 : ZMod 358321471201) ^ (59429 + 59429 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 59429 * (37 : ZMod 358321471201) ^ 59429) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 265611698739 := by rw [factor_7_15]; decide
      have factor_7_17 : (37 : ZMod 358321471201) ^ 237719 = 358306860654 := by
        calc
          (37 : ZMod 358321471201) ^ 237719 = (37 : ZMod 358321471201) ^ (118859 + 118859 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 118859 * (37 : ZMod 358321471201) ^ 118859) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 358306860654 := by rw [factor_7_16]; decide
      have factor_7_18 : (37 : ZMod 358321471201) ^ 475439 = 197226438291 := by
        calc
          (37 : ZMod 358321471201) ^ 475439 = (37 : ZMod 358321471201) ^ (237719 + 237719 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 237719 * (37 : ZMod 358321471201) ^ 237719) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 197226438291 := by rw [factor_7_17]; decide
      have factor_7_19 : (37 : ZMod 358321471201) ^ 950878 = 161955544317 := by
        calc
          (37 : ZMod 358321471201) ^ 950878 = (37 : ZMod 358321471201) ^ (475439 + 475439) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 475439 * (37 : ZMod 358321471201) ^ 475439 := by rw [pow_add]
          _ = 161955544317 := by rw [factor_7_18]; decide
      have factor_7_20 : (37 : ZMod 358321471201) ^ 1901757 = 173700675285 := by
        calc
          (37 : ZMod 358321471201) ^ 1901757 = (37 : ZMod 358321471201) ^ (950878 + 950878 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 950878 * (37 : ZMod 358321471201) ^ 950878) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 173700675285 := by rw [factor_7_19]; decide
      have factor_7_21 : (37 : ZMod 358321471201) ^ 3803514 = 302476307186 := by
        calc
          (37 : ZMod 358321471201) ^ 3803514 = (37 : ZMod 358321471201) ^ (1901757 + 1901757) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 1901757 * (37 : ZMod 358321471201) ^ 1901757 := by rw [pow_add]
          _ = 302476307186 := by rw [factor_7_20]; decide
      have factor_7_22 : (37 : ZMod 358321471201) ^ 7607028 = 204466631741 := by
        calc
          (37 : ZMod 358321471201) ^ 7607028 = (37 : ZMod 358321471201) ^ (3803514 + 3803514) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 3803514 * (37 : ZMod 358321471201) ^ 3803514 := by rw [pow_add]
          _ = 204466631741 := by rw [factor_7_21]; decide
      have factor_7_23 : (37 : ZMod 358321471201) ^ 15214057 = 141195077410 := by
        calc
          (37 : ZMod 358321471201) ^ 15214057 = (37 : ZMod 358321471201) ^ (7607028 + 7607028 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 7607028 * (37 : ZMod 358321471201) ^ 7607028) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 141195077410 := by rw [factor_7_22]; decide
      have factor_7_24 : (37 : ZMod 358321471201) ^ 30428114 = 343544071853 := by
        calc
          (37 : ZMod 358321471201) ^ 30428114 = (37 : ZMod 358321471201) ^ (15214057 + 15214057) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 15214057 * (37 : ZMod 358321471201) ^ 15214057 := by rw [pow_add]
          _ = 343544071853 := by rw [factor_7_23]; decide
      have factor_7_25 : (37 : ZMod 358321471201) ^ 60856228 = 143890947205 := by
        calc
          (37 : ZMod 358321471201) ^ 60856228 = (37 : ZMod 358321471201) ^ (30428114 + 30428114) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 30428114 * (37 : ZMod 358321471201) ^ 30428114 := by rw [pow_add]
          _ = 143890947205 := by rw [factor_7_24]; decide
      have factor_7_26 : (37 : ZMod 358321471201) ^ 121712456 = 272071195874 := by
        calc
          (37 : ZMod 358321471201) ^ 121712456 = (37 : ZMod 358321471201) ^ (60856228 + 60856228) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 60856228 * (37 : ZMod 358321471201) ^ 60856228 := by rw [pow_add]
          _ = 272071195874 := by rw [factor_7_25]; decide
      have factor_7_27 : (37 : ZMod 358321471201) ^ 243424912 = 44161613905 := by
        calc
          (37 : ZMod 358321471201) ^ 243424912 = (37 : ZMod 358321471201) ^ (121712456 + 121712456) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 121712456 * (37 : ZMod 358321471201) ^ 121712456 := by rw [pow_add]
          _ = 44161613905 := by rw [factor_7_26]; decide
      have factor_7_28 : (37 : ZMod 358321471201) ^ 486849825 = 169403692095 := by
        calc
          (37 : ZMod 358321471201) ^ 486849825 = (37 : ZMod 358321471201) ^ (243424912 + 243424912 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 243424912 * (37 : ZMod 358321471201) ^ 243424912) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 169403692095 := by rw [factor_7_27]; decide
      have factor_7_29 : (37 : ZMod 358321471201) ^ 973699650 = 244690004202 := by
        calc
          (37 : ZMod 358321471201) ^ 973699650 = (37 : ZMod 358321471201) ^ (486849825 + 486849825) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 486849825 * (37 : ZMod 358321471201) ^ 486849825 := by rw [pow_add]
          _ = 244690004202 := by rw [factor_7_28]; decide
      have factor_7_30 : (37 : ZMod 358321471201) ^ 1947399300 = 161936303348 := by
        calc
          (37 : ZMod 358321471201) ^ 1947399300 = (37 : ZMod 358321471201) ^ (973699650 + 973699650) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 973699650 * (37 : ZMod 358321471201) ^ 973699650 := by rw [pow_add]
          _ = 161936303348 := by rw [factor_7_29]; decide
      have factor_7_31 : (37 : ZMod 358321471201) ^ 3894798600 = 291966497386 := by
        calc
          (37 : ZMod 358321471201) ^ 3894798600 = (37 : ZMod 358321471201) ^ (1947399300 + 1947399300) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 1947399300 * (37 : ZMod 358321471201) ^ 1947399300 := by rw [pow_add]
          _ = 291966497386 := by rw [factor_7_30]; decide
      have factor_7_32 : (37 : ZMod 358321471201) ^ 7789597200 = 173226424692 := by
        calc
          (37 : ZMod 358321471201) ^ 7789597200 = (37 : ZMod 358321471201) ^ (3894798600 + 3894798600) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 3894798600 * (37 : ZMod 358321471201) ^ 3894798600 := by rw [pow_add]
          _ = 173226424692 := by rw [factor_7_31]; decide
      have factor_7_33 : (37 : ZMod 358321471201) ^ 15579194400 = 269859438982 := by
        calc
          (37 : ZMod 358321471201) ^ 15579194400 = (37 : ZMod 358321471201) ^ (7789597200 + 7789597200) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 7789597200 * (37 : ZMod 358321471201) ^ 7789597200 := by rw [pow_add]
          _ = 269859438982 := by rw [factor_7_32]; decide
      change (37 : ZMod 358321471201) ^ 15579194400 ≠ 1
      rw [factor_7_33]
      decide
    ·
      have factor_8_0 : (37 : ZMod 358321471201) ^ 1 = 37 := by norm_num
      have factor_8_1 : (37 : ZMod 358321471201) ^ 2 = 1369 := by
        calc
          (37 : ZMod 358321471201) ^ 2 = (37 : ZMod 358321471201) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 1 * (37 : ZMod 358321471201) ^ 1 := by rw [pow_add]
          _ = 1369 := by rw [factor_8_0]; decide
      have factor_8_2 : (37 : ZMod 358321471201) ^ 5 = 69343957 := by
        calc
          (37 : ZMod 358321471201) ^ 5 = (37 : ZMod 358321471201) ^ (2 + 2 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 2 * (37 : ZMod 358321471201) ^ 2) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 69343957 := by rw [factor_8_1]; decide
      have factor_8_3 : (37 : ZMod 358321471201) ^ 11 = 261684027883 := by
        calc
          (37 : ZMod 358321471201) ^ 11 = (37 : ZMod 358321471201) ^ (5 + 5 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 5 * (37 : ZMod 358321471201) ^ 5) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 261684027883 := by rw [factor_8_2]; decide
      have factor_8_4 : (37 : ZMod 358321471201) ^ 23 = 238394189563 := by
        calc
          (37 : ZMod 358321471201) ^ 23 = (37 : ZMod 358321471201) ^ (11 + 11 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 11 * (37 : ZMod 358321471201) ^ 11) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 238394189563 := by rw [factor_8_3]; decide
      have factor_8_5 : (37 : ZMod 358321471201) ^ 46 = 155599431831 := by
        calc
          (37 : ZMod 358321471201) ^ 46 = (37 : ZMod 358321471201) ^ (23 + 23) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 23 * (37 : ZMod 358321471201) ^ 23 := by rw [pow_add]
          _ = 155599431831 := by rw [factor_8_4]; decide
      have factor_8_6 : (37 : ZMod 358321471201) ^ 92 = 36200010392 := by
        calc
          (37 : ZMod 358321471201) ^ 92 = (37 : ZMod 358321471201) ^ (46 + 46) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 46 * (37 : ZMod 358321471201) ^ 46 := by rw [pow_add]
          _ = 36200010392 := by rw [factor_8_5]; decide
      have factor_8_7 : (37 : ZMod 358321471201) ^ 184 = 198066048639 := by
        calc
          (37 : ZMod 358321471201) ^ 184 = (37 : ZMod 358321471201) ^ (92 + 92) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 92 * (37 : ZMod 358321471201) ^ 92 := by rw [pow_add]
          _ = 198066048639 := by rw [factor_8_6]; decide
      have factor_8_8 : (37 : ZMod 358321471201) ^ 368 = 30933202404 := by
        calc
          (37 : ZMod 358321471201) ^ 368 = (37 : ZMod 358321471201) ^ (184 + 184) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 184 * (37 : ZMod 358321471201) ^ 184 := by rw [pow_add]
          _ = 30933202404 := by rw [factor_8_7]; decide
      have factor_8_9 : (37 : ZMod 358321471201) ^ 736 = 174841310637 := by
        calc
          (37 : ZMod 358321471201) ^ 736 = (37 : ZMod 358321471201) ^ (368 + 368) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 368 * (37 : ZMod 358321471201) ^ 368 := by rw [pow_add]
          _ = 174841310637 := by rw [factor_8_8]; decide
      have factor_8_10 : (37 : ZMod 358321471201) ^ 1472 = 199798519557 := by
        calc
          (37 : ZMod 358321471201) ^ 1472 = (37 : ZMod 358321471201) ^ (736 + 736) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 736 * (37 : ZMod 358321471201) ^ 736 := by rw [pow_add]
          _ = 199798519557 := by rw [factor_8_9]; decide
      have factor_8_11 : (37 : ZMod 358321471201) ^ 2945 = 264484210674 := by
        calc
          (37 : ZMod 358321471201) ^ 2945 = (37 : ZMod 358321471201) ^ (1472 + 1472 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 1472 * (37 : ZMod 358321471201) ^ 1472) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 264484210674 := by rw [factor_8_10]; decide
      have factor_8_12 : (37 : ZMod 358321471201) ^ 5891 = 350176699019 := by
        calc
          (37 : ZMod 358321471201) ^ 5891 = (37 : ZMod 358321471201) ^ (2945 + 2945 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 2945 * (37 : ZMod 358321471201) ^ 2945) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 350176699019 := by rw [factor_8_11]; decide
      have factor_8_13 : (37 : ZMod 358321471201) ^ 11783 = 264794932689 := by
        calc
          (37 : ZMod 358321471201) ^ 11783 = (37 : ZMod 358321471201) ^ (5891 + 5891 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 5891 * (37 : ZMod 358321471201) ^ 5891) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 264794932689 := by rw [factor_8_12]; decide
      have factor_8_14 : (37 : ZMod 358321471201) ^ 23567 = 134433679058 := by
        calc
          (37 : ZMod 358321471201) ^ 23567 = (37 : ZMod 358321471201) ^ (11783 + 11783 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 11783 * (37 : ZMod 358321471201) ^ 11783) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 134433679058 := by rw [factor_8_13]; decide
      have factor_8_15 : (37 : ZMod 358321471201) ^ 47134 = 119810531437 := by
        calc
          (37 : ZMod 358321471201) ^ 47134 = (37 : ZMod 358321471201) ^ (23567 + 23567) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 23567 * (37 : ZMod 358321471201) ^ 23567 := by rw [pow_add]
          _ = 119810531437 := by rw [factor_8_14]; decide
      have factor_8_16 : (37 : ZMod 358321471201) ^ 94268 = 167594190401 := by
        calc
          (37 : ZMod 358321471201) ^ 94268 = (37 : ZMod 358321471201) ^ (47134 + 47134) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 47134 * (37 : ZMod 358321471201) ^ 47134 := by rw [pow_add]
          _ = 167594190401 := by rw [factor_8_15]; decide
      have factor_8_17 : (37 : ZMod 358321471201) ^ 188536 = 59859591642 := by
        calc
          (37 : ZMod 358321471201) ^ 188536 = (37 : ZMod 358321471201) ^ (94268 + 94268) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 94268 * (37 : ZMod 358321471201) ^ 94268 := by rw [pow_add]
          _ = 59859591642 := by rw [factor_8_16]; decide
      have factor_8_18 : (37 : ZMod 358321471201) ^ 377072 = 338695325361 := by
        calc
          (37 : ZMod 358321471201) ^ 377072 = (37 : ZMod 358321471201) ^ (188536 + 188536) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 188536 * (37 : ZMod 358321471201) ^ 188536 := by rw [pow_add]
          _ = 338695325361 := by rw [factor_8_17]; decide
      have factor_8_19 : (37 : ZMod 358321471201) ^ 754145 = 273856136232 := by
        calc
          (37 : ZMod 358321471201) ^ 754145 = (37 : ZMod 358321471201) ^ (377072 + 377072 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 377072 * (37 : ZMod 358321471201) ^ 377072) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 273856136232 := by rw [factor_8_18]; decide
      have factor_8_20 : (37 : ZMod 358321471201) ^ 1508290 = 8918790421 := by
        calc
          (37 : ZMod 358321471201) ^ 1508290 = (37 : ZMod 358321471201) ^ (754145 + 754145) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 754145 * (37 : ZMod 358321471201) ^ 754145 := by rw [pow_add]
          _ = 8918790421 := by rw [factor_8_19]; decide
      have factor_8_21 : (37 : ZMod 358321471201) ^ 3016580 = 49544884341 := by
        calc
          (37 : ZMod 358321471201) ^ 3016580 = (37 : ZMod 358321471201) ^ (1508290 + 1508290) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 1508290 * (37 : ZMod 358321471201) ^ 1508290 := by rw [pow_add]
          _ = 49544884341 := by rw [factor_8_20]; decide
      have factor_8_22 : (37 : ZMod 358321471201) ^ 6033160 = 208197888301 := by
        calc
          (37 : ZMod 358321471201) ^ 6033160 = (37 : ZMod 358321471201) ^ (3016580 + 3016580) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 3016580 * (37 : ZMod 358321471201) ^ 3016580 := by rw [pow_add]
          _ = 208197888301 := by rw [factor_8_21]; decide
      have factor_8_23 : (37 : ZMod 358321471201) ^ 12066321 = 55272825650 := by
        calc
          (37 : ZMod 358321471201) ^ 12066321 = (37 : ZMod 358321471201) ^ (6033160 + 6033160 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 6033160 * (37 : ZMod 358321471201) ^ 6033160) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 55272825650 := by rw [factor_8_22]; decide
      have factor_8_24 : (37 : ZMod 358321471201) ^ 24132642 = 30313806538 := by
        calc
          (37 : ZMod 358321471201) ^ 24132642 = (37 : ZMod 358321471201) ^ (12066321 + 12066321) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 12066321 * (37 : ZMod 358321471201) ^ 12066321 := by rw [pow_add]
          _ = 30313806538 := by rw [factor_8_23]; decide
      have factor_8_25 : (37 : ZMod 358321471201) ^ 48265284 = 182500105479 := by
        calc
          (37 : ZMod 358321471201) ^ 48265284 = (37 : ZMod 358321471201) ^ (24132642 + 24132642) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 24132642 * (37 : ZMod 358321471201) ^ 24132642 := by rw [pow_add]
          _ = 182500105479 := by rw [factor_8_24]; decide
      have factor_8_26 : (37 : ZMod 358321471201) ^ 96530568 = 151205416571 := by
        calc
          (37 : ZMod 358321471201) ^ 96530568 = (37 : ZMod 358321471201) ^ (48265284 + 48265284) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 48265284 * (37 : ZMod 358321471201) ^ 48265284 := by rw [pow_add]
          _ = 151205416571 := by rw [factor_8_25]; decide
      have factor_8_27 : (37 : ZMod 358321471201) ^ 193061137 = 31534345674 := by
        calc
          (37 : ZMod 358321471201) ^ 193061137 = (37 : ZMod 358321471201) ^ (96530568 + 96530568 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 96530568 * (37 : ZMod 358321471201) ^ 96530568) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 31534345674 := by rw [factor_8_26]; decide
      have factor_8_28 : (37 : ZMod 358321471201) ^ 386122275 = 138721995247 := by
        calc
          (37 : ZMod 358321471201) ^ 386122275 = (37 : ZMod 358321471201) ^ (193061137 + 193061137 + 1) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = ((37 : ZMod 358321471201) ^ 193061137 * (37 : ZMod 358321471201) ^ 193061137) * (37 : ZMod 358321471201) := by rw [pow_succ, pow_add]
          _ = 138721995247 := by rw [factor_8_27]; decide
      have factor_8_29 : (37 : ZMod 358321471201) ^ 772244550 = 164394525282 := by
        calc
          (37 : ZMod 358321471201) ^ 772244550 = (37 : ZMod 358321471201) ^ (386122275 + 386122275) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 386122275 * (37 : ZMod 358321471201) ^ 386122275 := by rw [pow_add]
          _ = 164394525282 := by rw [factor_8_28]; decide
      have factor_8_30 : (37 : ZMod 358321471201) ^ 1544489100 = 190971511479 := by
        calc
          (37 : ZMod 358321471201) ^ 1544489100 = (37 : ZMod 358321471201) ^ (772244550 + 772244550) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 772244550 * (37 : ZMod 358321471201) ^ 772244550 := by rw [pow_add]
          _ = 190971511479 := by rw [factor_8_29]; decide
      have factor_8_31 : (37 : ZMod 358321471201) ^ 3088978200 = 211649458503 := by
        calc
          (37 : ZMod 358321471201) ^ 3088978200 = (37 : ZMod 358321471201) ^ (1544489100 + 1544489100) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 1544489100 * (37 : ZMod 358321471201) ^ 1544489100 := by rw [pow_add]
          _ = 211649458503 := by rw [factor_8_30]; decide
      have factor_8_32 : (37 : ZMod 358321471201) ^ 6177956400 = 162139141232 := by
        calc
          (37 : ZMod 358321471201) ^ 6177956400 = (37 : ZMod 358321471201) ^ (3088978200 + 3088978200) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 3088978200 * (37 : ZMod 358321471201) ^ 3088978200 := by rw [pow_add]
          _ = 162139141232 := by rw [factor_8_31]; decide
      have factor_8_33 : (37 : ZMod 358321471201) ^ 12355912800 = 91740077342 := by
        calc
          (37 : ZMod 358321471201) ^ 12355912800 = (37 : ZMod 358321471201) ^ (6177956400 + 6177956400) :=
            congrArg (fun n : ℕ => (37 : ZMod 358321471201) ^ n) (by norm_num)
          _ = (37 : ZMod 358321471201) ^ 6177956400 * (37 : ZMod 358321471201) ^ 6177956400 := by rw [pow_add]
          _ = 91740077342 := by rw [factor_8_32]; decide
      change (37 : ZMod 358321471201) ^ 12355912800 ≠ 1
      rw [factor_8_33]
      decide

#print axioms prime_lucas_358321471201

end TotientTailPeriodKiller
end Erdos249257
