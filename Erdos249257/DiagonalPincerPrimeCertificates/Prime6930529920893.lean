import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1732632480223

/-! A bounded Lucas certificate for one t=41 prime leaf. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem prime_lucas_6930529920893 : Nat.Prime 6930529920893 := by
  apply lucas_primality 6930529920893 (2 : ZMod 6930529920893)
  ·
      have fermat_0 : (2 : ZMod 6930529920893) ^ 1 = 2 := by norm_num
      have fermat_1 : (2 : ZMod 6930529920893) ^ 3 = 8 := by
        calc
          (2 : ZMod 6930529920893) ^ 3 = (2 : ZMod 6930529920893) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 1 * (2 : ZMod 6930529920893) ^ 1) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [fermat_0]; decide
      have fermat_2 : (2 : ZMod 6930529920893) ^ 6 = 64 := by
        calc
          (2 : ZMod 6930529920893) ^ 6 = (2 : ZMod 6930529920893) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 3 * (2 : ZMod 6930529920893) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [fermat_1]; decide
      have fermat_3 : (2 : ZMod 6930529920893) ^ 12 = 4096 := by
        calc
          (2 : ZMod 6930529920893) ^ 12 = (2 : ZMod 6930529920893) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 6 * (2 : ZMod 6930529920893) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [fermat_2]; decide
      have fermat_4 : (2 : ZMod 6930529920893) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 6930529920893) ^ 25 = (2 : ZMod 6930529920893) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 12 * (2 : ZMod 6930529920893) ^ 12) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [fermat_3]; decide
      have fermat_5 : (2 : ZMod 6930529920893) ^ 50 = 3154059657958 := by
        calc
          (2 : ZMod 6930529920893) ^ 50 = (2 : ZMod 6930529920893) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 25 * (2 : ZMod 6930529920893) ^ 25 := by rw [pow_add]
          _ = 3154059657958 := by rw [fermat_4]; decide
      have fermat_6 : (2 : ZMod 6930529920893) ^ 100 = 493944501177 := by
        calc
          (2 : ZMod 6930529920893) ^ 100 = (2 : ZMod 6930529920893) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 50 * (2 : ZMod 6930529920893) ^ 50 := by rw [pow_add]
          _ = 493944501177 := by rw [fermat_5]; decide
      have fermat_7 : (2 : ZMod 6930529920893) ^ 201 = 4563774203910 := by
        calc
          (2 : ZMod 6930529920893) ^ 201 = (2 : ZMod 6930529920893) ^ (100 + 100 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 100 * (2 : ZMod 6930529920893) ^ 100) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 4563774203910 := by rw [fermat_6]; decide
      have fermat_8 : (2 : ZMod 6930529920893) ^ 403 = 2754741103559 := by
        calc
          (2 : ZMod 6930529920893) ^ 403 = (2 : ZMod 6930529920893) ^ (201 + 201 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 201 * (2 : ZMod 6930529920893) ^ 201) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 2754741103559 := by rw [fermat_7]; decide
      have fermat_9 : (2 : ZMod 6930529920893) ^ 806 = 5309966498691 := by
        calc
          (2 : ZMod 6930529920893) ^ 806 = (2 : ZMod 6930529920893) ^ (403 + 403) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 403 * (2 : ZMod 6930529920893) ^ 403 := by rw [pow_add]
          _ = 5309966498691 := by rw [fermat_8]; decide
      have fermat_10 : (2 : ZMod 6930529920893) ^ 1613 = 1183564240973 := by
        calc
          (2 : ZMod 6930529920893) ^ 1613 = (2 : ZMod 6930529920893) ^ (806 + 806 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 806 * (2 : ZMod 6930529920893) ^ 806) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 1183564240973 := by rw [fermat_9]; decide
      have fermat_11 : (2 : ZMod 6930529920893) ^ 3227 = 1726946862170 := by
        calc
          (2 : ZMod 6930529920893) ^ 3227 = (2 : ZMod 6930529920893) ^ (1613 + 1613 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 1613 * (2 : ZMod 6930529920893) ^ 1613) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 1726946862170 := by rw [fermat_10]; decide
      have fermat_12 : (2 : ZMod 6930529920893) ^ 6454 = 3043117516885 := by
        calc
          (2 : ZMod 6930529920893) ^ 6454 = (2 : ZMod 6930529920893) ^ (3227 + 3227) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 3227 * (2 : ZMod 6930529920893) ^ 3227 := by rw [pow_add]
          _ = 3043117516885 := by rw [fermat_11]; decide
      have fermat_13 : (2 : ZMod 6930529920893) ^ 12909 = 4855679683952 := by
        calc
          (2 : ZMod 6930529920893) ^ 12909 = (2 : ZMod 6930529920893) ^ (6454 + 6454 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 6454 * (2 : ZMod 6930529920893) ^ 6454) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 4855679683952 := by rw [fermat_12]; decide
      have fermat_14 : (2 : ZMod 6930529920893) ^ 25818 = 2919775293296 := by
        calc
          (2 : ZMod 6930529920893) ^ 25818 = (2 : ZMod 6930529920893) ^ (12909 + 12909) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 12909 * (2 : ZMod 6930529920893) ^ 12909 := by rw [pow_add]
          _ = 2919775293296 := by rw [fermat_13]; decide
      have fermat_15 : (2 : ZMod 6930529920893) ^ 51636 = 4709906641004 := by
        calc
          (2 : ZMod 6930529920893) ^ 51636 = (2 : ZMod 6930529920893) ^ (25818 + 25818) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 25818 * (2 : ZMod 6930529920893) ^ 25818 := by rw [pow_add]
          _ = 4709906641004 := by rw [fermat_14]; decide
      have fermat_16 : (2 : ZMod 6930529920893) ^ 103272 = 951510643890 := by
        calc
          (2 : ZMod 6930529920893) ^ 103272 = (2 : ZMod 6930529920893) ^ (51636 + 51636) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 51636 * (2 : ZMod 6930529920893) ^ 51636 := by rw [pow_add]
          _ = 951510643890 := by rw [fermat_15]; decide
      have fermat_17 : (2 : ZMod 6930529920893) ^ 206545 = 3358692783651 := by
        calc
          (2 : ZMod 6930529920893) ^ 206545 = (2 : ZMod 6930529920893) ^ (103272 + 103272 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 103272 * (2 : ZMod 6930529920893) ^ 103272) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 3358692783651 := by rw [fermat_16]; decide
      have fermat_18 : (2 : ZMod 6930529920893) ^ 413091 = 4375434581574 := by
        calc
          (2 : ZMod 6930529920893) ^ 413091 = (2 : ZMod 6930529920893) ^ (206545 + 206545 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 206545 * (2 : ZMod 6930529920893) ^ 206545) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 4375434581574 := by rw [fermat_17]; decide
      have fermat_19 : (2 : ZMod 6930529920893) ^ 826183 = 918844424094 := by
        calc
          (2 : ZMod 6930529920893) ^ 826183 = (2 : ZMod 6930529920893) ^ (413091 + 413091 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 413091 * (2 : ZMod 6930529920893) ^ 413091) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 918844424094 := by rw [fermat_18]; decide
      have fermat_20 : (2 : ZMod 6930529920893) ^ 1652367 = 4489088552034 := by
        calc
          (2 : ZMod 6930529920893) ^ 1652367 = (2 : ZMod 6930529920893) ^ (826183 + 826183 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 826183 * (2 : ZMod 6930529920893) ^ 826183) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 4489088552034 := by rw [fermat_19]; decide
      have fermat_21 : (2 : ZMod 6930529920893) ^ 3304734 = 6368275946179 := by
        calc
          (2 : ZMod 6930529920893) ^ 3304734 = (2 : ZMod 6930529920893) ^ (1652367 + 1652367) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 1652367 * (2 : ZMod 6930529920893) ^ 1652367 := by rw [pow_add]
          _ = 6368275946179 := by rw [fermat_20]; decide
      have fermat_22 : (2 : ZMod 6930529920893) ^ 6609468 = 1850523298175 := by
        calc
          (2 : ZMod 6930529920893) ^ 6609468 = (2 : ZMod 6930529920893) ^ (3304734 + 3304734) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 3304734 * (2 : ZMod 6930529920893) ^ 3304734 := by rw [pow_add]
          _ = 1850523298175 := by rw [fermat_21]; decide
      have fermat_23 : (2 : ZMod 6930529920893) ^ 13218936 = 6560130637491 := by
        calc
          (2 : ZMod 6930529920893) ^ 13218936 = (2 : ZMod 6930529920893) ^ (6609468 + 6609468) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 6609468 * (2 : ZMod 6930529920893) ^ 6609468 := by rw [pow_add]
          _ = 6560130637491 := by rw [fermat_22]; decide
      have fermat_24 : (2 : ZMod 6930529920893) ^ 26437873 = 2756528107289 := by
        calc
          (2 : ZMod 6930529920893) ^ 26437873 = (2 : ZMod 6930529920893) ^ (13218936 + 13218936 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 13218936 * (2 : ZMod 6930529920893) ^ 13218936) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 2756528107289 := by rw [fermat_23]; decide
      have fermat_25 : (2 : ZMod 6930529920893) ^ 52875747 = 429256884941 := by
        calc
          (2 : ZMod 6930529920893) ^ 52875747 = (2 : ZMod 6930529920893) ^ (26437873 + 26437873 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 26437873 * (2 : ZMod 6930529920893) ^ 26437873) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 429256884941 := by rw [fermat_24]; decide
      have fermat_26 : (2 : ZMod 6930529920893) ^ 105751494 = 5537990595568 := by
        calc
          (2 : ZMod 6930529920893) ^ 105751494 = (2 : ZMod 6930529920893) ^ (52875747 + 52875747) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 52875747 * (2 : ZMod 6930529920893) ^ 52875747 := by rw [pow_add]
          _ = 5537990595568 := by rw [fermat_25]; decide
      have fermat_27 : (2 : ZMod 6930529920893) ^ 211502988 = 3054324408823 := by
        calc
          (2 : ZMod 6930529920893) ^ 211502988 = (2 : ZMod 6930529920893) ^ (105751494 + 105751494) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 105751494 * (2 : ZMod 6930529920893) ^ 105751494 := by rw [pow_add]
          _ = 3054324408823 := by rw [fermat_26]; decide
      have fermat_28 : (2 : ZMod 6930529920893) ^ 423005976 = 1187770637959 := by
        calc
          (2 : ZMod 6930529920893) ^ 423005976 = (2 : ZMod 6930529920893) ^ (211502988 + 211502988) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 211502988 * (2 : ZMod 6930529920893) ^ 211502988 := by rw [pow_add]
          _ = 1187770637959 := by rw [fermat_27]; decide
      have fermat_29 : (2 : ZMod 6930529920893) ^ 846011953 = 4963059963383 := by
        calc
          (2 : ZMod 6930529920893) ^ 846011953 = (2 : ZMod 6930529920893) ^ (423005976 + 423005976 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 423005976 * (2 : ZMod 6930529920893) ^ 423005976) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 4963059963383 := by rw [fermat_28]; decide
      have fermat_30 : (2 : ZMod 6930529920893) ^ 1692023906 = 6088171317845 := by
        calc
          (2 : ZMod 6930529920893) ^ 1692023906 = (2 : ZMod 6930529920893) ^ (846011953 + 846011953) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 846011953 * (2 : ZMod 6930529920893) ^ 846011953 := by rw [pow_add]
          _ = 6088171317845 := by rw [fermat_29]; decide
      have fermat_31 : (2 : ZMod 6930529920893) ^ 3384047812 = 2354101856642 := by
        calc
          (2 : ZMod 6930529920893) ^ 3384047812 = (2 : ZMod 6930529920893) ^ (1692023906 + 1692023906) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 1692023906 * (2 : ZMod 6930529920893) ^ 1692023906 := by rw [pow_add]
          _ = 2354101856642 := by rw [fermat_30]; decide
      have fermat_32 : (2 : ZMod 6930529920893) ^ 6768095625 = 746705081399 := by
        calc
          (2 : ZMod 6930529920893) ^ 6768095625 = (2 : ZMod 6930529920893) ^ (3384047812 + 3384047812 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 3384047812 * (2 : ZMod 6930529920893) ^ 3384047812) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 746705081399 := by rw [fermat_31]; decide
      have fermat_33 : (2 : ZMod 6930529920893) ^ 13536191251 = 5795190412077 := by
        calc
          (2 : ZMod 6930529920893) ^ 13536191251 = (2 : ZMod 6930529920893) ^ (6768095625 + 6768095625 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 6768095625 * (2 : ZMod 6930529920893) ^ 6768095625) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 5795190412077 := by rw [fermat_32]; decide
      have fermat_34 : (2 : ZMod 6930529920893) ^ 27072382503 = 2111747695559 := by
        calc
          (2 : ZMod 6930529920893) ^ 27072382503 = (2 : ZMod 6930529920893) ^ (13536191251 + 13536191251 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 13536191251 * (2 : ZMod 6930529920893) ^ 13536191251) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 2111747695559 := by rw [fermat_33]; decide
      have fermat_35 : (2 : ZMod 6930529920893) ^ 54144765006 = 6072634165082 := by
        calc
          (2 : ZMod 6930529920893) ^ 54144765006 = (2 : ZMod 6930529920893) ^ (27072382503 + 27072382503) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 27072382503 * (2 : ZMod 6930529920893) ^ 27072382503 := by rw [pow_add]
          _ = 6072634165082 := by rw [fermat_34]; decide
      have fermat_36 : (2 : ZMod 6930529920893) ^ 108289530013 = 1616965081958 := by
        calc
          (2 : ZMod 6930529920893) ^ 108289530013 = (2 : ZMod 6930529920893) ^ (54144765006 + 54144765006 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 54144765006 * (2 : ZMod 6930529920893) ^ 54144765006) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 1616965081958 := by rw [fermat_35]; decide
      have fermat_37 : (2 : ZMod 6930529920893) ^ 216579060027 = 172725982230 := by
        calc
          (2 : ZMod 6930529920893) ^ 216579060027 = (2 : ZMod 6930529920893) ^ (108289530013 + 108289530013 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 108289530013 * (2 : ZMod 6930529920893) ^ 108289530013) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 172725982230 := by rw [fermat_36]; decide
      have fermat_38 : (2 : ZMod 6930529920893) ^ 433158120055 = 2045650650747 := by
        calc
          (2 : ZMod 6930529920893) ^ 433158120055 = (2 : ZMod 6930529920893) ^ (216579060027 + 216579060027 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 216579060027 * (2 : ZMod 6930529920893) ^ 216579060027) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 2045650650747 := by rw [fermat_37]; decide
      have fermat_39 : (2 : ZMod 6930529920893) ^ 866316240111 = 5217900354870 := by
        calc
          (2 : ZMod 6930529920893) ^ 866316240111 = (2 : ZMod 6930529920893) ^ (433158120055 + 433158120055 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 433158120055 * (2 : ZMod 6930529920893) ^ 433158120055) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 5217900354870 := by rw [fermat_38]; decide
      have fermat_40 : (2 : ZMod 6930529920893) ^ 1732632480223 = 3425259132045 := by
        calc
          (2 : ZMod 6930529920893) ^ 1732632480223 = (2 : ZMod 6930529920893) ^ (866316240111 + 866316240111 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 866316240111 * (2 : ZMod 6930529920893) ^ 866316240111) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 3425259132045 := by rw [fermat_39]; decide
      have fermat_41 : (2 : ZMod 6930529920893) ^ 3465264960446 = 6930529920892 := by
        calc
          (2 : ZMod 6930529920893) ^ 3465264960446 = (2 : ZMod 6930529920893) ^ (1732632480223 + 1732632480223) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 1732632480223 * (2 : ZMod 6930529920893) ^ 1732632480223 := by rw [pow_add]
          _ = 6930529920892 := by rw [fermat_40]; decide
      have fermat_42 : (2 : ZMod 6930529920893) ^ 6930529920892 = 1 := by
        calc
          (2 : ZMod 6930529920893) ^ 6930529920892 = (2 : ZMod 6930529920893) ^ (3465264960446 + 3465264960446) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 3465264960446 * (2 : ZMod 6930529920893) ^ 3465264960446 := by rw [pow_add]
          _ = 1 := by rw [fermat_41]; decide
      simpa using fermat_42
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (1732632480223, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (1732632480223, 1)] : List FactorBlock).map factorBlockValue).prod = 6930529920893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · norm_num
      · exact prime_lucas_1732632480223) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    ·
      have factor_0_0 : (2 : ZMod 6930529920893) ^ 1 = 2 := by norm_num
      have factor_0_1 : (2 : ZMod 6930529920893) ^ 3 = 8 := by
        calc
          (2 : ZMod 6930529920893) ^ 3 = (2 : ZMod 6930529920893) ^ (1 + 1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 1 * (2 : ZMod 6930529920893) ^ 1) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 8 := by rw [factor_0_0]; decide
      have factor_0_2 : (2 : ZMod 6930529920893) ^ 6 = 64 := by
        calc
          (2 : ZMod 6930529920893) ^ 6 = (2 : ZMod 6930529920893) ^ (3 + 3) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 3 * (2 : ZMod 6930529920893) ^ 3 := by rw [pow_add]
          _ = 64 := by rw [factor_0_1]; decide
      have factor_0_3 : (2 : ZMod 6930529920893) ^ 12 = 4096 := by
        calc
          (2 : ZMod 6930529920893) ^ 12 = (2 : ZMod 6930529920893) ^ (6 + 6) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 6 * (2 : ZMod 6930529920893) ^ 6 := by rw [pow_add]
          _ = 4096 := by rw [factor_0_2]; decide
      have factor_0_4 : (2 : ZMod 6930529920893) ^ 25 = 33554432 := by
        calc
          (2 : ZMod 6930529920893) ^ 25 = (2 : ZMod 6930529920893) ^ (12 + 12 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 12 * (2 : ZMod 6930529920893) ^ 12) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 33554432 := by rw [factor_0_3]; decide
      have factor_0_5 : (2 : ZMod 6930529920893) ^ 50 = 3154059657958 := by
        calc
          (2 : ZMod 6930529920893) ^ 50 = (2 : ZMod 6930529920893) ^ (25 + 25) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 25 * (2 : ZMod 6930529920893) ^ 25 := by rw [pow_add]
          _ = 3154059657958 := by rw [factor_0_4]; decide
      have factor_0_6 : (2 : ZMod 6930529920893) ^ 100 = 493944501177 := by
        calc
          (2 : ZMod 6930529920893) ^ 100 = (2 : ZMod 6930529920893) ^ (50 + 50) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 50 * (2 : ZMod 6930529920893) ^ 50 := by rw [pow_add]
          _ = 493944501177 := by rw [factor_0_5]; decide
      have factor_0_7 : (2 : ZMod 6930529920893) ^ 201 = 4563774203910 := by
        calc
          (2 : ZMod 6930529920893) ^ 201 = (2 : ZMod 6930529920893) ^ (100 + 100 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 100 * (2 : ZMod 6930529920893) ^ 100) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 4563774203910 := by rw [factor_0_6]; decide
      have factor_0_8 : (2 : ZMod 6930529920893) ^ 403 = 2754741103559 := by
        calc
          (2 : ZMod 6930529920893) ^ 403 = (2 : ZMod 6930529920893) ^ (201 + 201 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 201 * (2 : ZMod 6930529920893) ^ 201) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 2754741103559 := by rw [factor_0_7]; decide
      have factor_0_9 : (2 : ZMod 6930529920893) ^ 806 = 5309966498691 := by
        calc
          (2 : ZMod 6930529920893) ^ 806 = (2 : ZMod 6930529920893) ^ (403 + 403) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 403 * (2 : ZMod 6930529920893) ^ 403 := by rw [pow_add]
          _ = 5309966498691 := by rw [factor_0_8]; decide
      have factor_0_10 : (2 : ZMod 6930529920893) ^ 1613 = 1183564240973 := by
        calc
          (2 : ZMod 6930529920893) ^ 1613 = (2 : ZMod 6930529920893) ^ (806 + 806 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 806 * (2 : ZMod 6930529920893) ^ 806) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 1183564240973 := by rw [factor_0_9]; decide
      have factor_0_11 : (2 : ZMod 6930529920893) ^ 3227 = 1726946862170 := by
        calc
          (2 : ZMod 6930529920893) ^ 3227 = (2 : ZMod 6930529920893) ^ (1613 + 1613 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 1613 * (2 : ZMod 6930529920893) ^ 1613) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 1726946862170 := by rw [factor_0_10]; decide
      have factor_0_12 : (2 : ZMod 6930529920893) ^ 6454 = 3043117516885 := by
        calc
          (2 : ZMod 6930529920893) ^ 6454 = (2 : ZMod 6930529920893) ^ (3227 + 3227) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 3227 * (2 : ZMod 6930529920893) ^ 3227 := by rw [pow_add]
          _ = 3043117516885 := by rw [factor_0_11]; decide
      have factor_0_13 : (2 : ZMod 6930529920893) ^ 12909 = 4855679683952 := by
        calc
          (2 : ZMod 6930529920893) ^ 12909 = (2 : ZMod 6930529920893) ^ (6454 + 6454 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 6454 * (2 : ZMod 6930529920893) ^ 6454) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 4855679683952 := by rw [factor_0_12]; decide
      have factor_0_14 : (2 : ZMod 6930529920893) ^ 25818 = 2919775293296 := by
        calc
          (2 : ZMod 6930529920893) ^ 25818 = (2 : ZMod 6930529920893) ^ (12909 + 12909) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 12909 * (2 : ZMod 6930529920893) ^ 12909 := by rw [pow_add]
          _ = 2919775293296 := by rw [factor_0_13]; decide
      have factor_0_15 : (2 : ZMod 6930529920893) ^ 51636 = 4709906641004 := by
        calc
          (2 : ZMod 6930529920893) ^ 51636 = (2 : ZMod 6930529920893) ^ (25818 + 25818) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 25818 * (2 : ZMod 6930529920893) ^ 25818 := by rw [pow_add]
          _ = 4709906641004 := by rw [factor_0_14]; decide
      have factor_0_16 : (2 : ZMod 6930529920893) ^ 103272 = 951510643890 := by
        calc
          (2 : ZMod 6930529920893) ^ 103272 = (2 : ZMod 6930529920893) ^ (51636 + 51636) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 51636 * (2 : ZMod 6930529920893) ^ 51636 := by rw [pow_add]
          _ = 951510643890 := by rw [factor_0_15]; decide
      have factor_0_17 : (2 : ZMod 6930529920893) ^ 206545 = 3358692783651 := by
        calc
          (2 : ZMod 6930529920893) ^ 206545 = (2 : ZMod 6930529920893) ^ (103272 + 103272 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 103272 * (2 : ZMod 6930529920893) ^ 103272) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 3358692783651 := by rw [factor_0_16]; decide
      have factor_0_18 : (2 : ZMod 6930529920893) ^ 413091 = 4375434581574 := by
        calc
          (2 : ZMod 6930529920893) ^ 413091 = (2 : ZMod 6930529920893) ^ (206545 + 206545 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 206545 * (2 : ZMod 6930529920893) ^ 206545) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 4375434581574 := by rw [factor_0_17]; decide
      have factor_0_19 : (2 : ZMod 6930529920893) ^ 826183 = 918844424094 := by
        calc
          (2 : ZMod 6930529920893) ^ 826183 = (2 : ZMod 6930529920893) ^ (413091 + 413091 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 413091 * (2 : ZMod 6930529920893) ^ 413091) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 918844424094 := by rw [factor_0_18]; decide
      have factor_0_20 : (2 : ZMod 6930529920893) ^ 1652367 = 4489088552034 := by
        calc
          (2 : ZMod 6930529920893) ^ 1652367 = (2 : ZMod 6930529920893) ^ (826183 + 826183 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 826183 * (2 : ZMod 6930529920893) ^ 826183) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 4489088552034 := by rw [factor_0_19]; decide
      have factor_0_21 : (2 : ZMod 6930529920893) ^ 3304734 = 6368275946179 := by
        calc
          (2 : ZMod 6930529920893) ^ 3304734 = (2 : ZMod 6930529920893) ^ (1652367 + 1652367) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 1652367 * (2 : ZMod 6930529920893) ^ 1652367 := by rw [pow_add]
          _ = 6368275946179 := by rw [factor_0_20]; decide
      have factor_0_22 : (2 : ZMod 6930529920893) ^ 6609468 = 1850523298175 := by
        calc
          (2 : ZMod 6930529920893) ^ 6609468 = (2 : ZMod 6930529920893) ^ (3304734 + 3304734) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 3304734 * (2 : ZMod 6930529920893) ^ 3304734 := by rw [pow_add]
          _ = 1850523298175 := by rw [factor_0_21]; decide
      have factor_0_23 : (2 : ZMod 6930529920893) ^ 13218936 = 6560130637491 := by
        calc
          (2 : ZMod 6930529920893) ^ 13218936 = (2 : ZMod 6930529920893) ^ (6609468 + 6609468) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 6609468 * (2 : ZMod 6930529920893) ^ 6609468 := by rw [pow_add]
          _ = 6560130637491 := by rw [factor_0_22]; decide
      have factor_0_24 : (2 : ZMod 6930529920893) ^ 26437873 = 2756528107289 := by
        calc
          (2 : ZMod 6930529920893) ^ 26437873 = (2 : ZMod 6930529920893) ^ (13218936 + 13218936 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 13218936 * (2 : ZMod 6930529920893) ^ 13218936) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 2756528107289 := by rw [factor_0_23]; decide
      have factor_0_25 : (2 : ZMod 6930529920893) ^ 52875747 = 429256884941 := by
        calc
          (2 : ZMod 6930529920893) ^ 52875747 = (2 : ZMod 6930529920893) ^ (26437873 + 26437873 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 26437873 * (2 : ZMod 6930529920893) ^ 26437873) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 429256884941 := by rw [factor_0_24]; decide
      have factor_0_26 : (2 : ZMod 6930529920893) ^ 105751494 = 5537990595568 := by
        calc
          (2 : ZMod 6930529920893) ^ 105751494 = (2 : ZMod 6930529920893) ^ (52875747 + 52875747) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 52875747 * (2 : ZMod 6930529920893) ^ 52875747 := by rw [pow_add]
          _ = 5537990595568 := by rw [factor_0_25]; decide
      have factor_0_27 : (2 : ZMod 6930529920893) ^ 211502988 = 3054324408823 := by
        calc
          (2 : ZMod 6930529920893) ^ 211502988 = (2 : ZMod 6930529920893) ^ (105751494 + 105751494) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 105751494 * (2 : ZMod 6930529920893) ^ 105751494 := by rw [pow_add]
          _ = 3054324408823 := by rw [factor_0_26]; decide
      have factor_0_28 : (2 : ZMod 6930529920893) ^ 423005976 = 1187770637959 := by
        calc
          (2 : ZMod 6930529920893) ^ 423005976 = (2 : ZMod 6930529920893) ^ (211502988 + 211502988) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 211502988 * (2 : ZMod 6930529920893) ^ 211502988 := by rw [pow_add]
          _ = 1187770637959 := by rw [factor_0_27]; decide
      have factor_0_29 : (2 : ZMod 6930529920893) ^ 846011953 = 4963059963383 := by
        calc
          (2 : ZMod 6930529920893) ^ 846011953 = (2 : ZMod 6930529920893) ^ (423005976 + 423005976 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 423005976 * (2 : ZMod 6930529920893) ^ 423005976) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 4963059963383 := by rw [factor_0_28]; decide
      have factor_0_30 : (2 : ZMod 6930529920893) ^ 1692023906 = 6088171317845 := by
        calc
          (2 : ZMod 6930529920893) ^ 1692023906 = (2 : ZMod 6930529920893) ^ (846011953 + 846011953) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 846011953 * (2 : ZMod 6930529920893) ^ 846011953 := by rw [pow_add]
          _ = 6088171317845 := by rw [factor_0_29]; decide
      have factor_0_31 : (2 : ZMod 6930529920893) ^ 3384047812 = 2354101856642 := by
        calc
          (2 : ZMod 6930529920893) ^ 3384047812 = (2 : ZMod 6930529920893) ^ (1692023906 + 1692023906) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 1692023906 * (2 : ZMod 6930529920893) ^ 1692023906 := by rw [pow_add]
          _ = 2354101856642 := by rw [factor_0_30]; decide
      have factor_0_32 : (2 : ZMod 6930529920893) ^ 6768095625 = 746705081399 := by
        calc
          (2 : ZMod 6930529920893) ^ 6768095625 = (2 : ZMod 6930529920893) ^ (3384047812 + 3384047812 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 3384047812 * (2 : ZMod 6930529920893) ^ 3384047812) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 746705081399 := by rw [factor_0_31]; decide
      have factor_0_33 : (2 : ZMod 6930529920893) ^ 13536191251 = 5795190412077 := by
        calc
          (2 : ZMod 6930529920893) ^ 13536191251 = (2 : ZMod 6930529920893) ^ (6768095625 + 6768095625 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 6768095625 * (2 : ZMod 6930529920893) ^ 6768095625) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 5795190412077 := by rw [factor_0_32]; decide
      have factor_0_34 : (2 : ZMod 6930529920893) ^ 27072382503 = 2111747695559 := by
        calc
          (2 : ZMod 6930529920893) ^ 27072382503 = (2 : ZMod 6930529920893) ^ (13536191251 + 13536191251 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 13536191251 * (2 : ZMod 6930529920893) ^ 13536191251) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 2111747695559 := by rw [factor_0_33]; decide
      have factor_0_35 : (2 : ZMod 6930529920893) ^ 54144765006 = 6072634165082 := by
        calc
          (2 : ZMod 6930529920893) ^ 54144765006 = (2 : ZMod 6930529920893) ^ (27072382503 + 27072382503) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 27072382503 * (2 : ZMod 6930529920893) ^ 27072382503 := by rw [pow_add]
          _ = 6072634165082 := by rw [factor_0_34]; decide
      have factor_0_36 : (2 : ZMod 6930529920893) ^ 108289530013 = 1616965081958 := by
        calc
          (2 : ZMod 6930529920893) ^ 108289530013 = (2 : ZMod 6930529920893) ^ (54144765006 + 54144765006 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 54144765006 * (2 : ZMod 6930529920893) ^ 54144765006) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 1616965081958 := by rw [factor_0_35]; decide
      have factor_0_37 : (2 : ZMod 6930529920893) ^ 216579060027 = 172725982230 := by
        calc
          (2 : ZMod 6930529920893) ^ 216579060027 = (2 : ZMod 6930529920893) ^ (108289530013 + 108289530013 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 108289530013 * (2 : ZMod 6930529920893) ^ 108289530013) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 172725982230 := by rw [factor_0_36]; decide
      have factor_0_38 : (2 : ZMod 6930529920893) ^ 433158120055 = 2045650650747 := by
        calc
          (2 : ZMod 6930529920893) ^ 433158120055 = (2 : ZMod 6930529920893) ^ (216579060027 + 216579060027 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 216579060027 * (2 : ZMod 6930529920893) ^ 216579060027) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 2045650650747 := by rw [factor_0_37]; decide
      have factor_0_39 : (2 : ZMod 6930529920893) ^ 866316240111 = 5217900354870 := by
        calc
          (2 : ZMod 6930529920893) ^ 866316240111 = (2 : ZMod 6930529920893) ^ (433158120055 + 433158120055 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 433158120055 * (2 : ZMod 6930529920893) ^ 433158120055) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 5217900354870 := by rw [factor_0_38]; decide
      have factor_0_40 : (2 : ZMod 6930529920893) ^ 1732632480223 = 3425259132045 := by
        calc
          (2 : ZMod 6930529920893) ^ 1732632480223 = (2 : ZMod 6930529920893) ^ (866316240111 + 866316240111 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = ((2 : ZMod 6930529920893) ^ 866316240111 * (2 : ZMod 6930529920893) ^ 866316240111) * (2 : ZMod 6930529920893) := by rw [pow_succ, pow_add]
          _ = 3425259132045 := by rw [factor_0_39]; decide
      have factor_0_41 : (2 : ZMod 6930529920893) ^ 3465264960446 = 6930529920892 := by
        calc
          (2 : ZMod 6930529920893) ^ 3465264960446 = (2 : ZMod 6930529920893) ^ (1732632480223 + 1732632480223) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 1732632480223 * (2 : ZMod 6930529920893) ^ 1732632480223 := by rw [pow_add]
          _ = 6930529920892 := by rw [factor_0_40]; decide
      change (2 : ZMod 6930529920893) ^ 3465264960446 ≠ 1
      rw [factor_0_41]
      decide
    ·
      have factor_1_0 : (2 : ZMod 6930529920893) ^ 1 = 2 := by norm_num
      have factor_1_1 : (2 : ZMod 6930529920893) ^ 2 = 4 := by
        calc
          (2 : ZMod 6930529920893) ^ 2 = (2 : ZMod 6930529920893) ^ (1 + 1) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 1 * (2 : ZMod 6930529920893) ^ 1 := by rw [pow_add]
          _ = 4 := by rw [factor_1_0]; decide
      have factor_1_2 : (2 : ZMod 6930529920893) ^ 4 = 16 := by
        calc
          (2 : ZMod 6930529920893) ^ 4 = (2 : ZMod 6930529920893) ^ (2 + 2) :=
            congrArg (fun n : ℕ => (2 : ZMod 6930529920893) ^ n) (by norm_num)
          _ = (2 : ZMod 6930529920893) ^ 2 * (2 : ZMod 6930529920893) ^ 2 := by rw [pow_add]
          _ = 16 := by rw [factor_1_1]; decide
      change (2 : ZMod 6930529920893) ^ 4 ≠ 1
      rw [factor_1_2]
      decide

#print axioms prime_lucas_6930529920893

end TotientTailPeriodKiller
end Erdos249257
