import LegendreK6.Pratt.Block000

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LegendreK6.Pratt

theorem prime_1229 : Nat.Prime 1229 := by
  apply lucas_primality 1229 (2 : ZMod 1229)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1229 - 1 = (2 : ℕ)^2 * ((307 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1229)^614 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 307 := Nat.prime_eq_prime_of_dvd_pow hq prime_307 hd
      subst q
      change (2 : ZMod 1229)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_1231 : Nat.Prime 1231 := by
  apply lucas_primality 1231 (3 : ZMod 1231)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1231 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((41 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1231)^615 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1231)^410 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 1231)^246 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (3 : ZMod 1231)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_1237 : Nat.Prime 1237 := by
  apply lucas_primality 1237 (2 : ZMod 1237)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1237 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((103 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1237)^618 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1237)^412 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
        subst q
        change (2 : ZMod 1237)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_1249 : Nat.Prime 1249 := by
  apply lucas_primality 1249 (7 : ZMod 1249)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1249 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((13 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1249)^624 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 1249)^416 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (7 : ZMod 1249)^96 ≠ 1
        reduce_mod_char
        decide

theorem prime_1259 : Nat.Prime 1259 := by
  apply lucas_primality 1259 (2 : ZMod 1259)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1259 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((37 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1259)^629 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 1259)^74 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (2 : ZMod 1259)^34 ≠ 1
        reduce_mod_char
        decide

theorem prime_1277 : Nat.Prime 1277 := by
  apply lucas_primality 1277 (2 : ZMod 1277)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1277 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((29 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1277)^638 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 1277)^116 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (2 : ZMod 1277)^44 ≠ 1
        reduce_mod_char
        decide

theorem prime_1279 : Nat.Prime 1279 := by
  apply lucas_primality 1279 (3 : ZMod 1279)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1279 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((71 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1279)^639 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1279)^426 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
        subst q
        change (3 : ZMod 1279)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_1283 : Nat.Prime 1283 := by
  apply lucas_primality 1283 (2 : ZMod 1283)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1283 - 1 = (2 : ℕ)^1 * ((641 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1283)^641 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 641 := Nat.prime_eq_prime_of_dvd_pow hq prime_641 hd
      subst q
      change (2 : ZMod 1283)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_1289 : Nat.Prime 1289 := by
  apply lucas_primality 1289 (6 : ZMod 1289)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1289 - 1 = (2 : ℕ)^3 * ((7 : ℕ)^1 * ((23 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 1289)^644 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (6 : ZMod 1289)^184 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (6 : ZMod 1289)^56 ≠ 1
        reduce_mod_char
        decide

theorem prime_1291 : Nat.Prime 1291 := by
  apply lucas_primality 1291 (2 : ZMod 1291)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1291 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((43 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1291)^645 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1291)^430 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 1291)^258 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (2 : ZMod 1291)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_1297 : Nat.Prime 1297 := by
  apply lucas_primality 1297 (10 : ZMod 1297)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1297 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^4) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 1297)^648 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
      subst q
      change (10 : ZMod 1297)^432 ≠ 1
      reduce_mod_char
      decide

theorem prime_1301 : Nat.Prime 1301 := by
  apply lucas_primality 1301 (2 : ZMod 1301)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1301 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((13 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1301)^650 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 1301)^260 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 1301)^100 ≠ 1
        reduce_mod_char
        decide

theorem prime_1303 : Nat.Prime 1303 := by
  apply lucas_primality 1303 (6 : ZMod 1303)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1303 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((31 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 1303)^651 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 1303)^434 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 1303)^186 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (6 : ZMod 1303)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_1307 : Nat.Prime 1307 := by
  apply lucas_primality 1307 (2 : ZMod 1307)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1307 - 1 = (2 : ℕ)^1 * ((653 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1307)^653 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 653 := Nat.prime_eq_prime_of_dvd_pow hq prime_653 hd
      subst q
      change (2 : ZMod 1307)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_1319 : Nat.Prime 1319 := by
  apply lucas_primality 1319 (13 : ZMod 1319)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1319 - 1 = (2 : ℕ)^1 * ((659 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 1319)^659 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 659 := Nat.prime_eq_prime_of_dvd_pow hq prime_659 hd
      subst q
      change (13 : ZMod 1319)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_1321 : Nat.Prime 1321 := by
  apply lucas_primality 1321 (13 : ZMod 1321)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1321 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 1321)^660 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 1321)^440 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 1321)^264 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (13 : ZMod 1321)^120 ≠ 1
          reduce_mod_char
          decide

theorem prime_1327 : Nat.Prime 1327 := by
  apply lucas_primality 1327 (3 : ZMod 1327)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1327 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((17 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1327)^663 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1327)^442 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 1327)^102 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (3 : ZMod 1327)^78 ≠ 1
          reduce_mod_char
          decide

theorem prime_1361 : Nat.Prime 1361 := by
  apply lucas_primality 1361 (3 : ZMod 1361)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1361 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((17 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1361)^680 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 1361)^272 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (3 : ZMod 1361)^80 ≠ 1
        reduce_mod_char
        decide

theorem prime_1367 : Nat.Prime 1367 := by
  apply lucas_primality 1367 (5 : ZMod 1367)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1367 - 1 = (2 : ℕ)^1 * ((683 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1367)^683 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 683 := Nat.prime_eq_prime_of_dvd_pow hq prime_683 hd
      subst q
      change (5 : ZMod 1367)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_1373 : Nat.Prime 1373 := by
  apply lucas_primality 1373 (2 : ZMod 1373)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1373 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^3) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1373)^686 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
      subst q
      change (2 : ZMod 1373)^196 ≠ 1
      reduce_mod_char
      decide

theorem prime_1381 : Nat.Prime 1381 := by
  apply lucas_primality 1381 (2 : ZMod 1381)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1381 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((23 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1381)^690 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1381)^460 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 1381)^276 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 1381)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_1399 : Nat.Prime 1399 := by
  apply lucas_primality 1399 (13 : ZMod 1399)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1399 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((233 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 1399)^699 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 1399)^466 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
        subst q
        change (13 : ZMod 1399)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_1409 : Nat.Prime 1409 := by
  apply lucas_primality 1409 (3 : ZMod 1409)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1409 - 1 = (2 : ℕ)^7 * ((11 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1409)^704 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
      subst q
      change (3 : ZMod 1409)^128 ≠ 1
      reduce_mod_char
      decide

theorem prime_1423 : Nat.Prime 1423 := by
  apply lucas_primality 1423 (3 : ZMod 1423)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1423 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((79 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1423)^711 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1423)^474 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
        subst q
        change (3 : ZMod 1423)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_1427 : Nat.Prime 1427 := by
  apply lucas_primality 1427 (2 : ZMod 1427)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1427 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((31 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1427)^713 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (2 : ZMod 1427)^62 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (2 : ZMod 1427)^46 ≠ 1
        reduce_mod_char
        decide

theorem prime_1429 : Nat.Prime 1429 := by
  apply lucas_primality 1429 (6 : ZMod 1429)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1429 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((17 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 1429)^714 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 1429)^476 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 1429)^204 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (6 : ZMod 1429)^84 ≠ 1
          reduce_mod_char
          decide

theorem prime_1433 : Nat.Prime 1433 := by
  apply lucas_primality 1433 (3 : ZMod 1433)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1433 - 1 = (2 : ℕ)^3 * ((179 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1433)^716 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 179 := Nat.prime_eq_prime_of_dvd_pow hq prime_179 hd
      subst q
      change (3 : ZMod 1433)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_1439 : Nat.Prime 1439 := by
  apply lucas_primality 1439 (7 : ZMod 1439)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1439 - 1 = (2 : ℕ)^1 * ((719 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1439)^719 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 719 := Nat.prime_eq_prime_of_dvd_pow hq prime_719 hd
      subst q
      change (7 : ZMod 1439)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_1447 : Nat.Prime 1447 := by
  apply lucas_primality 1447 (3 : ZMod 1447)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1447 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((241 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1447)^723 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1447)^482 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 241 := Nat.prime_eq_prime_of_dvd_pow hq prime_241 hd
        subst q
        change (3 : ZMod 1447)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_1451 : Nat.Prime 1451 := by
  apply lucas_primality 1451 (2 : ZMod 1451)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1451 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((29 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1451)^725 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 1451)^290 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (2 : ZMod 1451)^50 ≠ 1
        reduce_mod_char
        decide

theorem prime_1453 : Nat.Prime 1453 := by
  apply lucas_primality 1453 (2 : ZMod 1453)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1453 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((11 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1453)^726 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1453)^484 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 1453)^132 ≠ 1
        reduce_mod_char
        decide

theorem prime_1459 : Nat.Prime 1459 := by
  apply lucas_primality 1459 (3 : ZMod 1459)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1459 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^6) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1459)^729 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
      subst q
      change (3 : ZMod 1459)^486 ≠ 1
      reduce_mod_char
      decide

theorem prime_1471 : Nat.Prime 1471 := by
  apply lucas_primality 1471 (6 : ZMod 1471)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1471 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^2))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 1471)^735 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 1471)^490 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 1471)^294 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 1471)^210 ≠ 1
          reduce_mod_char
          decide

theorem prime_1481 : Nat.Prime 1481 := by
  apply lucas_primality 1481 (3 : ZMod 1481)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1481 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((37 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1481)^740 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 1481)^296 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (3 : ZMod 1481)^40 ≠ 1
        reduce_mod_char
        decide

theorem prime_1483 : Nat.Prime 1483 := by
  apply lucas_primality 1483 (2 : ZMod 1483)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1483 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((19 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1483)^741 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1483)^494 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 1483)^114 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 1483)^78 ≠ 1
          reduce_mod_char
          decide

theorem prime_1487 : Nat.Prime 1487 := by
  apply lucas_primality 1487 (5 : ZMod 1487)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1487 - 1 = (2 : ℕ)^1 * ((743 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1487)^743 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 743 := Nat.prime_eq_prime_of_dvd_pow hq prime_743 hd
      subst q
      change (5 : ZMod 1487)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_1489 : Nat.Prime 1489 := by
  apply lucas_primality 1489 (14 : ZMod 1489)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1489 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((31 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 1489)^744 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 1489)^496 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (14 : ZMod 1489)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_1493 : Nat.Prime 1493 := by
  apply lucas_primality 1493 (2 : ZMod 1493)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1493 - 1 = (2 : ℕ)^2 * ((373 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1493)^746 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 373 := Nat.prime_eq_prime_of_dvd_pow hq prime_373 hd
      subst q
      change (2 : ZMod 1493)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_1499 : Nat.Prime 1499 := by
  apply lucas_primality 1499 (2 : ZMod 1499)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1499 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((107 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1499)^749 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 1499)^214 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
        subst q
        change (2 : ZMod 1499)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_1511 : Nat.Prime 1511 := by
  apply lucas_primality 1511 (11 : ZMod 1511)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1511 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((151 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 1511)^755 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 1511)^302 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
        subst q
        change (11 : ZMod 1511)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_1523 : Nat.Prime 1523 := by
  apply lucas_primality 1523 (2 : ZMod 1523)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1523 - 1 = (2 : ℕ)^1 * ((761 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1523)^761 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 761 := Nat.prime_eq_prime_of_dvd_pow hq prime_761 hd
      subst q
      change (2 : ZMod 1523)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_1531 : Nat.Prime 1531 := by
  apply lucas_primality 1531 (2 : ZMod 1531)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1531 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((17 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1531)^765 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1531)^510 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 1531)^306 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 1531)^90 ≠ 1
          reduce_mod_char
          decide

theorem prime_1543 : Nat.Prime 1543 := by
  apply lucas_primality 1543 (5 : ZMod 1543)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1543 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((257 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1543)^771 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1543)^514 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 257 := Nat.prime_eq_prime_of_dvd_pow hq prime_257 hd
        subst q
        change (5 : ZMod 1543)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_1549 : Nat.Prime 1549 := by
  apply lucas_primality 1549 (2 : ZMod 1549)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1549 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((43 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1549)^774 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1549)^516 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
        subst q
        change (2 : ZMod 1549)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_1553 : Nat.Prime 1553 := by
  apply lucas_primality 1553 (3 : ZMod 1553)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1553 - 1 = (2 : ℕ)^4 * ((97 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1553)^776 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
      subst q
      change (3 : ZMod 1553)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_1559 : Nat.Prime 1559 := by
  apply lucas_primality 1559 (19 : ZMod 1559)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1559 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((41 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 1559)^779 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (19 : ZMod 1559)^82 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
        subst q
        change (19 : ZMod 1559)^38 ≠ 1
        reduce_mod_char
        decide

theorem prime_1567 : Nat.Prime 1567 := by
  apply lucas_primality 1567 (3 : ZMod 1567)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1567 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((29 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1567)^783 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1567)^522 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (3 : ZMod 1567)^54 ≠ 1
        reduce_mod_char
        decide

theorem prime_1571 : Nat.Prime 1571 := by
  apply lucas_primality 1571 (2 : ZMod 1571)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1571 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((157 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1571)^785 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 1571)^314 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
        subst q
        change (2 : ZMod 1571)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_1579 : Nat.Prime 1579 := by
  apply lucas_primality 1579 (3 : ZMod 1579)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1579 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((263 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1579)^789 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1579)^526 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 263 := Nat.prime_eq_prime_of_dvd_pow hq prime_263 hd
        subst q
        change (3 : ZMod 1579)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_1583 : Nat.Prime 1583 := by
  apply lucas_primality 1583 (5 : ZMod 1583)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1583 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((113 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1583)^791 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 1583)^226 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
        subst q
        change (5 : ZMod 1583)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_1597 : Nat.Prime 1597 := by
  apply lucas_primality 1597 (11 : ZMod 1597)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1597 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((19 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 1597)^798 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 1597)^532 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (11 : ZMod 1597)^228 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (11 : ZMod 1597)^84 ≠ 1
          reduce_mod_char
          decide

theorem prime_1601 : Nat.Prime 1601 := by
  apply lucas_primality 1601 (3 : ZMod 1601)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1601 - 1 = (2 : ℕ)^6 * ((5 : ℕ)^2) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1601)^800 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
      subst q
      change (3 : ZMod 1601)^320 ≠ 1
      reduce_mod_char
      decide

theorem prime_1607 : Nat.Prime 1607 := by
  apply lucas_primality 1607 (5 : ZMod 1607)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1607 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((73 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1607)^803 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 1607)^146 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
        subst q
        change (5 : ZMod 1607)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_1609 : Nat.Prime 1609 := by
  apply lucas_primality 1609 (7 : ZMod 1609)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1609 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((67 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1609)^804 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 1609)^536 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
        subst q
        change (7 : ZMod 1609)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_1613 : Nat.Prime 1613 := by
  apply lucas_primality 1613 (3 : ZMod 1613)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1613 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((31 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1613)^806 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 1613)^124 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (3 : ZMod 1613)^52 ≠ 1
        reduce_mod_char
        decide

theorem prime_1619 : Nat.Prime 1619 := by
  apply lucas_primality 1619 (2 : ZMod 1619)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1619 - 1 = (2 : ℕ)^1 * ((809 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1619)^809 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 809 := Nat.prime_eq_prime_of_dvd_pow hq prime_809 hd
      subst q
      change (2 : ZMod 1619)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_1621 : Nat.Prime 1621 := by
  apply lucas_primality 1621 (2 : ZMod 1621)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1621 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^4 * ((5 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1621)^810 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1621)^540 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 1621)^324 ≠ 1
        reduce_mod_char
        decide

theorem prime_1627 : Nat.Prime 1627 := by
  apply lucas_primality 1627 (3 : ZMod 1627)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1627 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((271 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1627)^813 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1627)^542 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 271 := Nat.prime_eq_prime_of_dvd_pow hq prime_271 hd
        subst q
        change (3 : ZMod 1627)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_1637 : Nat.Prime 1637 := by
  apply lucas_primality 1637 (2 : ZMod 1637)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1637 - 1 = (2 : ℕ)^2 * ((409 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1637)^818 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 409 := Nat.prime_eq_prime_of_dvd_pow hq prime_409 hd
      subst q
      change (2 : ZMod 1637)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_1657 : Nat.Prime 1657 := by
  apply lucas_primality 1657 (11 : ZMod 1657)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1657 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((23 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 1657)^828 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 1657)^552 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (11 : ZMod 1657)^72 ≠ 1
        reduce_mod_char
        decide

theorem prime_1667 : Nat.Prime 1667 := by
  apply lucas_primality 1667 (2 : ZMod 1667)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1667 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^2 * ((17 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1667)^833 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 1667)^238 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 1667)^98 ≠ 1
        reduce_mod_char
        decide

theorem prime_1669 : Nat.Prime 1669 := by
  apply lucas_primality 1669 (2 : ZMod 1669)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1669 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((139 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1669)^834 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1669)^556 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
        subst q
        change (2 : ZMod 1669)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_1693 : Nat.Prime 1693 := by
  apply lucas_primality 1693 (2 : ZMod 1693)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1693 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((47 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1693)^846 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1693)^564 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (2 : ZMod 1693)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_1697 : Nat.Prime 1697 := by
  apply lucas_primality 1697 (3 : ZMod 1697)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1697 - 1 = (2 : ℕ)^5 * ((53 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1697)^848 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
      subst q
      change (3 : ZMod 1697)^32 ≠ 1
      reduce_mod_char
      decide

theorem prime_1699 : Nat.Prime 1699 := by
  apply lucas_primality 1699 (3 : ZMod 1699)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1699 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((283 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1699)^849 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1699)^566 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 283 := Nat.prime_eq_prime_of_dvd_pow hq prime_283 hd
        subst q
        change (3 : ZMod 1699)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_1709 : Nat.Prime 1709 := by
  apply lucas_primality 1709 (3 : ZMod 1709)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1709 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((61 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1709)^854 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 1709)^244 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
        subst q
        change (3 : ZMod 1709)^28 ≠ 1
        reduce_mod_char
        decide

theorem prime_1721 : Nat.Prime 1721 := by
  apply lucas_primality 1721 (3 : ZMod 1721)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1721 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((43 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1721)^860 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 1721)^344 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
        subst q
        change (3 : ZMod 1721)^40 ≠ 1
        reduce_mod_char
        decide

theorem prime_1723 : Nat.Prime 1723 := by
  apply lucas_primality 1723 (3 : ZMod 1723)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1723 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((41 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1723)^861 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1723)^574 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 1723)^246 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (3 : ZMod 1723)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_1733 : Nat.Prime 1733 := by
  apply lucas_primality 1733 (2 : ZMod 1733)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1733 - 1 = (2 : ℕ)^2 * ((433 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1733)^866 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 433 := Nat.prime_eq_prime_of_dvd_pow hq prime_433 hd
      subst q
      change (2 : ZMod 1733)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_1747 : Nat.Prime 1747 := by
  apply lucas_primality 1747 (2 : ZMod 1747)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1747 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((97 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1747)^873 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1747)^582 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
        subst q
        change (2 : ZMod 1747)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_1753 : Nat.Prime 1753 := by
  apply lucas_primality 1753 (7 : ZMod 1753)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1753 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((73 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1753)^876 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 1753)^584 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
        subst q
        change (7 : ZMod 1753)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_1759 : Nat.Prime 1759 := by
  apply lucas_primality 1759 (6 : ZMod 1759)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1759 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((293 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 1759)^879 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 1759)^586 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 293 := Nat.prime_eq_prime_of_dvd_pow hq prime_293 hd
        subst q
        change (6 : ZMod 1759)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_1777 : Nat.Prime 1777 := by
  apply lucas_primality 1777 (5 : ZMod 1777)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1777 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((37 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1777)^888 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1777)^592 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (5 : ZMod 1777)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_1783 : Nat.Prime 1783 := by
  apply lucas_primality 1783 (10 : ZMod 1783)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1783 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((11 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 1783)^891 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 1783)^594 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (10 : ZMod 1783)^162 ≠ 1
        reduce_mod_char
        decide

theorem prime_1787 : Nat.Prime 1787 := by
  apply lucas_primality 1787 (2 : ZMod 1787)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1787 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((47 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1787)^893 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 1787)^94 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (2 : ZMod 1787)^38 ≠ 1
        reduce_mod_char
        decide

theorem prime_1789 : Nat.Prime 1789 := by
  apply lucas_primality 1789 (6 : ZMod 1789)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1789 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((149 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 1789)^894 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 1789)^596 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
        subst q
        change (6 : ZMod 1789)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_1801 : Nat.Prime 1801 := by
  apply lucas_primality 1801 (11 : ZMod 1801)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1801 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((5 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 1801)^900 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 1801)^600 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 1801)^360 ≠ 1
        reduce_mod_char
        decide

theorem prime_1811 : Nat.Prime 1811 := by
  apply lucas_primality 1811 (6 : ZMod 1811)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1811 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((181 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 1811)^905 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 1811)^362 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 181 := Nat.prime_eq_prime_of_dvd_pow hq prime_181 hd
        subst q
        change (6 : ZMod 1811)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_1823 : Nat.Prime 1823 := by
  apply lucas_primality 1823 (5 : ZMod 1823)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1823 - 1 = (2 : ℕ)^1 * ((911 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1823)^911 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 911 := Nat.prime_eq_prime_of_dvd_pow hq prime_911 hd
      subst q
      change (5 : ZMod 1823)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_1831 : Nat.Prime 1831 := by
  apply lucas_primality 1831 (3 : ZMod 1831)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1831 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((61 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1831)^915 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1831)^610 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 1831)^366 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (3 : ZMod 1831)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_1847 : Nat.Prime 1847 := by
  apply lucas_primality 1847 (5 : ZMod 1847)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1847 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((71 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1847)^923 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (5 : ZMod 1847)^142 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
        subst q
        change (5 : ZMod 1847)^26 ≠ 1
        reduce_mod_char
        decide

theorem prime_1867 : Nat.Prime 1867 := by
  apply lucas_primality 1867 (2 : ZMod 1867)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1867 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((311 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1867)^933 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1867)^622 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 311 := Nat.prime_eq_prime_of_dvd_pow hq prime_311 hd
        subst q
        change (2 : ZMod 1867)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_1873 : Nat.Prime 1873 := by
  apply lucas_primality 1873 (10 : ZMod 1873)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1873 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((13 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 1873)^936 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 1873)^624 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (10 : ZMod 1873)^144 ≠ 1
        reduce_mod_char
        decide

theorem prime_1877 : Nat.Prime 1877 := by
  apply lucas_primality 1877 (2 : ZMod 1877)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1877 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((67 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1877)^938 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 1877)^268 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
        subst q
        change (2 : ZMod 1877)^28 ≠ 1
        reduce_mod_char
        decide

theorem prime_1879 : Nat.Prime 1879 := by
  apply lucas_primality 1879 (6 : ZMod 1879)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1879 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((313 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 1879)^939 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 1879)^626 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 313 := Nat.prime_eq_prime_of_dvd_pow hq prime_313 hd
        subst q
        change (6 : ZMod 1879)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_1901 : Nat.Prime 1901 := by
  apply lucas_primality 1901 (2 : ZMod 1901)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1901 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((19 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1901)^950 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 1901)^380 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 1901)^100 ≠ 1
        reduce_mod_char
        decide

theorem prime_1907 : Nat.Prime 1907 := by
  apply lucas_primality 1907 (2 : ZMod 1907)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1907 - 1 = (2 : ℕ)^1 * ((953 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1907)^953 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 953 := Nat.prime_eq_prime_of_dvd_pow hq prime_953 hd
      subst q
      change (2 : ZMod 1907)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_1913 : Nat.Prime 1913 := by
  apply lucas_primality 1913 (3 : ZMod 1913)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1913 - 1 = (2 : ℕ)^3 * ((239 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1913)^956 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 239 := Nat.prime_eq_prime_of_dvd_pow hq prime_239 hd
      subst q
      change (3 : ZMod 1913)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_1931 : Nat.Prime 1931 := by
  apply lucas_primality 1931 (2 : ZMod 1931)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1931 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((193 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1931)^965 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 1931)^386 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
        subst q
        change (2 : ZMod 1931)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_1933 : Nat.Prime 1933 := by
  apply lucas_primality 1933 (5 : ZMod 1933)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1933 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((23 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1933)^966 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1933)^644 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 1933)^276 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (5 : ZMod 1933)^84 ≠ 1
          reduce_mod_char
          decide

theorem prime_1949 : Nat.Prime 1949 := by
  apply lucas_primality 1949 (2 : ZMod 1949)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1949 - 1 = (2 : ℕ)^2 * ((487 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1949)^974 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 487 := Nat.prime_eq_prime_of_dvd_pow hq prime_487 hd
      subst q
      change (2 : ZMod 1949)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_1951 : Nat.Prime 1951 := by
  apply lucas_primality 1951 (3 : ZMod 1951)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1951 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((13 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1951)^975 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1951)^650 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 1951)^390 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 1951)^150 ≠ 1
          reduce_mod_char
          decide

theorem prime_1973 : Nat.Prime 1973 := by
  apply lucas_primality 1973 (2 : ZMod 1973)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1973 - 1 = (2 : ℕ)^2 * ((17 : ℕ)^1 * ((29 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1973)^986 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 1973)^116 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (2 : ZMod 1973)^68 ≠ 1
        reduce_mod_char
        decide

theorem prime_1987 : Nat.Prime 1987 := by
  apply lucas_primality 1987 (2 : ZMod 1987)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1987 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((331 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1987)^993 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1987)^662 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 331 := Nat.prime_eq_prime_of_dvd_pow hq prime_331 hd
        subst q
        change (2 : ZMod 1987)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_1993 : Nat.Prime 1993 := by
  apply lucas_primality 1993 (5 : ZMod 1993)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1993 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((83 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1993)^996 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1993)^664 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
        subst q
        change (5 : ZMod 1993)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_1997 : Nat.Prime 1997 := by
  apply lucas_primality 1997 (2 : ZMod 1997)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1997 - 1 = (2 : ℕ)^2 * ((499 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1997)^998 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 499 := Nat.prime_eq_prime_of_dvd_pow hq prime_499 hd
      subst q
      change (2 : ZMod 1997)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_1999 : Nat.Prime 1999 := by
  apply lucas_primality 1999 (3 : ZMod 1999)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1999 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((37 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1999)^999 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1999)^666 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (3 : ZMod 1999)^54 ≠ 1
        reduce_mod_char
        decide

theorem prime_2003 : Nat.Prime 2003 := by
  apply lucas_primality 2003 (5 : ZMod 2003)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2003 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2003)^1001 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 2003)^286 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 2003)^182 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (5 : ZMod 2003)^154 ≠ 1
          reduce_mod_char
          decide

theorem prime_2011 : Nat.Prime 2011 := by
  apply lucas_primality 2011 (3 : ZMod 2011)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2011 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((67 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2011)^1005 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 2011)^670 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 2011)^402 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (3 : ZMod 2011)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_2027 : Nat.Prime 2027 := by
  apply lucas_primality 2027 (2 : ZMod 2027)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2027 - 1 = (2 : ℕ)^1 * ((1013 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2027)^1013 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1013 := Nat.prime_eq_prime_of_dvd_pow hq prime_1013 hd
      subst q
      change (2 : ZMod 2027)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_2029 : Nat.Prime 2029 := by
  apply lucas_primality 2029 (2 : ZMod 2029)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2029 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((13 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2029)^1014 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2029)^676 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 2029)^156 ≠ 1
        reduce_mod_char
        decide

theorem prime_2039 : Nat.Prime 2039 := by
  apply lucas_primality 2039 (7 : ZMod 2039)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2039 - 1 = (2 : ℕ)^1 * ((1019 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2039)^1019 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1019 := Nat.prime_eq_prime_of_dvd_pow hq prime_1019 hd
      subst q
      change (7 : ZMod 2039)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_2053 : Nat.Prime 2053 := by
  apply lucas_primality 2053 (2 : ZMod 2053)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2053 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((19 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2053)^1026 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2053)^684 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 2053)^108 ≠ 1
        reduce_mod_char
        decide

theorem prime_2063 : Nat.Prime 2063 := by
  apply lucas_primality 2063 (5 : ZMod 2063)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2063 - 1 = (2 : ℕ)^1 * ((1031 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2063)^1031 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1031 := Nat.prime_eq_prime_of_dvd_pow hq prime_1031 hd
      subst q
      change (5 : ZMod 2063)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_2069 : Nat.Prime 2069 := by
  apply lucas_primality 2069 (2 : ZMod 2069)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2069 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((47 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2069)^1034 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 2069)^188 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (2 : ZMod 2069)^44 ≠ 1
        reduce_mod_char
        decide

theorem prime_2081 : Nat.Prime 2081 := by
  apply lucas_primality 2081 (3 : ZMod 2081)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2081 - 1 = (2 : ℕ)^5 * ((5 : ℕ)^1 * ((13 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2081)^1040 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 2081)^416 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 2081)^160 ≠ 1
        reduce_mod_char
        decide

theorem prime_2083 : Nat.Prime 2083 := by
  apply lucas_primality 2083 (2 : ZMod 2083)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2083 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((347 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2083)^1041 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2083)^694 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 347 := Nat.prime_eq_prime_of_dvd_pow hq prime_347 hd
        subst q
        change (2 : ZMod 2083)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_2087 : Nat.Prime 2087 := by
  apply lucas_primality 2087 (5 : ZMod 2087)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2087 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((149 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2087)^1043 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 2087)^298 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
        subst q
        change (5 : ZMod 2087)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_2099 : Nat.Prime 2099 := by
  apply lucas_primality 2099 (2 : ZMod 2099)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2099 - 1 = (2 : ℕ)^1 * ((1049 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2099)^1049 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1049 := Nat.prime_eq_prime_of_dvd_pow hq prime_1049 hd
      subst q
      change (2 : ZMod 2099)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_2111 : Nat.Prime 2111 := by
  apply lucas_primality 2111 (7 : ZMod 2111)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2111 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((211 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2111)^1055 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 2111)^422 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 211 := Nat.prime_eq_prime_of_dvd_pow hq prime_211 hd
        subst q
        change (7 : ZMod 2111)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_2113 : Nat.Prime 2113 := by
  apply lucas_primality 2113 (5 : ZMod 2113)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2113 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^1 * ((11 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2113)^1056 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 2113)^704 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 2113)^192 ≠ 1
        reduce_mod_char
        decide

theorem prime_2129 : Nat.Prime 2129 := by
  apply lucas_primality 2129 (3 : ZMod 2129)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2129 - 1 = (2 : ℕ)^4 * ((7 : ℕ)^1 * ((19 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2129)^1064 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 2129)^304 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (3 : ZMod 2129)^112 ≠ 1
        reduce_mod_char
        decide

theorem prime_2131 : Nat.Prime 2131 := by
  apply lucas_primality 2131 (2 : ZMod 2131)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2131 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((71 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2131)^1065 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2131)^710 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 2131)^426 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
          subst q
          change (2 : ZMod 2131)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_2137 : Nat.Prime 2137 := by
  apply lucas_primality 2137 (10 : ZMod 2137)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2137 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((89 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 2137)^1068 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 2137)^712 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
        subst q
        change (10 : ZMod 2137)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_2141 : Nat.Prime 2141 := by
  apply lucas_primality 2141 (2 : ZMod 2141)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2141 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((107 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2141)^1070 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 2141)^428 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
        subst q
        change (2 : ZMod 2141)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_2143 : Nat.Prime 2143 := by
  apply lucas_primality 2143 (3 : ZMod 2143)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2143 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((17 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2143)^1071 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 2143)^714 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 2143)^306 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (3 : ZMod 2143)^126 ≠ 1
          reduce_mod_char
          decide

theorem prime_2153 : Nat.Prime 2153 := by
  apply lucas_primality 2153 (3 : ZMod 2153)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2153 - 1 = (2 : ℕ)^3 * ((269 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2153)^1076 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
      subst q
      change (3 : ZMod 2153)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_2161 : Nat.Prime 2161 := by
  apply lucas_primality 2161 (23 : ZMod 2161)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2161 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^3 * ((5 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (23 : ZMod 2161)^1080 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (23 : ZMod 2161)^720 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (23 : ZMod 2161)^432 ≠ 1
        reduce_mod_char
        decide

theorem prime_2179 : Nat.Prime 2179 := by
  apply lucas_primality 2179 (7 : ZMod 2179)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2179 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((11 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2179)^1089 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 2179)^726 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (7 : ZMod 2179)^198 ≠ 1
        reduce_mod_char
        decide

theorem prime_2203 : Nat.Prime 2203 := by
  apply lucas_primality 2203 (5 : ZMod 2203)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2203 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((367 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2203)^1101 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 2203)^734 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 367 := Nat.prime_eq_prime_of_dvd_pow hq prime_367 hd
        subst q
        change (5 : ZMod 2203)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_2207 : Nat.Prime 2207 := by
  apply lucas_primality 2207 (5 : ZMod 2207)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2207 - 1 = (2 : ℕ)^1 * ((1103 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2207)^1103 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1103 := Nat.prime_eq_prime_of_dvd_pow hq prime_1103 hd
      subst q
      change (5 : ZMod 2207)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_2213 : Nat.Prime 2213 := by
  apply lucas_primality 2213 (2 : ZMod 2213)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2213 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((79 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2213)^1106 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 2213)^316 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
        subst q
        change (2 : ZMod 2213)^28 ≠ 1
        reduce_mod_char
        decide

theorem prime_2221 : Nat.Prime 2221 := by
  apply lucas_primality 2221 (2 : ZMod 2221)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2221 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((37 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2221)^1110 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2221)^740 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 2221)^444 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (2 : ZMod 2221)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_2237 : Nat.Prime 2237 := by
  apply lucas_primality 2237 (2 : ZMod 2237)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2237 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((43 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2237)^1118 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 2237)^172 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
        subst q
        change (2 : ZMod 2237)^52 ≠ 1
        reduce_mod_char
        decide

theorem prime_2239 : Nat.Prime 2239 := by
  apply lucas_primality 2239 (3 : ZMod 2239)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2239 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((373 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2239)^1119 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 2239)^746 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 373 := Nat.prime_eq_prime_of_dvd_pow hq prime_373 hd
        subst q
        change (3 : ZMod 2239)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_2243 : Nat.Prime 2243 := by
  apply lucas_primality 2243 (2 : ZMod 2243)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2243 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((59 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2243)^1121 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 2243)^118 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
        subst q
        change (2 : ZMod 2243)^38 ≠ 1
        reduce_mod_char
        decide

theorem prime_2251 : Nat.Prime 2251 := by
  apply lucas_primality 2251 (7 : ZMod 2251)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2251 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^3)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2251)^1125 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 2251)^750 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 2251)^450 ≠ 1
        reduce_mod_char
        decide

theorem prime_2267 : Nat.Prime 2267 := by
  apply lucas_primality 2267 (2 : ZMod 2267)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2267 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((103 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2267)^1133 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 2267)^206 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
        subst q
        change (2 : ZMod 2267)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_2269 : Nat.Prime 2269 := by
  apply lucas_primality 2269 (2 : ZMod 2269)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2269 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^4 * ((7 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2269)^1134 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2269)^756 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 2269)^324 ≠ 1
        reduce_mod_char
        decide

theorem prime_2273 : Nat.Prime 2273 := by
  apply lucas_primality 2273 (3 : ZMod 2273)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2273 - 1 = (2 : ℕ)^5 * ((71 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2273)^1136 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
      subst q
      change (3 : ZMod 2273)^32 ≠ 1
      reduce_mod_char
      decide

theorem prime_2281 : Nat.Prime 2281 := by
  apply lucas_primality 2281 (7 : ZMod 2281)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2281 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((19 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2281)^1140 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 2281)^760 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 2281)^456 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (7 : ZMod 2281)^120 ≠ 1
          reduce_mod_char
          decide

theorem prime_2287 : Nat.Prime 2287 := by
  apply lucas_primality 2287 (19 : ZMod 2287)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2287 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((127 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 2287)^1143 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 2287)^762 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
        subst q
        change (19 : ZMod 2287)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_2293 : Nat.Prime 2293 := by
  apply lucas_primality 2293 (2 : ZMod 2293)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2293 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((191 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2293)^1146 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2293)^764 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
        subst q
        change (2 : ZMod 2293)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_2297 : Nat.Prime 2297 := by
  apply lucas_primality 2297 (5 : ZMod 2297)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2297 - 1 = (2 : ℕ)^3 * ((7 : ℕ)^1 * ((41 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2297)^1148 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 2297)^328 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
        subst q
        change (5 : ZMod 2297)^56 ≠ 1
        reduce_mod_char
        decide

theorem prime_2309 : Nat.Prime 2309 := by
  apply lucas_primality 2309 (2 : ZMod 2309)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2309 - 1 = (2 : ℕ)^2 * ((577 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2309)^1154 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 577 := Nat.prime_eq_prime_of_dvd_pow hq prime_577 hd
      subst q
      change (2 : ZMod 2309)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_2311 : Nat.Prime 2311 := by
  apply lucas_primality 2311 (3 : ZMod 2311)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2311 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2311)^1155 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 2311)^770 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 2311)^462 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (3 : ZMod 2311)^330 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (3 : ZMod 2311)^210 ≠ 1
            reduce_mod_char
            decide

theorem prime_2333 : Nat.Prime 2333 := by
  apply lucas_primality 2333 (2 : ZMod 2333)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2333 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((53 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2333)^1166 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 2333)^212 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
        subst q
        change (2 : ZMod 2333)^44 ≠ 1
        reduce_mod_char
        decide

theorem prime_2339 : Nat.Prime 2339 := by
  apply lucas_primality 2339 (2 : ZMod 2339)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2339 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((167 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2339)^1169 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 2339)^334 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
        subst q
        change (2 : ZMod 2339)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_2341 : Nat.Prime 2341 := by
  apply lucas_primality 2341 (7 : ZMod 2341)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2341 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((13 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2341)^1170 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 2341)^780 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 2341)^468 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (7 : ZMod 2341)^180 ≠ 1
          reduce_mod_char
          decide

theorem prime_2351 : Nat.Prime 2351 := by
  apply lucas_primality 2351 (13 : ZMod 2351)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2351 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((47 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 2351)^1175 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (13 : ZMod 2351)^470 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (13 : ZMod 2351)^50 ≠ 1
        reduce_mod_char
        decide

theorem prime_2357 : Nat.Prime 2357 := by
  apply lucas_primality 2357 (2 : ZMod 2357)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2357 - 1 = (2 : ℕ)^2 * ((19 : ℕ)^1 * ((31 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2357)^1178 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 2357)^124 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (2 : ZMod 2357)^76 ≠ 1
        reduce_mod_char
        decide

theorem prime_2371 : Nat.Prime 2371 := by
  apply lucas_primality 2371 (2 : ZMod 2371)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2371 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((79 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2371)^1185 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2371)^790 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 2371)^474 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (2 : ZMod 2371)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_2377 : Nat.Prime 2377 := by
  apply lucas_primality 2377 (5 : ZMod 2377)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2377 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((11 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2377)^1188 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 2377)^792 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 2377)^216 ≠ 1
        reduce_mod_char
        decide

theorem prime_2381 : Nat.Prime 2381 := by
  apply lucas_primality 2381 (3 : ZMod 2381)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2381 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((17 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2381)^1190 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 2381)^476 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 2381)^340 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (3 : ZMod 2381)^140 ≠ 1
          reduce_mod_char
          decide

theorem prime_2389 : Nat.Prime 2389 := by
  apply lucas_primality 2389 (2 : ZMod 2389)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2389 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((199 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2389)^1194 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2389)^796 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 199 := Nat.prime_eq_prime_of_dvd_pow hq prime_199 hd
        subst q
        change (2 : ZMod 2389)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_2393 : Nat.Prime 2393 := by
  apply lucas_primality 2393 (3 : ZMod 2393)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2393 - 1 = (2 : ℕ)^3 * ((13 : ℕ)^1 * ((23 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2393)^1196 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 2393)^184 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (3 : ZMod 2393)^104 ≠ 1
        reduce_mod_char
        decide

theorem prime_2399 : Nat.Prime 2399 := by
  apply lucas_primality 2399 (11 : ZMod 2399)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2399 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((109 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 2399)^1199 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (11 : ZMod 2399)^218 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
        subst q
        change (11 : ZMod 2399)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_2411 : Nat.Prime 2411 := by
  apply lucas_primality 2411 (6 : ZMod 2411)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2411 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((241 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 2411)^1205 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 2411)^482 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 241 := Nat.prime_eq_prime_of_dvd_pow hq prime_241 hd
        subst q
        change (6 : ZMod 2411)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_2417 : Nat.Prime 2417 := by
  apply lucas_primality 2417 (3 : ZMod 2417)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2417 - 1 = (2 : ℕ)^4 * ((151 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2417)^1208 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
      subst q
      change (3 : ZMod 2417)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_2423 : Nat.Prime 2423 := by
  apply lucas_primality 2423 (5 : ZMod 2423)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2423 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((173 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2423)^1211 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 2423)^346 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
        subst q
        change (5 : ZMod 2423)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_2437 : Nat.Prime 2437 := by
  apply lucas_primality 2437 (2 : ZMod 2437)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2437 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((29 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2437)^1218 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2437)^812 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 2437)^348 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (2 : ZMod 2437)^84 ≠ 1
          reduce_mod_char
          decide

theorem prime_2441 : Nat.Prime 2441 := by
  apply lucas_primality 2441 (6 : ZMod 2441)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2441 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((61 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 2441)^1220 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 2441)^488 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
        subst q
        change (6 : ZMod 2441)^40 ≠ 1
        reduce_mod_char
        decide

theorem prime_2459 : Nat.Prime 2459 := by
  apply lucas_primality 2459 (2 : ZMod 2459)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2459 - 1 = (2 : ℕ)^1 * ((1229 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2459)^1229 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1229 := Nat.prime_eq_prime_of_dvd_pow hq prime_1229 hd
      subst q
      change (2 : ZMod 2459)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_2467 : Nat.Prime 2467 := by
  apply lucas_primality 2467 (2 : ZMod 2467)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2467 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((137 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2467)^1233 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2467)^822 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
        subst q
        change (2 : ZMod 2467)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_2473 : Nat.Prime 2473 := by
  apply lucas_primality 2473 (5 : ZMod 2473)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2473 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((103 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2473)^1236 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 2473)^824 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
        subst q
        change (5 : ZMod 2473)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_2503 : Nat.Prime 2503 := by
  apply lucas_primality 2503 (3 : ZMod 2503)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2503 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((139 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2503)^1251 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 2503)^834 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
        subst q
        change (3 : ZMod 2503)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_2531 : Nat.Prime 2531 := by
  apply lucas_primality 2531 (2 : ZMod 2531)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2531 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((23 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2531)^1265 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 2531)^506 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 2531)^230 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 2531)^110 ≠ 1
          reduce_mod_char
          decide

theorem prime_2539 : Nat.Prime 2539 := by
  apply lucas_primality 2539 (2 : ZMod 2539)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2539 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((47 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2539)^1269 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2539)^846 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (2 : ZMod 2539)^54 ≠ 1
        reduce_mod_char
        decide

theorem prime_2543 : Nat.Prime 2543 := by
  apply lucas_primality 2543 (5 : ZMod 2543)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2543 - 1 = (2 : ℕ)^1 * ((31 : ℕ)^1 * ((41 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2543)^1271 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (5 : ZMod 2543)^82 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
        subst q
        change (5 : ZMod 2543)^62 ≠ 1
        reduce_mod_char
        decide

theorem prime_2549 : Nat.Prime 2549 := by
  apply lucas_primality 2549 (2 : ZMod 2549)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2549 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^2 * ((13 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2549)^1274 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 2549)^364 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 2549)^196 ≠ 1
        reduce_mod_char
        decide

theorem prime_2551 : Nat.Prime 2551 := by
  apply lucas_primality 2551 (6 : ZMod 2551)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2551 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((17 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 2551)^1275 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 2551)^850 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 2551)^510 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (6 : ZMod 2551)^150 ≠ 1
          reduce_mod_char
          decide

theorem prime_2557 : Nat.Prime 2557 := by
  apply lucas_primality 2557 (2 : ZMod 2557)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2557 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((71 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2557)^1278 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2557)^852 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
        subst q
        change (2 : ZMod 2557)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_2579 : Nat.Prime 2579 := by
  apply lucas_primality 2579 (2 : ZMod 2579)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2579 - 1 = (2 : ℕ)^1 * ((1289 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2579)^1289 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1289 := Nat.prime_eq_prime_of_dvd_pow hq prime_1289 hd
      subst q
      change (2 : ZMod 2579)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_2591 : Nat.Prime 2591 := by
  apply lucas_primality 2591 (7 : ZMod 2591)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2591 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((37 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2591)^1295 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 2591)^518 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 2591)^370 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (7 : ZMod 2591)^70 ≠ 1
          reduce_mod_char
          decide

theorem prime_2593 : Nat.Prime 2593 := by
  apply lucas_primality 2593 (7 : ZMod 2593)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2593 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^4) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2593)^1296 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
      subst q
      change (7 : ZMod 2593)^864 ≠ 1
      reduce_mod_char
      decide

theorem prime_2609 : Nat.Prime 2609 := by
  apply lucas_primality 2609 (3 : ZMod 2609)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2609 - 1 = (2 : ℕ)^4 * ((163 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2609)^1304 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
      subst q
      change (3 : ZMod 2609)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_2617 : Nat.Prime 2617 := by
  apply lucas_primality 2617 (5 : ZMod 2617)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2617 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((109 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2617)^1308 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 2617)^872 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
        subst q
        change (5 : ZMod 2617)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_2633 : Nat.Prime 2633 := by
  apply lucas_primality 2633 (3 : ZMod 2633)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2633 - 1 = (2 : ℕ)^3 * ((7 : ℕ)^1 * ((47 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2633)^1316 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 2633)^376 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (3 : ZMod 2633)^56 ≠ 1
        reduce_mod_char
        decide

theorem prime_2657 : Nat.Prime 2657 := by
  apply lucas_primality 2657 (3 : ZMod 2657)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2657 - 1 = (2 : ℕ)^5 * ((83 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2657)^1328 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
      subst q
      change (3 : ZMod 2657)^32 ≠ 1
      reduce_mod_char
      decide

theorem prime_2659 : Nat.Prime 2659 := by
  apply lucas_primality 2659 (2 : ZMod 2659)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2659 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((443 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2659)^1329 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2659)^886 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 443 := Nat.prime_eq_prime_of_dvd_pow hq prime_443 hd
        subst q
        change (2 : ZMod 2659)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_2663 : Nat.Prime 2663 := by
  apply lucas_primality 2663 (5 : ZMod 2663)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2663 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^3) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2663)^1331 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
      subst q
      change (5 : ZMod 2663)^242 ≠ 1
      reduce_mod_char
      decide

theorem prime_2671 : Nat.Prime 2671 := by
  apply lucas_primality 2671 (7 : ZMod 2671)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2671 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((89 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2671)^1335 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 2671)^890 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 2671)^534 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (7 : ZMod 2671)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_2677 : Nat.Prime 2677 := by
  apply lucas_primality 2677 (2 : ZMod 2677)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2677 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((223 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2677)^1338 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2677)^892 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 223 := Nat.prime_eq_prime_of_dvd_pow hq prime_223 hd
        subst q
        change (2 : ZMod 2677)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_2683 : Nat.Prime 2683 := by
  apply lucas_primality 2683 (2 : ZMod 2683)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2683 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((149 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2683)^1341 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2683)^894 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
        subst q
        change (2 : ZMod 2683)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_2689 : Nat.Prime 2689 := by
  apply lucas_primality 2689 (19 : ZMod 2689)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2689 - 1 = (2 : ℕ)^7 * ((3 : ℕ)^1 * ((7 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 2689)^1344 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 2689)^896 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (19 : ZMod 2689)^384 ≠ 1
        reduce_mod_char
        decide

theorem prime_2699 : Nat.Prime 2699 := by
  apply lucas_primality 2699 (2 : ZMod 2699)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2699 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((71 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2699)^1349 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 2699)^142 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
        subst q
        change (2 : ZMod 2699)^38 ≠ 1
        reduce_mod_char
        decide

theorem prime_2707 : Nat.Prime 2707 := by
  apply lucas_primality 2707 (2 : ZMod 2707)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2707 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((41 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2707)^1353 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2707)^902 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 2707)^246 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (2 : ZMod 2707)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_2711 : Nat.Prime 2711 := by
  apply lucas_primality 2711 (7 : ZMod 2711)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2711 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((271 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2711)^1355 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 2711)^542 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 271 := Nat.prime_eq_prime_of_dvd_pow hq prime_271 hd
        subst q
        change (7 : ZMod 2711)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_2719 : Nat.Prime 2719 := by
  apply lucas_primality 2719 (3 : ZMod 2719)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2719 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((151 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2719)^1359 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 2719)^906 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
        subst q
        change (3 : ZMod 2719)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_2729 : Nat.Prime 2729 := by
  apply lucas_primality 2729 (3 : ZMod 2729)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2729 - 1 = (2 : ℕ)^3 * ((11 : ℕ)^1 * ((31 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2729)^1364 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 2729)^248 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (3 : ZMod 2729)^88 ≠ 1
        reduce_mod_char
        decide

theorem prime_2741 : Nat.Prime 2741 := by
  apply lucas_primality 2741 (2 : ZMod 2741)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2741 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((137 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2741)^1370 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 2741)^548 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
        subst q
        change (2 : ZMod 2741)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_2753 : Nat.Prime 2753 := by
  apply lucas_primality 2753 (3 : ZMod 2753)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2753 - 1 = (2 : ℕ)^6 * ((43 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2753)^1376 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
      subst q
      change (3 : ZMod 2753)^64 ≠ 1
      reduce_mod_char
      decide

theorem prime_2767 : Nat.Prime 2767 := by
  apply lucas_primality 2767 (3 : ZMod 2767)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2767 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((461 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2767)^1383 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 2767)^922 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 461 := Nat.prime_eq_prime_of_dvd_pow hq prime_461 hd
        subst q
        change (3 : ZMod 2767)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_2777 : Nat.Prime 2777 := by
  apply lucas_primality 2777 (3 : ZMod 2777)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2777 - 1 = (2 : ℕ)^3 * ((347 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2777)^1388 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 347 := Nat.prime_eq_prime_of_dvd_pow hq prime_347 hd
      subst q
      change (3 : ZMod 2777)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_2789 : Nat.Prime 2789 := by
  apply lucas_primality 2789 (2 : ZMod 2789)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2789 - 1 = (2 : ℕ)^2 * ((17 : ℕ)^1 * ((41 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2789)^1394 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 2789)^164 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
        subst q
        change (2 : ZMod 2789)^68 ≠ 1
        reduce_mod_char
        decide

theorem prime_2791 : Nat.Prime 2791 := by
  apply lucas_primality 2791 (6 : ZMod 2791)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2791 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((31 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 2791)^1395 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 2791)^930 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 2791)^558 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (6 : ZMod 2791)^90 ≠ 1
          reduce_mod_char
          decide

theorem prime_2797 : Nat.Prime 2797 := by
  apply lucas_primality 2797 (2 : ZMod 2797)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2797 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((233 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2797)^1398 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2797)^932 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
        subst q
        change (2 : ZMod 2797)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_2801 : Nat.Prime 2801 := by
  apply lucas_primality 2801 (3 : ZMod 2801)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2801 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^2 * ((7 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2801)^1400 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 2801)^560 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 2801)^400 ≠ 1
        reduce_mod_char
        decide

theorem prime_2803 : Nat.Prime 2803 := by
  apply lucas_primality 2803 (2 : ZMod 2803)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2803 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((467 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2803)^1401 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2803)^934 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 467 := Nat.prime_eq_prime_of_dvd_pow hq prime_467 hd
        subst q
        change (2 : ZMod 2803)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_2819 : Nat.Prime 2819 := by
  apply lucas_primality 2819 (2 : ZMod 2819)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2819 - 1 = (2 : ℕ)^1 * ((1409 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2819)^1409 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1409 := Nat.prime_eq_prime_of_dvd_pow hq prime_1409 hd
      subst q
      change (2 : ZMod 2819)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_2833 : Nat.Prime 2833 := by
  apply lucas_primality 2833 (5 : ZMod 2833)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2833 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((59 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2833)^1416 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 2833)^944 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
        subst q
        change (5 : ZMod 2833)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_2837 : Nat.Prime 2837 := by
  apply lucas_primality 2837 (2 : ZMod 2837)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2837 - 1 = (2 : ℕ)^2 * ((709 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2837)^1418 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 709 := Nat.prime_eq_prime_of_dvd_pow hq prime_709 hd
      subst q
      change (2 : ZMod 2837)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_2843 : Nat.Prime 2843 := by
  apply lucas_primality 2843 (2 : ZMod 2843)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2843 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^2 * ((29 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2843)^1421 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 2843)^406 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (2 : ZMod 2843)^98 ≠ 1
        reduce_mod_char
        decide

theorem prime_2851 : Nat.Prime 2851 := by
  apply lucas_primality 2851 (2 : ZMod 2851)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2851 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((19 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2851)^1425 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2851)^950 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 2851)^570 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 2851)^150 ≠ 1
          reduce_mod_char
          decide

theorem prime_2857 : Nat.Prime 2857 := by
  apply lucas_primality 2857 (11 : ZMod 2857)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2857 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((17 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 2857)^1428 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 2857)^952 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (11 : ZMod 2857)^408 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (11 : ZMod 2857)^168 ≠ 1
          reduce_mod_char
          decide

theorem prime_2861 : Nat.Prime 2861 := by
  apply lucas_primality 2861 (2 : ZMod 2861)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2861 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2861)^1430 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 2861)^572 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 2861)^260 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 2861)^220 ≠ 1
          reduce_mod_char
          decide

theorem prime_2897 : Nat.Prime 2897 := by
  apply lucas_primality 2897 (3 : ZMod 2897)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2897 - 1 = (2 : ℕ)^4 * ((181 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2897)^1448 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 181 := Nat.prime_eq_prime_of_dvd_pow hq prime_181 hd
      subst q
      change (3 : ZMod 2897)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_2903 : Nat.Prime 2903 := by
  apply lucas_primality 2903 (5 : ZMod 2903)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2903 - 1 = (2 : ℕ)^1 * ((1451 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2903)^1451 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1451 := Nat.prime_eq_prime_of_dvd_pow hq prime_1451 hd
      subst q
      change (5 : ZMod 2903)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_2909 : Nat.Prime 2909 := by
  apply lucas_primality 2909 (2 : ZMod 2909)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2909 - 1 = (2 : ℕ)^2 * ((727 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2909)^1454 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 727 := Nat.prime_eq_prime_of_dvd_pow hq prime_727 hd
      subst q
      change (2 : ZMod 2909)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_2917 : Nat.Prime 2917 := by
  apply lucas_primality 2917 (5 : ZMod 2917)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2917 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^6) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2917)^1458 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
      subst q
      change (5 : ZMod 2917)^972 ≠ 1
      reduce_mod_char
      decide

end LegendreK6.Pratt
