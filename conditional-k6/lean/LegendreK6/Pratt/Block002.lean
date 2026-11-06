import LegendreK6.Pratt.Block001

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LegendreK6.Pratt

theorem prime_2939 : Nat.Prime 2939 := by
  apply lucas_primality 2939 (2 : ZMod 2939)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2939 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((113 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2939)^1469 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 2939)^226 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
        subst q
        change (2 : ZMod 2939)^26 ≠ 1
        reduce_mod_char
        decide

theorem prime_2953 : Nat.Prime 2953 := by
  apply lucas_primality 2953 (13 : ZMod 2953)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2953 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((41 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 2953)^1476 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 2953)^984 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
        subst q
        change (13 : ZMod 2953)^72 ≠ 1
        reduce_mod_char
        decide

theorem prime_2963 : Nat.Prime 2963 := by
  apply lucas_primality 2963 (2 : ZMod 2963)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2963 - 1 = (2 : ℕ)^1 * ((1481 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2963)^1481 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1481 := Nat.prime_eq_prime_of_dvd_pow hq prime_1481 hd
      subst q
      change (2 : ZMod 2963)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_2969 : Nat.Prime 2969 := by
  apply lucas_primality 2969 (3 : ZMod 2969)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2969 - 1 = (2 : ℕ)^3 * ((7 : ℕ)^1 * ((53 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2969)^1484 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 2969)^424 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
        subst q
        change (3 : ZMod 2969)^56 ≠ 1
        reduce_mod_char
        decide

theorem prime_2971 : Nat.Prime 2971 := by
  apply lucas_primality 2971 (10 : ZMod 2971)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2971 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((11 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 2971)^1485 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 2971)^990 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 2971)^594 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (10 : ZMod 2971)^270 ≠ 1
          reduce_mod_char
          decide

theorem prime_3001 : Nat.Prime 3001 := by
  apply lucas_primality 3001 (14 : ZMod 3001)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3001 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^3)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 3001)^1500 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 3001)^1000 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (14 : ZMod 3001)^600 ≠ 1
        reduce_mod_char
        decide

theorem prime_3011 : Nat.Prime 3011 := by
  apply lucas_primality 3011 (2 : ZMod 3011)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3011 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((43 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3011)^1505 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 3011)^602 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 3011)^430 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (2 : ZMod 3011)^70 ≠ 1
          reduce_mod_char
          decide

theorem prime_3023 : Nat.Prime 3023 := by
  apply lucas_primality 3023 (5 : ZMod 3023)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3023 - 1 = (2 : ℕ)^1 * ((1511 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3023)^1511 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1511 := Nat.prime_eq_prime_of_dvd_pow hq prime_1511 hd
      subst q
      change (5 : ZMod 3023)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_3037 : Nat.Prime 3037 := by
  apply lucas_primality 3037 (2 : ZMod 3037)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3037 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((23 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3037)^1518 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3037)^1012 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 3037)^276 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 3037)^132 ≠ 1
          reduce_mod_char
          decide

theorem prime_3049 : Nat.Prime 3049 := by
  apply lucas_primality 3049 (11 : ZMod 3049)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3049 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((127 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 3049)^1524 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 3049)^1016 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
        subst q
        change (11 : ZMod 3049)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_3061 : Nat.Prime 3061 := by
  apply lucas_primality 3061 (6 : ZMod 3061)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3061 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((17 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 3061)^1530 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 3061)^1020 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 3061)^612 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (6 : ZMod 3061)^180 ≠ 1
          reduce_mod_char
          decide

theorem prime_3067 : Nat.Prime 3067 := by
  apply lucas_primality 3067 (2 : ZMod 3067)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3067 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((73 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3067)^1533 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3067)^1022 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 3067)^438 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
          subst q
          change (2 : ZMod 3067)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_3083 : Nat.Prime 3083 := by
  apply lucas_primality 3083 (2 : ZMod 3083)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3083 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((67 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3083)^1541 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (2 : ZMod 3083)^134 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
        subst q
        change (2 : ZMod 3083)^46 ≠ 1
        reduce_mod_char
        decide

theorem prime_3089 : Nat.Prime 3089 := by
  apply lucas_primality 3089 (3 : ZMod 3089)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3089 - 1 = (2 : ℕ)^4 * ((193 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3089)^1544 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
      subst q
      change (3 : ZMod 3089)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_3109 : Nat.Prime 3109 := by
  apply lucas_primality 3109 (6 : ZMod 3109)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3109 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((37 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 3109)^1554 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 3109)^1036 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 3109)^444 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (6 : ZMod 3109)^84 ≠ 1
          reduce_mod_char
          decide

theorem prime_3119 : Nat.Prime 3119 := by
  apply lucas_primality 3119 (7 : ZMod 3119)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3119 - 1 = (2 : ℕ)^1 * ((1559 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 3119)^1559 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1559 := Nat.prime_eq_prime_of_dvd_pow hq prime_1559 hd
      subst q
      change (7 : ZMod 3119)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_3121 : Nat.Prime 3121 := by
  apply lucas_primality 3121 (7 : ZMod 3121)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3121 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 3121)^1560 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 3121)^1040 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 3121)^624 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (7 : ZMod 3121)^240 ≠ 1
          reduce_mod_char
          decide

theorem prime_3137 : Nat.Prime 3137 := by
  apply lucas_primality 3137 (3 : ZMod 3137)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3137 - 1 = (2 : ℕ)^6 * ((7 : ℕ)^2) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3137)^1568 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
      subst q
      change (3 : ZMod 3137)^448 ≠ 1
      reduce_mod_char
      decide

theorem prime_3163 : Nat.Prime 3163 := by
  apply lucas_primality 3163 (3 : ZMod 3163)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3163 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((31 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3163)^1581 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3163)^1054 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (3 : ZMod 3163)^186 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (3 : ZMod 3163)^102 ≠ 1
          reduce_mod_char
          decide

theorem prime_3169 : Nat.Prime 3169 := by
  apply lucas_primality 3169 (7 : ZMod 3169)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3169 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^2 * ((11 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 3169)^1584 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 3169)^1056 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (7 : ZMod 3169)^288 ≠ 1
        reduce_mod_char
        decide

theorem prime_3181 : Nat.Prime 3181 := by
  apply lucas_primality 3181 (7 : ZMod 3181)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3181 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((53 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 3181)^1590 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 3181)^1060 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 3181)^636 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (7 : ZMod 3181)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_3187 : Nat.Prime 3187 := by
  apply lucas_primality 3187 (2 : ZMod 3187)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3187 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((59 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3187)^1593 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3187)^1062 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
        subst q
        change (2 : ZMod 3187)^54 ≠ 1
        reduce_mod_char
        decide

theorem prime_3203 : Nat.Prime 3203 := by
  apply lucas_primality 3203 (2 : ZMod 3203)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3203 - 1 = (2 : ℕ)^1 * ((1601 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3203)^1601 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1601 := Nat.prime_eq_prime_of_dvd_pow hq prime_1601 hd
      subst q
      change (2 : ZMod 3203)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_3217 : Nat.Prime 3217 := by
  apply lucas_primality 3217 (5 : ZMod 3217)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3217 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((67 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3217)^1608 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 3217)^1072 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
        subst q
        change (5 : ZMod 3217)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_3221 : Nat.Prime 3221 := by
  apply lucas_primality 3221 (10 : ZMod 3221)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3221 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((23 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 3221)^1610 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (10 : ZMod 3221)^644 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (10 : ZMod 3221)^460 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (10 : ZMod 3221)^140 ≠ 1
          reduce_mod_char
          decide

theorem prime_3251 : Nat.Prime 3251 := by
  apply lucas_primality 3251 (6 : ZMod 3251)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3251 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^3 * ((13 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 3251)^1625 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 3251)^650 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (6 : ZMod 3251)^250 ≠ 1
        reduce_mod_char
        decide

theorem prime_3253 : Nat.Prime 3253 := by
  apply lucas_primality 3253 (2 : ZMod 3253)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3253 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((271 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3253)^1626 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3253)^1084 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 271 := Nat.prime_eq_prime_of_dvd_pow hq prime_271 hd
        subst q
        change (2 : ZMod 3253)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_3259 : Nat.Prime 3259 := by
  apply lucas_primality 3259 (3 : ZMod 3259)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3259 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((181 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3259)^1629 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3259)^1086 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 181 := Nat.prime_eq_prime_of_dvd_pow hq prime_181 hd
        subst q
        change (3 : ZMod 3259)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_3301 : Nat.Prime 3301 := by
  apply lucas_primality 3301 (6 : ZMod 3301)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3301 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((11 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 3301)^1650 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 3301)^1100 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 3301)^660 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (6 : ZMod 3301)^300 ≠ 1
          reduce_mod_char
          decide

theorem prime_3307 : Nat.Prime 3307 := by
  apply lucas_primality 3307 (2 : ZMod 3307)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3307 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((29 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3307)^1653 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3307)^1102 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 3307)^174 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (2 : ZMod 3307)^114 ≠ 1
          reduce_mod_char
          decide

theorem prime_3313 : Nat.Prime 3313 := by
  apply lucas_primality 3313 (10 : ZMod 3313)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3313 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((23 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 3313)^1656 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 3313)^1104 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (10 : ZMod 3313)^144 ≠ 1
        reduce_mod_char
        decide

theorem prime_3319 : Nat.Prime 3319 := by
  apply lucas_primality 3319 (6 : ZMod 3319)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3319 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((79 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 3319)^1659 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 3319)^1106 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 3319)^474 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (6 : ZMod 3319)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_3329 : Nat.Prime 3329 := by
  apply lucas_primality 3329 (3 : ZMod 3329)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3329 - 1 = (2 : ℕ)^8 * ((13 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3329)^1664 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
      subst q
      change (3 : ZMod 3329)^256 ≠ 1
      reduce_mod_char
      decide

theorem prime_3331 : Nat.Prime 3331 := by
  apply lucas_primality 3331 (3 : ZMod 3331)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3331 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((37 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3331)^1665 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3331)^1110 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 3331)^666 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (3 : ZMod 3331)^90 ≠ 1
          reduce_mod_char
          decide

theorem prime_3343 : Nat.Prime 3343 := by
  apply lucas_primality 3343 (5 : ZMod 3343)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3343 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((557 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3343)^1671 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 3343)^1114 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 557 := Nat.prime_eq_prime_of_dvd_pow hq prime_557 hd
        subst q
        change (5 : ZMod 3343)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_3347 : Nat.Prime 3347 := by
  apply lucas_primality 3347 (2 : ZMod 3347)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3347 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((239 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3347)^1673 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 3347)^478 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 239 := Nat.prime_eq_prime_of_dvd_pow hq prime_239 hd
        subst q
        change (2 : ZMod 3347)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_3359 : Nat.Prime 3359 := by
  apply lucas_primality 3359 (11 : ZMod 3359)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3359 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((73 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 3359)^1679 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (11 : ZMod 3359)^146 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
        subst q
        change (11 : ZMod 3359)^46 ≠ 1
        reduce_mod_char
        decide

theorem prime_3361 : Nat.Prime 3361 := by
  apply lucas_primality 3361 (22 : ZMod 3361)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3361 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (22 : ZMod 3361)^1680 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (22 : ZMod 3361)^1120 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (22 : ZMod 3361)^672 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (22 : ZMod 3361)^480 ≠ 1
          reduce_mod_char
          decide

theorem prime_3371 : Nat.Prime 3371 := by
  apply lucas_primality 3371 (2 : ZMod 3371)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3371 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((337 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3371)^1685 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 3371)^674 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 337 := Nat.prime_eq_prime_of_dvd_pow hq prime_337 hd
        subst q
        change (2 : ZMod 3371)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_3373 : Nat.Prime 3373 := by
  apply lucas_primality 3373 (5 : ZMod 3373)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3373 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((281 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3373)^1686 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 3373)^1124 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 281 := Nat.prime_eq_prime_of_dvd_pow hq prime_281 hd
        subst q
        change (5 : ZMod 3373)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_3391 : Nat.Prime 3391 := by
  apply lucas_primality 3391 (3 : ZMod 3391)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3391 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((113 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3391)^1695 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3391)^1130 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 3391)^678 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
          subst q
          change (3 : ZMod 3391)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_3413 : Nat.Prime 3413 := by
  apply lucas_primality 3413 (2 : ZMod 3413)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3413 - 1 = (2 : ℕ)^2 * ((853 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3413)^1706 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 853 := Nat.prime_eq_prime_of_dvd_pow hq prime_853 hd
      subst q
      change (2 : ZMod 3413)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_3433 : Nat.Prime 3433 := by
  apply lucas_primality 3433 (5 : ZMod 3433)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3433 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3433)^1716 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 3433)^1144 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 3433)^312 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (5 : ZMod 3433)^264 ≠ 1
          reduce_mod_char
          decide

theorem prime_3449 : Nat.Prime 3449 := by
  apply lucas_primality 3449 (3 : ZMod 3449)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3449 - 1 = (2 : ℕ)^3 * ((431 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3449)^1724 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 431 := Nat.prime_eq_prime_of_dvd_pow hq prime_431 hd
      subst q
      change (3 : ZMod 3449)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_3457 : Nat.Prime 3457 := by
  apply lucas_primality 3457 (7 : ZMod 3457)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3457 - 1 = (2 : ℕ)^7 * ((3 : ℕ)^3) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 3457)^1728 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
      subst q
      change (7 : ZMod 3457)^1152 ≠ 1
      reduce_mod_char
      decide

theorem prime_3467 : Nat.Prime 3467 := by
  apply lucas_primality 3467 (2 : ZMod 3467)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3467 - 1 = (2 : ℕ)^1 * ((1733 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3467)^1733 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1733 := Nat.prime_eq_prime_of_dvd_pow hq prime_1733 hd
      subst q
      change (2 : ZMod 3467)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_3469 : Nat.Prime 3469 := by
  apply lucas_primality 3469 (2 : ZMod 3469)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3469 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((17 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3469)^1734 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3469)^1156 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 3469)^204 ≠ 1
        reduce_mod_char
        decide

theorem prime_3491 : Nat.Prime 3491 := by
  apply lucas_primality 3491 (2 : ZMod 3491)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3491 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((349 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3491)^1745 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 3491)^698 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 349 := Nat.prime_eq_prime_of_dvd_pow hq prime_349 hd
        subst q
        change (2 : ZMod 3491)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_3499 : Nat.Prime 3499 := by
  apply lucas_primality 3499 (2 : ZMod 3499)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3499 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((53 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3499)^1749 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3499)^1166 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 3499)^318 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (2 : ZMod 3499)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_3511 : Nat.Prime 3511 := by
  apply lucas_primality 3511 (7 : ZMod 3511)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3511 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((13 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 3511)^1755 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 3511)^1170 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 3511)^702 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (7 : ZMod 3511)^270 ≠ 1
          reduce_mod_char
          decide

theorem prime_3529 : Nat.Prime 3529 := by
  apply lucas_primality 3529 (17 : ZMod 3529)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3529 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((7 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 3529)^1764 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 3529)^1176 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (17 : ZMod 3529)^504 ≠ 1
        reduce_mod_char
        decide

theorem prime_3539 : Nat.Prime 3539 := by
  apply lucas_primality 3539 (2 : ZMod 3539)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3539 - 1 = (2 : ℕ)^1 * ((29 : ℕ)^1 * ((61 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3539)^1769 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (2 : ZMod 3539)^122 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
        subst q
        change (2 : ZMod 3539)^58 ≠ 1
        reduce_mod_char
        decide

theorem prime_3541 : Nat.Prime 3541 := by
  apply lucas_primality 3541 (7 : ZMod 3541)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3541 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((59 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 3541)^1770 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 3541)^1180 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 3541)^708 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (7 : ZMod 3541)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_3547 : Nat.Prime 3547 := by
  apply lucas_primality 3547 (2 : ZMod 3547)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3547 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((197 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3547)^1773 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3547)^1182 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
        subst q
        change (2 : ZMod 3547)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_3557 : Nat.Prime 3557 := by
  apply lucas_primality 3557 (2 : ZMod 3557)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3557 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((127 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3557)^1778 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 3557)^508 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
        subst q
        change (2 : ZMod 3557)^28 ≠ 1
        reduce_mod_char
        decide

theorem prime_3559 : Nat.Prime 3559 := by
  apply lucas_primality 3559 (3 : ZMod 3559)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3559 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((593 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3559)^1779 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3559)^1186 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 593 := Nat.prime_eq_prime_of_dvd_pow hq prime_593 hd
        subst q
        change (3 : ZMod 3559)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_3581 : Nat.Prime 3581 := by
  apply lucas_primality 3581 (2 : ZMod 3581)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3581 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((179 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3581)^1790 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 3581)^716 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 179 := Nat.prime_eq_prime_of_dvd_pow hq prime_179 hd
        subst q
        change (2 : ZMod 3581)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_3583 : Nat.Prime 3583 := by
  apply lucas_primality 3583 (3 : ZMod 3583)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3583 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((199 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3583)^1791 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3583)^1194 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 199 := Nat.prime_eq_prime_of_dvd_pow hq prime_199 hd
        subst q
        change (3 : ZMod 3583)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_3593 : Nat.Prime 3593 := by
  apply lucas_primality 3593 (3 : ZMod 3593)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3593 - 1 = (2 : ℕ)^3 * ((449 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3593)^1796 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 449 := Nat.prime_eq_prime_of_dvd_pow hq prime_449 hd
      subst q
      change (3 : ZMod 3593)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_3607 : Nat.Prime 3607 := by
  apply lucas_primality 3607 (5 : ZMod 3607)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3607 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((601 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3607)^1803 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 3607)^1202 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 601 := Nat.prime_eq_prime_of_dvd_pow hq prime_601 hd
        subst q
        change (5 : ZMod 3607)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_3613 : Nat.Prime 3613 := by
  apply lucas_primality 3613 (2 : ZMod 3613)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3613 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((43 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3613)^1806 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3613)^1204 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 3613)^516 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (2 : ZMod 3613)^84 ≠ 1
          reduce_mod_char
          decide

theorem prime_3623 : Nat.Prime 3623 := by
  apply lucas_primality 3623 (5 : ZMod 3623)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3623 - 1 = (2 : ℕ)^1 * ((1811 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3623)^1811 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1811 := Nat.prime_eq_prime_of_dvd_pow hq prime_1811 hd
      subst q
      change (5 : ZMod 3623)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_3631 : Nat.Prime 3631 := by
  apply lucas_primality 3631 (15 : ZMod 3631)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3631 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^2))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (15 : ZMod 3631)^1815 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (15 : ZMod 3631)^1210 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (15 : ZMod 3631)^726 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (15 : ZMod 3631)^330 ≠ 1
          reduce_mod_char
          decide

theorem prime_3637 : Nat.Prime 3637 := by
  apply lucas_primality 3637 (2 : ZMod 3637)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3637 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((101 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3637)^1818 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3637)^1212 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
        subst q
        change (2 : ZMod 3637)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_3643 : Nat.Prime 3643 := by
  apply lucas_primality 3643 (2 : ZMod 3643)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3643 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((607 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3643)^1821 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3643)^1214 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 607 := Nat.prime_eq_prime_of_dvd_pow hq prime_607 hd
        subst q
        change (2 : ZMod 3643)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_3659 : Nat.Prime 3659 := by
  apply lucas_primality 3659 (2 : ZMod 3659)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3659 - 1 = (2 : ℕ)^1 * ((31 : ℕ)^1 * ((59 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3659)^1829 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (2 : ZMod 3659)^118 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
        subst q
        change (2 : ZMod 3659)^62 ≠ 1
        reduce_mod_char
        decide

theorem prime_3671 : Nat.Prime 3671 := by
  apply lucas_primality 3671 (13 : ZMod 3671)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3671 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((367 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 3671)^1835 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (13 : ZMod 3671)^734 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 367 := Nat.prime_eq_prime_of_dvd_pow hq prime_367 hd
        subst q
        change (13 : ZMod 3671)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_3673 : Nat.Prime 3673 := by
  apply lucas_primality 3673 (5 : ZMod 3673)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3673 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((17 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3673)^1836 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 3673)^1224 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (5 : ZMod 3673)^216 ≠ 1
        reduce_mod_char
        decide

theorem prime_3677 : Nat.Prime 3677 := by
  apply lucas_primality 3677 (2 : ZMod 3677)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3677 - 1 = (2 : ℕ)^2 * ((919 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3677)^1838 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 919 := Nat.prime_eq_prime_of_dvd_pow hq prime_919 hd
      subst q
      change (2 : ZMod 3677)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_3691 : Nat.Prime 3691 := by
  apply lucas_primality 3691 (2 : ZMod 3691)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3691 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((41 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3691)^1845 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3691)^1230 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 3691)^738 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (2 : ZMod 3691)^90 ≠ 1
          reduce_mod_char
          decide

theorem prime_3697 : Nat.Prime 3697 := by
  apply lucas_primality 3697 (5 : ZMod 3697)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3697 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3697)^1848 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 3697)^1232 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 3697)^528 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 3697)^336 ≠ 1
          reduce_mod_char
          decide

theorem prime_3701 : Nat.Prime 3701 := by
  apply lucas_primality 3701 (2 : ZMod 3701)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3701 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((37 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3701)^1850 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 3701)^740 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (2 : ZMod 3701)^100 ≠ 1
        reduce_mod_char
        decide

theorem prime_3719 : Nat.Prime 3719 := by
  apply lucas_primality 3719 (7 : ZMod 3719)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3719 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 3719)^1859 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (7 : ZMod 3719)^338 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (7 : ZMod 3719)^286 ≠ 1
        reduce_mod_char
        decide

theorem prime_3727 : Nat.Prime 3727 := by
  apply lucas_primality 3727 (3 : ZMod 3727)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3727 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((23 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3727)^1863 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3727)^1242 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (3 : ZMod 3727)^162 ≠ 1
        reduce_mod_char
        decide

theorem prime_3733 : Nat.Prime 3733 := by
  apply lucas_primality 3733 (2 : ZMod 3733)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3733 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((311 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3733)^1866 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3733)^1244 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 311 := Nat.prime_eq_prime_of_dvd_pow hq prime_311 hd
        subst q
        change (2 : ZMod 3733)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_3739 : Nat.Prime 3739 := by
  apply lucas_primality 3739 (7 : ZMod 3739)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3739 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((89 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 3739)^1869 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 3739)^1246 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 3739)^534 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (7 : ZMod 3739)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_3761 : Nat.Prime 3761 := by
  apply lucas_primality 3761 (3 : ZMod 3761)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3761 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((47 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3761)^1880 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 3761)^752 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (3 : ZMod 3761)^80 ≠ 1
        reduce_mod_char
        decide

theorem prime_3767 : Nat.Prime 3767 := by
  apply lucas_primality 3767 (5 : ZMod 3767)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3767 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((269 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3767)^1883 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 3767)^538 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
        subst q
        change (5 : ZMod 3767)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_3769 : Nat.Prime 3769 := by
  apply lucas_primality 3769 (7 : ZMod 3769)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3769 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((157 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 3769)^1884 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 3769)^1256 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
        subst q
        change (7 : ZMod 3769)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_3793 : Nat.Prime 3793 := by
  apply lucas_primality 3793 (5 : ZMod 3793)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3793 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((79 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3793)^1896 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 3793)^1264 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
        subst q
        change (5 : ZMod 3793)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_3797 : Nat.Prime 3797 := by
  apply lucas_primality 3797 (2 : ZMod 3797)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3797 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((73 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3797)^1898 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 3797)^292 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
        subst q
        change (2 : ZMod 3797)^52 ≠ 1
        reduce_mod_char
        decide

theorem prime_3803 : Nat.Prime 3803 := by
  apply lucas_primality 3803 (2 : ZMod 3803)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3803 - 1 = (2 : ℕ)^1 * ((1901 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3803)^1901 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1901 := Nat.prime_eq_prime_of_dvd_pow hq prime_1901 hd
      subst q
      change (2 : ZMod 3803)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_3821 : Nat.Prime 3821 := by
  apply lucas_primality 3821 (3 : ZMod 3821)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3821 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((191 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3821)^1910 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 3821)^764 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
        subst q
        change (3 : ZMod 3821)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_3823 : Nat.Prime 3823 := by
  apply lucas_primality 3823 (3 : ZMod 3823)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3823 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((13 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3823)^1911 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3823)^1274 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 3823)^546 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 3823)^294 ≠ 1
          reduce_mod_char
          decide

theorem prime_3833 : Nat.Prime 3833 := by
  apply lucas_primality 3833 (3 : ZMod 3833)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3833 - 1 = (2 : ℕ)^3 * ((479 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3833)^1916 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 479 := Nat.prime_eq_prime_of_dvd_pow hq prime_479 hd
      subst q
      change (3 : ZMod 3833)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_3851 : Nat.Prime 3851 := by
  apply lucas_primality 3851 (2 : ZMod 3851)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3851 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((7 : ℕ)^1 * ((11 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3851)^1925 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 3851)^770 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 3851)^550 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 3851)^350 ≠ 1
          reduce_mod_char
          decide

theorem prime_3853 : Nat.Prime 3853 := by
  apply lucas_primality 3853 (2 : ZMod 3853)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3853 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((107 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3853)^1926 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3853)^1284 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
        subst q
        change (2 : ZMod 3853)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_3863 : Nat.Prime 3863 := by
  apply lucas_primality 3863 (5 : ZMod 3863)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3863 - 1 = (2 : ℕ)^1 * ((1931 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3863)^1931 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1931 := Nat.prime_eq_prime_of_dvd_pow hq prime_1931 hd
      subst q
      change (5 : ZMod 3863)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_3877 : Nat.Prime 3877 := by
  apply lucas_primality 3877 (2 : ZMod 3877)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3877 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((19 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3877)^1938 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3877)^1292 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 3877)^228 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 3877)^204 ≠ 1
          reduce_mod_char
          decide

theorem prime_3881 : Nat.Prime 3881 := by
  apply lucas_primality 3881 (13 : ZMod 3881)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3881 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((97 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 3881)^1940 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (13 : ZMod 3881)^776 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
        subst q
        change (13 : ZMod 3881)^40 ≠ 1
        reduce_mod_char
        decide

theorem prime_3889 : Nat.Prime 3889 := by
  apply lucas_primality 3889 (11 : ZMod 3889)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3889 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^5) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 3889)^1944 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
      subst q
      change (11 : ZMod 3889)^1296 ≠ 1
      reduce_mod_char
      decide

theorem prime_3907 : Nat.Prime 3907 := by
  apply lucas_primality 3907 (2 : ZMod 3907)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3907 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((31 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3907)^1953 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3907)^1302 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 3907)^558 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (2 : ZMod 3907)^126 ≠ 1
          reduce_mod_char
          decide

theorem prime_3917 : Nat.Prime 3917 := by
  apply lucas_primality 3917 (2 : ZMod 3917)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3917 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((89 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3917)^1958 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 3917)^356 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
        subst q
        change (2 : ZMod 3917)^44 ≠ 1
        reduce_mod_char
        decide

theorem prime_3919 : Nat.Prime 3919 := by
  apply lucas_primality 3919 (3 : ZMod 3919)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3919 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((653 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3919)^1959 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3919)^1306 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 653 := Nat.prime_eq_prime_of_dvd_pow hq prime_653 hd
        subst q
        change (3 : ZMod 3919)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_3929 : Nat.Prime 3929 := by
  apply lucas_primality 3929 (3 : ZMod 3929)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3929 - 1 = (2 : ℕ)^3 * ((491 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3929)^1964 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 491 := Nat.prime_eq_prime_of_dvd_pow hq prime_491 hd
      subst q
      change (3 : ZMod 3929)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_3943 : Nat.Prime 3943 := by
  apply lucas_primality 3943 (3 : ZMod 3943)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3943 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((73 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3943)^1971 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3943)^1314 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
        subst q
        change (3 : ZMod 3943)^54 ≠ 1
        reduce_mod_char
        decide

theorem prime_3947 : Nat.Prime 3947 := by
  apply lucas_primality 3947 (2 : ZMod 3947)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3947 - 1 = (2 : ℕ)^1 * ((1973 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3947)^1973 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1973 := Nat.prime_eq_prime_of_dvd_pow hq prime_1973 hd
      subst q
      change (2 : ZMod 3947)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_3967 : Nat.Prime 3967 := by
  apply lucas_primality 3967 (6 : ZMod 3967)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3967 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((661 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 3967)^1983 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 3967)^1322 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 661 := Nat.prime_eq_prime_of_dvd_pow hq prime_661 hd
        subst q
        change (6 : ZMod 3967)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_4003 : Nat.Prime 4003 := by
  apply lucas_primality 4003 (2 : ZMod 4003)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4003 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((29 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4003)^2001 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 4003)^1334 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 4003)^174 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (2 : ZMod 4003)^138 ≠ 1
          reduce_mod_char
          decide

theorem prime_4007 : Nat.Prime 4007 := by
  apply lucas_primality 4007 (5 : ZMod 4007)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4007 - 1 = (2 : ℕ)^1 * ((2003 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 4007)^2003 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 2003 := Nat.prime_eq_prime_of_dvd_pow hq prime_2003 hd
      subst q
      change (5 : ZMod 4007)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_4013 : Nat.Prime 4013 := by
  apply lucas_primality 4013 (2 : ZMod 4013)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4013 - 1 = (2 : ℕ)^2 * ((17 : ℕ)^1 * ((59 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4013)^2006 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 4013)^236 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
        subst q
        change (2 : ZMod 4013)^68 ≠ 1
        reduce_mod_char
        decide

theorem prime_4021 : Nat.Prime 4021 := by
  apply lucas_primality 4021 (2 : ZMod 4021)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4021 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((67 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4021)^2010 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 4021)^1340 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 4021)^804 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (2 : ZMod 4021)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_4049 : Nat.Prime 4049 := by
  apply lucas_primality 4049 (3 : ZMod 4049)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4049 - 1 = (2 : ℕ)^4 * ((11 : ℕ)^1 * ((23 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4049)^2024 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 4049)^368 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (3 : ZMod 4049)^176 ≠ 1
        reduce_mod_char
        decide

theorem prime_4057 : Nat.Prime 4057 := by
  apply lucas_primality 4057 (5 : ZMod 4057)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4057 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((13 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 4057)^2028 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 4057)^1352 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (5 : ZMod 4057)^312 ≠ 1
        reduce_mod_char
        decide

theorem prime_4073 : Nat.Prime 4073 := by
  apply lucas_primality 4073 (3 : ZMod 4073)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4073 - 1 = (2 : ℕ)^3 * ((509 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4073)^2036 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 509 := Nat.prime_eq_prime_of_dvd_pow hq prime_509 hd
      subst q
      change (3 : ZMod 4073)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_4091 : Nat.Prime 4091 := by
  apply lucas_primality 4091 (2 : ZMod 4091)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4091 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((409 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4091)^2045 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 4091)^818 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 409 := Nat.prime_eq_prime_of_dvd_pow hq prime_409 hd
        subst q
        change (2 : ZMod 4091)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_4093 : Nat.Prime 4093 := by
  apply lucas_primality 4093 (2 : ZMod 4093)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4093 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((31 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4093)^2046 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 4093)^1364 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 4093)^372 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (2 : ZMod 4093)^132 ≠ 1
          reduce_mod_char
          decide

theorem prime_4099 : Nat.Prime 4099 := by
  apply lucas_primality 4099 (2 : ZMod 4099)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4099 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((683 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4099)^2049 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 4099)^1366 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 683 := Nat.prime_eq_prime_of_dvd_pow hq prime_683 hd
        subst q
        change (2 : ZMod 4099)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_4111 : Nat.Prime 4111 := by
  apply lucas_primality 4111 (12 : ZMod 4111)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4111 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((137 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (12 : ZMod 4111)^2055 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (12 : ZMod 4111)^1370 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (12 : ZMod 4111)^822 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
          subst q
          change (12 : ZMod 4111)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_4129 : Nat.Prime 4129 := by
  apply lucas_primality 4129 (13 : ZMod 4129)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4129 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((43 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 4129)^2064 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 4129)^1376 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
        subst q
        change (13 : ZMod 4129)^96 ≠ 1
        reduce_mod_char
        decide

theorem prime_4133 : Nat.Prime 4133 := by
  apply lucas_primality 4133 (2 : ZMod 4133)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4133 - 1 = (2 : ℕ)^2 * ((1033 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4133)^2066 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1033 := Nat.prime_eq_prime_of_dvd_pow hq prime_1033 hd
      subst q
      change (2 : ZMod 4133)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_4139 : Nat.Prime 4139 := by
  apply lucas_primality 4139 (2 : ZMod 4139)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4139 - 1 = (2 : ℕ)^1 * ((2069 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4139)^2069 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 2069 := Nat.prime_eq_prime_of_dvd_pow hq prime_2069 hd
      subst q
      change (2 : ZMod 4139)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_4153 : Nat.Prime 4153 := by
  apply lucas_primality 4153 (5 : ZMod 4153)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4153 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((173 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 4153)^2076 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 4153)^1384 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
        subst q
        change (5 : ZMod 4153)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_4157 : Nat.Prime 4157 := by
  apply lucas_primality 4157 (2 : ZMod 4157)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4157 - 1 = (2 : ℕ)^2 * ((1039 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4157)^2078 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1039 := Nat.prime_eq_prime_of_dvd_pow hq prime_1039 hd
      subst q
      change (2 : ZMod 4157)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_4177 : Nat.Prime 4177 := by
  apply lucas_primality 4177 (5 : ZMod 4177)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4177 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((29 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 4177)^2088 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 4177)^1392 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (5 : ZMod 4177)^144 ≠ 1
        reduce_mod_char
        decide

theorem prime_4211 : Nat.Prime 4211 := by
  apply lucas_primality 4211 (6 : ZMod 4211)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4211 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((421 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 4211)^2105 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 4211)^842 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 421 := Nat.prime_eq_prime_of_dvd_pow hq prime_421 hd
        subst q
        change (6 : ZMod 4211)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_4217 : Nat.Prime 4217 := by
  apply lucas_primality 4217 (3 : ZMod 4217)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4217 - 1 = (2 : ℕ)^3 * ((17 : ℕ)^1 * ((31 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4217)^2108 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (3 : ZMod 4217)^248 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (3 : ZMod 4217)^136 ≠ 1
        reduce_mod_char
        decide

theorem prime_4219 : Nat.Prime 4219 := by
  apply lucas_primality 4219 (2 : ZMod 4219)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4219 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((37 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4219)^2109 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 4219)^1406 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 4219)^222 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (2 : ZMod 4219)^114 ≠ 1
          reduce_mod_char
          decide

theorem prime_4229 : Nat.Prime 4229 := by
  apply lucas_primality 4229 (2 : ZMod 4229)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4229 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((151 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4229)^2114 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 4229)^604 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
        subst q
        change (2 : ZMod 4229)^28 ≠ 1
        reduce_mod_char
        decide

theorem prime_4231 : Nat.Prime 4231 := by
  apply lucas_primality 4231 (3 : ZMod 4231)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4231 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((47 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4231)^2115 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 4231)^1410 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 4231)^846 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (3 : ZMod 4231)^90 ≠ 1
          reduce_mod_char
          decide

theorem prime_4241 : Nat.Prime 4241 := by
  apply lucas_primality 4241 (3 : ZMod 4241)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4241 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((53 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4241)^2120 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 4241)^848 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
        subst q
        change (3 : ZMod 4241)^80 ≠ 1
        reduce_mod_char
        decide

theorem prime_4253 : Nat.Prime 4253 := by
  apply lucas_primality 4253 (2 : ZMod 4253)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4253 - 1 = (2 : ℕ)^2 * ((1063 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4253)^2126 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1063 := Nat.prime_eq_prime_of_dvd_pow hq prime_1063 hd
      subst q
      change (2 : ZMod 4253)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_4259 : Nat.Prime 4259 := by
  apply lucas_primality 4259 (2 : ZMod 4259)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4259 - 1 = (2 : ℕ)^1 * ((2129 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4259)^2129 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 2129 := Nat.prime_eq_prime_of_dvd_pow hq prime_2129 hd
      subst q
      change (2 : ZMod 4259)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_4273 : Nat.Prime 4273 := by
  apply lucas_primality 4273 (5 : ZMod 4273)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4273 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((89 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 4273)^2136 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 4273)^1424 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
        subst q
        change (5 : ZMod 4273)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_4283 : Nat.Prime 4283 := by
  apply lucas_primality 4283 (2 : ZMod 4283)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4283 - 1 = (2 : ℕ)^1 * ((2141 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4283)^2141 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 2141 := Nat.prime_eq_prime_of_dvd_pow hq prime_2141 hd
      subst q
      change (2 : ZMod 4283)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_4289 : Nat.Prime 4289 := by
  apply lucas_primality 4289 (3 : ZMod 4289)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4289 - 1 = (2 : ℕ)^6 * ((67 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4289)^2144 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
      subst q
      change (3 : ZMod 4289)^64 ≠ 1
      reduce_mod_char
      decide

theorem prime_4297 : Nat.Prime 4297 := by
  apply lucas_primality 4297 (5 : ZMod 4297)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4297 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((179 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 4297)^2148 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 4297)^1432 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 179 := Nat.prime_eq_prime_of_dvd_pow hq prime_179 hd
        subst q
        change (5 : ZMod 4297)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_4337 : Nat.Prime 4337 := by
  apply lucas_primality 4337 (3 : ZMod 4337)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4337 - 1 = (2 : ℕ)^4 * ((271 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4337)^2168 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 271 := Nat.prime_eq_prime_of_dvd_pow hq prime_271 hd
      subst q
      change (3 : ZMod 4337)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_4339 : Nat.Prime 4339 := by
  apply lucas_primality 4339 (10 : ZMod 4339)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4339 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((241 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 4339)^2169 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 4339)^1446 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 241 := Nat.prime_eq_prime_of_dvd_pow hq prime_241 hd
        subst q
        change (10 : ZMod 4339)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_4349 : Nat.Prime 4349 := by
  apply lucas_primality 4349 (2 : ZMod 4349)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4349 - 1 = (2 : ℕ)^2 * ((1087 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4349)^2174 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1087 := Nat.prime_eq_prime_of_dvd_pow hq prime_1087 hd
      subst q
      change (2 : ZMod 4349)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_4363 : Nat.Prime 4363 := by
  apply lucas_primality 4363 (2 : ZMod 4363)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4363 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((727 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4363)^2181 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 4363)^1454 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 727 := Nat.prime_eq_prime_of_dvd_pow hq prime_727 hd
        subst q
        change (2 : ZMod 4363)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_4397 : Nat.Prime 4397 := by
  apply lucas_primality 4397 (2 : ZMod 4397)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4397 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((157 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4397)^2198 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 4397)^628 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
        subst q
        change (2 : ZMod 4397)^28 ≠ 1
        reduce_mod_char
        decide

theorem prime_4423 : Nat.Prime 4423 := by
  apply lucas_primality 4423 (3 : ZMod 4423)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4423 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((67 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4423)^2211 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 4423)^1474 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 4423)^402 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (3 : ZMod 4423)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_4441 : Nat.Prime 4441 := by
  apply lucas_primality 4441 (21 : ZMod 4441)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4441 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((37 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (21 : ZMod 4441)^2220 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (21 : ZMod 4441)^1480 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (21 : ZMod 4441)^888 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (21 : ZMod 4441)^120 ≠ 1
          reduce_mod_char
          decide

theorem prime_4447 : Nat.Prime 4447 := by
  apply lucas_primality 4447 (3 : ZMod 4447)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4447 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((13 : ℕ)^1 * ((19 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4447)^2223 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 4447)^1482 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 4447)^342 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (3 : ZMod 4447)^234 ≠ 1
          reduce_mod_char
          decide

theorem prime_4451 : Nat.Prime 4451 := by
  apply lucas_primality 4451 (2 : ZMod 4451)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4451 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((89 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4451)^2225 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 4451)^890 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
        subst q
        change (2 : ZMod 4451)^50 ≠ 1
        reduce_mod_char
        decide

theorem prime_4481 : Nat.Prime 4481 := by
  apply lucas_primality 4481 (3 : ZMod 4481)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4481 - 1 = (2 : ℕ)^7 * ((5 : ℕ)^1 * ((7 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4481)^2240 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 4481)^896 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 4481)^640 ≠ 1
        reduce_mod_char
        decide

theorem prime_4483 : Nat.Prime 4483 := by
  apply lucas_primality 4483 (2 : ZMod 4483)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4483 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((83 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4483)^2241 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 4483)^1494 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
        subst q
        change (2 : ZMod 4483)^54 ≠ 1
        reduce_mod_char
        decide

theorem prime_4507 : Nat.Prime 4507 := by
  apply lucas_primality 4507 (2 : ZMod 4507)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4507 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((751 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4507)^2253 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 4507)^1502 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 751 := Nat.prime_eq_prime_of_dvd_pow hq prime_751 hd
        subst q
        change (2 : ZMod 4507)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_4517 : Nat.Prime 4517 := by
  apply lucas_primality 4517 (2 : ZMod 4517)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4517 - 1 = (2 : ℕ)^2 * ((1129 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4517)^2258 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1129 := Nat.prime_eq_prime_of_dvd_pow hq prime_1129 hd
      subst q
      change (2 : ZMod 4517)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_4519 : Nat.Prime 4519 := by
  apply lucas_primality 4519 (3 : ZMod 4519)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4519 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((251 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4519)^2259 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 4519)^1506 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 251 := Nat.prime_eq_prime_of_dvd_pow hq prime_251 hd
        subst q
        change (3 : ZMod 4519)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_4547 : Nat.Prime 4547 := by
  apply lucas_primality 4547 (2 : ZMod 4547)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4547 - 1 = (2 : ℕ)^1 * ((2273 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4547)^2273 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 2273 := Nat.prime_eq_prime_of_dvd_pow hq prime_2273 hd
      subst q
      change (2 : ZMod 4547)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_4549 : Nat.Prime 4549 := by
  apply lucas_primality 4549 (6 : ZMod 4549)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4549 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((379 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 4549)^2274 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 4549)^1516 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 379 := Nat.prime_eq_prime_of_dvd_pow hq prime_379 hd
        subst q
        change (6 : ZMod 4549)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_4567 : Nat.Prime 4567 := by
  apply lucas_primality 4567 (3 : ZMod 4567)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4567 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((761 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4567)^2283 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 4567)^1522 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 761 := Nat.prime_eq_prime_of_dvd_pow hq prime_761 hd
        subst q
        change (3 : ZMod 4567)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_4591 : Nat.Prime 4591 := by
  apply lucas_primality 4591 (11 : ZMod 4591)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4591 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((17 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 4591)^2295 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 4591)^1530 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 4591)^918 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (11 : ZMod 4591)^270 ≠ 1
          reduce_mod_char
          decide

theorem prime_4597 : Nat.Prime 4597 := by
  apply lucas_primality 4597 (5 : ZMod 4597)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4597 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((383 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 4597)^2298 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 4597)^1532 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 383 := Nat.prime_eq_prime_of_dvd_pow hq prime_383 hd
        subst q
        change (5 : ZMod 4597)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_4643 : Nat.Prime 4643 := by
  apply lucas_primality 4643 (5 : ZMod 4643)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4643 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((211 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 4643)^2321 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 4643)^422 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 211 := Nat.prime_eq_prime_of_dvd_pow hq prime_211 hd
        subst q
        change (5 : ZMod 4643)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_4651 : Nat.Prime 4651 := by
  apply lucas_primality 4651 (3 : ZMod 4651)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4651 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((31 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4651)^2325 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 4651)^1550 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 4651)^930 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (3 : ZMod 4651)^150 ≠ 1
          reduce_mod_char
          decide

theorem prime_4657 : Nat.Prime 4657 := by
  apply lucas_primality 4657 (15 : ZMod 4657)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4657 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((97 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (15 : ZMod 4657)^2328 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (15 : ZMod 4657)^1552 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
        subst q
        change (15 : ZMod 4657)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_4663 : Nat.Prime 4663 := by
  apply lucas_primality 4663 (3 : ZMod 4663)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4663 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((37 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4663)^2331 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 4663)^1554 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 4663)^666 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (3 : ZMod 4663)^126 ≠ 1
          reduce_mod_char
          decide

theorem prime_4673 : Nat.Prime 4673 := by
  apply lucas_primality 4673 (3 : ZMod 4673)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4673 - 1 = (2 : ℕ)^6 * ((73 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4673)^2336 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
      subst q
      change (3 : ZMod 4673)^64 ≠ 1
      reduce_mod_char
      decide

theorem prime_4679 : Nat.Prime 4679 := by
  apply lucas_primality 4679 (11 : ZMod 4679)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4679 - 1 = (2 : ℕ)^1 * ((2339 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 4679)^2339 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 2339 := Nat.prime_eq_prime_of_dvd_pow hq prime_2339 hd
      subst q
      change (11 : ZMod 4679)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_4703 : Nat.Prime 4703 := by
  apply lucas_primality 4703 (5 : ZMod 4703)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4703 - 1 = (2 : ℕ)^1 * ((2351 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 4703)^2351 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 2351 := Nat.prime_eq_prime_of_dvd_pow hq prime_2351 hd
      subst q
      change (5 : ZMod 4703)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_4721 : Nat.Prime 4721 := by
  apply lucas_primality 4721 (6 : ZMod 4721)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4721 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((59 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 4721)^2360 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 4721)^944 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
        subst q
        change (6 : ZMod 4721)^80 ≠ 1
        reduce_mod_char
        decide

theorem prime_4733 : Nat.Prime 4733 := by
  apply lucas_primality 4733 (5 : ZMod 4733)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4733 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((13 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 4733)^2366 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 4733)^676 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (5 : ZMod 4733)^364 ≠ 1
        reduce_mod_char
        decide

theorem prime_4759 : Nat.Prime 4759 := by
  apply lucas_primality 4759 (3 : ZMod 4759)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4759 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((61 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4759)^2379 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 4759)^1586 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 4759)^366 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (3 : ZMod 4759)^78 ≠ 1
          reduce_mod_char
          decide

theorem prime_4787 : Nat.Prime 4787 := by
  apply lucas_primality 4787 (2 : ZMod 4787)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4787 - 1 = (2 : ℕ)^1 * ((2393 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4787)^2393 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 2393 := Nat.prime_eq_prime_of_dvd_pow hq prime_2393 hd
      subst q
      change (2 : ZMod 4787)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_4793 : Nat.Prime 4793 := by
  apply lucas_primality 4793 (3 : ZMod 4793)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4793 - 1 = (2 : ℕ)^3 * ((599 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4793)^2396 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 599 := Nat.prime_eq_prime_of_dvd_pow hq prime_599 hd
      subst q
      change (3 : ZMod 4793)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_4799 : Nat.Prime 4799 := by
  apply lucas_primality 4799 (7 : ZMod 4799)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4799 - 1 = (2 : ℕ)^1 * ((2399 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 4799)^2399 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 2399 := Nat.prime_eq_prime_of_dvd_pow hq prime_2399 hd
      subst q
      change (7 : ZMod 4799)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_4817 : Nat.Prime 4817 := by
  apply lucas_primality 4817 (3 : ZMod 4817)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4817 - 1 = (2 : ℕ)^4 * ((7 : ℕ)^1 * ((43 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4817)^2408 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 4817)^688 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
        subst q
        change (3 : ZMod 4817)^112 ≠ 1
        reduce_mod_char
        decide

theorem prime_4831 : Nat.Prime 4831 := by
  apply lucas_primality 4831 (3 : ZMod 4831)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4831 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((23 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4831)^2415 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 4831)^1610 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 4831)^966 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (3 : ZMod 4831)^690 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (3 : ZMod 4831)^210 ≠ 1
            reduce_mod_char
            decide

theorem prime_4871 : Nat.Prime 4871 := by
  apply lucas_primality 4871 (11 : ZMod 4871)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4871 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((487 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 4871)^2435 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 4871)^974 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 487 := Nat.prime_eq_prime_of_dvd_pow hq prime_487 hd
        subst q
        change (11 : ZMod 4871)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_4877 : Nat.Prime 4877 := by
  apply lucas_primality 4877 (2 : ZMod 4877)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4877 - 1 = (2 : ℕ)^2 * ((23 : ℕ)^1 * ((53 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4877)^2438 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (2 : ZMod 4877)^212 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
        subst q
        change (2 : ZMod 4877)^92 ≠ 1
        reduce_mod_char
        decide

theorem prime_4889 : Nat.Prime 4889 := by
  apply lucas_primality 4889 (3 : ZMod 4889)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4889 - 1 = (2 : ℕ)^3 * ((13 : ℕ)^1 * ((47 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4889)^2444 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 4889)^376 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (3 : ZMod 4889)^104 ≠ 1
        reduce_mod_char
        decide

theorem prime_4919 : Nat.Prime 4919 := by
  apply lucas_primality 4919 (13 : ZMod 4919)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4919 - 1 = (2 : ℕ)^1 * ((2459 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 4919)^2459 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 2459 := Nat.prime_eq_prime_of_dvd_pow hq prime_2459 hd
      subst q
      change (13 : ZMod 4919)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_4931 : Nat.Prime 4931 := by
  apply lucas_primality 4931 (6 : ZMod 4931)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4931 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((29 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 4931)^2465 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 4931)^986 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (6 : ZMod 4931)^290 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (6 : ZMod 4931)^170 ≠ 1
          reduce_mod_char
          decide

theorem prime_4943 : Nat.Prime 4943 := by
  apply lucas_primality 4943 (7 : ZMod 4943)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4943 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((353 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 4943)^2471 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 4943)^706 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 353 := Nat.prime_eq_prime_of_dvd_pow hq prime_353 hd
        subst q
        change (7 : ZMod 4943)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_4951 : Nat.Prime 4951 := by
  apply lucas_primality 4951 (6 : ZMod 4951)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4951 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^2 * ((11 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 4951)^2475 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 4951)^1650 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 4951)^990 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (6 : ZMod 4951)^450 ≠ 1
          reduce_mod_char
          decide

theorem prime_4957 : Nat.Prime 4957 := by
  apply lucas_primality 4957 (2 : ZMod 4957)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4957 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((59 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4957)^2478 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 4957)^1652 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 4957)^708 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (2 : ZMod 4957)^84 ≠ 1
          reduce_mod_char
          decide

theorem prime_4967 : Nat.Prime 4967 := by
  apply lucas_primality 4967 (5 : ZMod 4967)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4967 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((191 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 4967)^2483 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (5 : ZMod 4967)^382 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
        subst q
        change (5 : ZMod 4967)^26 ≠ 1
        reduce_mod_char
        decide

theorem prime_4969 : Nat.Prime 4969 := by
  apply lucas_primality 4969 (11 : ZMod 4969)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4969 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((23 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 4969)^2484 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 4969)^1656 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (11 : ZMod 4969)^216 ≠ 1
        reduce_mod_char
        decide

theorem prime_4973 : Nat.Prime 4973 := by
  apply lucas_primality 4973 (2 : ZMod 4973)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4973 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((113 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4973)^2486 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 4973)^452 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
        subst q
        change (2 : ZMod 4973)^44 ≠ 1
        reduce_mod_char
        decide

theorem prime_4987 : Nat.Prime 4987 := by
  apply lucas_primality 4987 (2 : ZMod 4987)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4987 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((277 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4987)^2493 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 4987)^1662 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 277 := Nat.prime_eq_prime_of_dvd_pow hq prime_277 hd
        subst q
        change (2 : ZMod 4987)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_4993 : Nat.Prime 4993 := by
  apply lucas_primality 4993 (5 : ZMod 4993)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4993 - 1 = (2 : ℕ)^7 * ((3 : ℕ)^1 * ((13 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 4993)^2496 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 4993)^1664 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (5 : ZMod 4993)^384 ≠ 1
        reduce_mod_char
        decide

theorem prime_5023 : Nat.Prime 5023 := by
  apply lucas_primality 5023 (3 : ZMod 5023)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5023 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((31 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 5023)^2511 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 5023)^1674 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (3 : ZMod 5023)^162 ≠ 1
        reduce_mod_char
        decide

theorem prime_5039 : Nat.Prime 5039 := by
  apply lucas_primality 5039 (11 : ZMod 5039)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5039 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((229 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 5039)^2519 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (11 : ZMod 5039)^458 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 229 := Nat.prime_eq_prime_of_dvd_pow hq prime_229 hd
        subst q
        change (11 : ZMod 5039)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_5059 : Nat.Prime 5059 := by
  apply lucas_primality 5059 (2 : ZMod 5059)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5059 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((281 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5059)^2529 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 5059)^1686 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 281 := Nat.prime_eq_prime_of_dvd_pow hq prime_281 hd
        subst q
        change (2 : ZMod 5059)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_5077 : Nat.Prime 5077 := by
  apply lucas_primality 5077 (2 : ZMod 5077)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5077 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((47 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5077)^2538 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 5077)^1692 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (2 : ZMod 5077)^108 ≠ 1
        reduce_mod_char
        decide

theorem prime_5081 : Nat.Prime 5081 := by
  apply lucas_primality 5081 (3 : ZMod 5081)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5081 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((127 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 5081)^2540 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 5081)^1016 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
        subst q
        change (3 : ZMod 5081)^40 ≠ 1
        reduce_mod_char
        decide

theorem prime_5087 : Nat.Prime 5087 := by
  apply lucas_primality 5087 (5 : ZMod 5087)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5087 - 1 = (2 : ℕ)^1 * ((2543 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 5087)^2543 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 2543 := Nat.prime_eq_prime_of_dvd_pow hq prime_2543 hd
      subst q
      change (5 : ZMod 5087)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_5099 : Nat.Prime 5099 := by
  apply lucas_primality 5099 (2 : ZMod 5099)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5099 - 1 = (2 : ℕ)^1 * ((2549 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5099)^2549 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 2549 := Nat.prime_eq_prime_of_dvd_pow hq prime_2549 hd
      subst q
      change (2 : ZMod 5099)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_5101 : Nat.Prime 5101 := by
  apply lucas_primality 5101 (6 : ZMod 5101)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5101 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((17 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 5101)^2550 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 5101)^1700 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 5101)^1020 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (6 : ZMod 5101)^300 ≠ 1
          reduce_mod_char
          decide

theorem prime_5113 : Nat.Prime 5113 := by
  apply lucas_primality 5113 (19 : ZMod 5113)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5113 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((71 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 5113)^2556 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 5113)^1704 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
        subst q
        change (19 : ZMod 5113)^72 ≠ 1
        reduce_mod_char
        decide

theorem prime_5119 : Nat.Prime 5119 := by
  apply lucas_primality 5119 (3 : ZMod 5119)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5119 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((853 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 5119)^2559 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 5119)^1706 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 853 := Nat.prime_eq_prime_of_dvd_pow hq prime_853 hd
        subst q
        change (3 : ZMod 5119)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_5153 : Nat.Prime 5153 := by
  apply lucas_primality 5153 (5 : ZMod 5153)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5153 - 1 = (2 : ℕ)^5 * ((7 : ℕ)^1 * ((23 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 5153)^2576 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 5153)^736 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (5 : ZMod 5153)^224 ≠ 1
        reduce_mod_char
        decide

theorem prime_5167 : Nat.Prime 5167 := by
  apply lucas_primality 5167 (6 : ZMod 5167)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5167 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((41 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 5167)^2583 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 5167)^1722 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 5167)^738 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (6 : ZMod 5167)^126 ≠ 1
          reduce_mod_char
          decide

theorem prime_5171 : Nat.Prime 5171 := by
  apply lucas_primality 5171 (2 : ZMod 5171)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5171 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((47 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5171)^2585 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 5171)^1034 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 5171)^470 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (2 : ZMod 5171)^110 ≠ 1
          reduce_mod_char
          decide

theorem prime_5179 : Nat.Prime 5179 := by
  apply lucas_primality 5179 (2 : ZMod 5179)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5179 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((863 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5179)^2589 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 5179)^1726 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 863 := Nat.prime_eq_prime_of_dvd_pow hq prime_863 hd
        subst q
        change (2 : ZMod 5179)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_5189 : Nat.Prime 5189 := by
  apply lucas_primality 5189 (2 : ZMod 5189)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5189 - 1 = (2 : ℕ)^2 * ((1297 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5189)^2594 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1297 := Nat.prime_eq_prime_of_dvd_pow hq prime_1297 hd
      subst q
      change (2 : ZMod 5189)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_5237 : Nat.Prime 5237 := by
  apply lucas_primality 5237 (3 : ZMod 5237)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5237 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((17 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 5237)^2618 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 5237)^748 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 5237)^476 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (3 : ZMod 5237)^308 ≠ 1
          reduce_mod_char
          decide

theorem prime_5273 : Nat.Prime 5273 := by
  apply lucas_primality 5273 (3 : ZMod 5273)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5273 - 1 = (2 : ℕ)^3 * ((659 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 5273)^2636 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 659 := Nat.prime_eq_prime_of_dvd_pow hq prime_659 hd
      subst q
      change (3 : ZMod 5273)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_5281 : Nat.Prime 5281 := by
  apply lucas_primality 5281 (7 : ZMod 5281)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5281 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 5281)^2640 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 5281)^1760 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 5281)^1056 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (7 : ZMod 5281)^480 ≠ 1
          reduce_mod_char
          decide

theorem prime_5297 : Nat.Prime 5297 := by
  apply lucas_primality 5297 (3 : ZMod 5297)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5297 - 1 = (2 : ℕ)^4 * ((331 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 5297)^2648 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 331 := Nat.prime_eq_prime_of_dvd_pow hq prime_331 hd
      subst q
      change (3 : ZMod 5297)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_5303 : Nat.Prime 5303 := by
  apply lucas_primality 5303 (5 : ZMod 5303)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5303 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((241 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 5303)^2651 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 5303)^482 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 241 := Nat.prime_eq_prime_of_dvd_pow hq prime_241 hd
        subst q
        change (5 : ZMod 5303)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_5309 : Nat.Prime 5309 := by
  apply lucas_primality 5309 (2 : ZMod 5309)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5309 - 1 = (2 : ℕ)^2 * ((1327 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5309)^2654 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1327 := Nat.prime_eq_prime_of_dvd_pow hq prime_1327 hd
      subst q
      change (2 : ZMod 5309)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_5323 : Nat.Prime 5323 := by
  apply lucas_primality 5323 (5 : ZMod 5323)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5323 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((887 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 5323)^2661 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 5323)^1774 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 887 := Nat.prime_eq_prime_of_dvd_pow hq prime_887 hd
        subst q
        change (5 : ZMod 5323)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_5351 : Nat.Prime 5351 := by
  apply lucas_primality 5351 (11 : ZMod 5351)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5351 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((107 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 5351)^2675 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 5351)^1070 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
        subst q
        change (11 : ZMod 5351)^50 ≠ 1
        reduce_mod_char
        decide

theorem prime_5381 : Nat.Prime 5381 := by
  apply lucas_primality 5381 (3 : ZMod 5381)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5381 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((269 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 5381)^2690 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 5381)^1076 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
        subst q
        change (3 : ZMod 5381)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_5393 : Nat.Prime 5393 := by
  apply lucas_primality 5393 (3 : ZMod 5393)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5393 - 1 = (2 : ℕ)^4 * ((337 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 5393)^2696 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 337 := Nat.prime_eq_prime_of_dvd_pow hq prime_337 hd
      subst q
      change (3 : ZMod 5393)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_5399 : Nat.Prime 5399 := by
  apply lucas_primality 5399 (7 : ZMod 5399)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5399 - 1 = (2 : ℕ)^1 * ((2699 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 5399)^2699 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 2699 := Nat.prime_eq_prime_of_dvd_pow hq prime_2699 hd
      subst q
      change (7 : ZMod 5399)^2 ≠ 1
      reduce_mod_char
      decide

end LegendreK6.Pratt
