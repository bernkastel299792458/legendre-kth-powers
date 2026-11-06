import LegendreK6.Pratt.Block005

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LegendreK6.Pratt

theorem prime_25703 : Nat.Prime 25703 := by
  apply lucas_primality 25703 (5 : ZMod 25703)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 25703 - 1 = (2 : ℕ)^1 * ((71 : ℕ)^1 * ((181 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 25703)^12851 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
        subst q
        change (5 : ZMod 25703)^362 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 181 := Nat.prime_eq_prime_of_dvd_pow hq prime_181 hd
        subst q
        change (5 : ZMod 25703)^142 ≠ 1
        reduce_mod_char
        decide

theorem prime_25717 : Nat.Prime 25717 := by
  apply lucas_primality 25717 (2 : ZMod 25717)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 25717 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((2143 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 25717)^12858 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 25717)^8572 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2143 := Nat.prime_eq_prime_of_dvd_pow hq prime_2143 hd
        subst q
        change (2 : ZMod 25717)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_25819 : Nat.Prime 25819 := by
  apply lucas_primality 25819 (3 : ZMod 25819)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 25819 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((331 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 25819)^12909 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 25819)^8606 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 25819)^1986 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 331 := Nat.prime_eq_prime_of_dvd_pow hq prime_331 hd
          subst q
          change (3 : ZMod 25819)^78 ≠ 1
          reduce_mod_char
          decide

theorem prime_25999 : Nat.Prime 25999 := by
  apply lucas_primality 25999 (7 : ZMod 25999)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 25999 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((619 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 25999)^12999 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 25999)^8666 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 25999)^3714 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 619 := Nat.prime_eq_prime_of_dvd_pow hq prime_619 hd
          subst q
          change (7 : ZMod 25999)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_26053 : Nat.Prime 26053 := by
  apply lucas_primality 26053 (2 : ZMod 26053)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26053 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((167 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 26053)^13026 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 26053)^8684 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 26053)^2004 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
          subst q
          change (2 : ZMod 26053)^156 ≠ 1
          reduce_mod_char
          decide

theorem prime_26111 : Nat.Prime 26111 := by
  apply lucas_primality 26111 (7 : ZMod 26111)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26111 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((373 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 26111)^13055 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 26111)^5222 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 26111)^3730 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 373 := Nat.prime_eq_prime_of_dvd_pow hq prime_373 hd
          subst q
          change (7 : ZMod 26111)^70 ≠ 1
          reduce_mod_char
          decide

theorem prime_26309 : Nat.Prime 26309 := by
  apply lucas_primality 26309 (2 : ZMod 26309)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26309 - 1 = (2 : ℕ)^2 * ((6577 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 26309)^13154 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 6577 := Nat.prime_eq_prime_of_dvd_pow hq prime_6577 hd
      subst q
      change (2 : ZMod 26309)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_26557 : Nat.Prime 26557 := by
  apply lucas_primality 26557 (2 : ZMod 26557)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26557 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((2213 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 26557)^13278 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 26557)^8852 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2213 := Nat.prime_eq_prime_of_dvd_pow hq prime_2213 hd
        subst q
        change (2 : ZMod 26557)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_26561 : Nat.Prime 26561 := by
  apply lucas_primality 26561 (3 : ZMod 26561)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26561 - 1 = (2 : ℕ)^6 * ((5 : ℕ)^1 * ((83 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 26561)^13280 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 26561)^5312 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
        subst q
        change (3 : ZMod 26561)^320 ≠ 1
        reduce_mod_char
        decide

theorem prime_26633 : Nat.Prime 26633 := by
  apply lucas_primality 26633 (3 : ZMod 26633)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26633 - 1 = (2 : ℕ)^3 * ((3329 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 26633)^13316 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3329 := Nat.prime_eq_prime_of_dvd_pow hq prime_3329 hd
      subst q
      change (3 : ZMod 26633)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_26681 : Nat.Prime 26681 := by
  apply lucas_primality 26681 (6 : ZMod 26681)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26681 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((23 : ℕ)^1 * ((29 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 26681)^13340 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 26681)^5336 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (6 : ZMod 26681)^1160 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (6 : ZMod 26681)^920 ≠ 1
          reduce_mod_char
          decide

theorem prime_26683 : Nat.Prime 26683 := by
  apply lucas_primality 26683 (2 : ZMod 26683)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26683 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((4447 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 26683)^13341 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 26683)^8894 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4447 := Nat.prime_eq_prime_of_dvd_pow hq prime_4447 hd
        subst q
        change (2 : ZMod 26683)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_26701 : Nat.Prime 26701 := by
  apply lucas_primality 26701 (22 : ZMod 26701)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26701 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((89 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (22 : ZMod 26701)^13350 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (22 : ZMod 26701)^8900 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (22 : ZMod 26701)^5340 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (22 : ZMod 26701)^300 ≠ 1
          reduce_mod_char
          decide

theorem prime_26731 : Nat.Prime 26731 := by
  apply lucas_primality 26731 (3 : ZMod 26731)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26731 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^5 * ((5 : ℕ)^1 * ((11 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 26731)^13365 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 26731)^8910 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 26731)^5346 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 26731)^2430 ≠ 1
          reduce_mod_char
          decide

theorem prime_26777 : Nat.Prime 26777 := by
  apply lucas_primality 26777 (3 : ZMod 26777)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26777 - 1 = (2 : ℕ)^3 * ((3347 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 26777)^13388 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3347 := Nat.prime_eq_prime_of_dvd_pow hq prime_3347 hd
      subst q
      change (3 : ZMod 26777)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_27017 : Nat.Prime 27017 := by
  apply lucas_primality 27017 (5 : ZMod 27017)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 27017 - 1 = (2 : ℕ)^3 * ((11 : ℕ)^1 * ((307 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 27017)^13508 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 27017)^2456 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 307 := Nat.prime_eq_prime_of_dvd_pow hq prime_307 hd
        subst q
        change (5 : ZMod 27017)^88 ≠ 1
        reduce_mod_char
        decide

theorem prime_27059 : Nat.Prime 27059 := by
  apply lucas_primality 27059 (2 : ZMod 27059)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 27059 - 1 = (2 : ℕ)^1 * ((83 : ℕ)^1 * ((163 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 27059)^13529 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
        subst q
        change (2 : ZMod 27059)^326 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
        subst q
        change (2 : ZMod 27059)^166 ≠ 1
        reduce_mod_char
        decide

theorem prime_27107 : Nat.Prime 27107 := by
  apply lucas_primality 27107 (2 : ZMod 27107)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 27107 - 1 = (2 : ℕ)^1 * ((13553 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 27107)^13553 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 13553 := Nat.prime_eq_prime_of_dvd_pow hq prime_13553 hd
      subst q
      change (2 : ZMod 27107)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_27179 : Nat.Prime 27179 := by
  apply lucas_primality 27179 (2 : ZMod 27179)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 27179 - 1 = (2 : ℕ)^1 * ((107 : ℕ)^1 * ((127 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 27179)^13589 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
        subst q
        change (2 : ZMod 27179)^254 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
        subst q
        change (2 : ZMod 27179)^214 ≠ 1
        reduce_mod_char
        decide

theorem prime_27241 : Nat.Prime 27241 := by
  apply lucas_primality 27241 (17 : ZMod 27241)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 27241 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((227 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 27241)^13620 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 27241)^9080 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (17 : ZMod 27241)^5448 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 227 := Nat.prime_eq_prime_of_dvd_pow hq prime_227 hd
          subst q
          change (17 : ZMod 27241)^120 ≠ 1
          reduce_mod_char
          decide

theorem prime_27259 : Nat.Prime 27259 := by
  apply lucas_primality 27259 (2 : ZMod 27259)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 27259 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((59 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 27259)^13629 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 27259)^9086 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 27259)^3894 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (2 : ZMod 27259)^2478 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
            subst q
            change (2 : ZMod 27259)^462 ≠ 1
            reduce_mod_char
            decide

theorem prime_27437 : Nat.Prime 27437 := by
  apply lucas_primality 27437 (2 : ZMod 27437)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 27437 - 1 = (2 : ℕ)^2 * ((19 : ℕ)^3) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 27437)^13718 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
      subst q
      change (2 : ZMod 27437)^1444 ≠ 1
      reduce_mod_char
      decide

theorem prime_27541 : Nat.Prime 27541 := by
  apply lucas_primality 27541 (19 : ZMod 27541)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 27541 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^4 * ((5 : ℕ)^1 * ((17 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 27541)^13770 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 27541)^9180 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (19 : ZMod 27541)^5508 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (19 : ZMod 27541)^1620 ≠ 1
          reduce_mod_char
          decide

theorem prime_27673 : Nat.Prime 27673 := by
  apply lucas_primality 27673 (11 : ZMod 27673)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 27673 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((1153 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 27673)^13836 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 27673)^9224 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1153 := Nat.prime_eq_prime_of_dvd_pow hq prime_1153 hd
        subst q
        change (11 : ZMod 27673)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_27739 : Nat.Prime 27739 := by
  apply lucas_primality 27739 (3 : ZMod 27739)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 27739 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((23 : ℕ)^1 * ((67 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 27739)^13869 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 27739)^9246 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (3 : ZMod 27739)^1206 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (3 : ZMod 27739)^414 ≠ 1
          reduce_mod_char
          decide

theorem prime_27893 : Nat.Prime 27893 := by
  apply lucas_primality 27893 (2 : ZMod 27893)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 27893 - 1 = (2 : ℕ)^2 * ((19 : ℕ)^1 * ((367 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 27893)^13946 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 27893)^1468 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 367 := Nat.prime_eq_prime_of_dvd_pow hq prime_367 hd
        subst q
        change (2 : ZMod 27893)^76 ≠ 1
        reduce_mod_char
        decide

theorem prime_27983 : Nat.Prime 27983 := by
  apply lucas_primality 27983 (5 : ZMod 27983)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 27983 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((823 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 27983)^13991 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (5 : ZMod 27983)^1646 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 823 := Nat.prime_eq_prime_of_dvd_pow hq prime_823 hd
        subst q
        change (5 : ZMod 27983)^34 ≠ 1
        reduce_mod_char
        decide

theorem prime_28057 : Nat.Prime 28057 := by
  apply lucas_primality 28057 (5 : ZMod 28057)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 28057 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((167 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 28057)^14028 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 28057)^9352 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 28057)^4008 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
          subst q
          change (5 : ZMod 28057)^168 ≠ 1
          reduce_mod_char
          decide

theorem prime_28087 : Nat.Prime 28087 := by
  apply lucas_primality 28087 (3 : ZMod 28087)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 28087 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((31 : ℕ)^1 * ((151 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 28087)^14043 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 28087)^9362 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (3 : ZMod 28087)^906 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
          subst q
          change (3 : ZMod 28087)^186 ≠ 1
          reduce_mod_char
          decide

theorem prime_28219 : Nat.Prime 28219 := by
  apply lucas_primality 28219 (3 : ZMod 28219)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 28219 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((4703 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 28219)^14109 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 28219)^9406 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4703 := Nat.prime_eq_prime_of_dvd_pow hq prime_4703 hd
        subst q
        change (3 : ZMod 28219)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_28229 : Nat.Prime 28229 := by
  apply lucas_primality 28229 (2 : ZMod 28229)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 28229 - 1 = (2 : ℕ)^2 * ((7057 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 28229)^14114 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 7057 := Nat.prime_eq_prime_of_dvd_pow hq prime_7057 hd
      subst q
      change (2 : ZMod 28229)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_28349 : Nat.Prime 28349 := by
  apply lucas_primality 28349 (2 : ZMod 28349)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 28349 - 1 = (2 : ℕ)^2 * ((19 : ℕ)^1 * ((373 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 28349)^14174 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 28349)^1492 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 373 := Nat.prime_eq_prime_of_dvd_pow hq prime_373 hd
        subst q
        change (2 : ZMod 28349)^76 ≠ 1
        reduce_mod_char
        decide

theorem prime_28351 : Nat.Prime 28351 := by
  apply lucas_primality 28351 (6 : ZMod 28351)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 28351 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((5 : ℕ)^2 * ((7 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 28351)^14175 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 28351)^9450 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 28351)^5670 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 28351)^4050 ≠ 1
          reduce_mod_char
          decide

theorem prime_28433 : Nat.Prime 28433 := by
  apply lucas_primality 28433 (3 : ZMod 28433)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 28433 - 1 = (2 : ℕ)^4 * ((1777 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 28433)^14216 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1777 := Nat.prime_eq_prime_of_dvd_pow hq prime_1777 hd
      subst q
      change (3 : ZMod 28433)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_28477 : Nat.Prime 28477 := by
  apply lucas_primality 28477 (2 : ZMod 28477)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 28477 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((113 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 28477)^14238 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 28477)^9492 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 28477)^4068 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
          subst q
          change (2 : ZMod 28477)^252 ≠ 1
          reduce_mod_char
          decide

theorem prime_28499 : Nat.Prime 28499 := by
  apply lucas_primality 28499 (2 : ZMod 28499)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 28499 - 1 = (2 : ℕ)^1 * ((14249 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 28499)^14249 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 14249 := Nat.prime_eq_prime_of_dvd_pow hq prime_14249 hd
      subst q
      change (2 : ZMod 28499)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_28573 : Nat.Prime 28573 := by
  apply lucas_primality 28573 (2 : ZMod 28573)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 28573 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((2381 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 28573)^14286 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 28573)^9524 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2381 := Nat.prime_eq_prime_of_dvd_pow hq prime_2381 hd
        subst q
        change (2 : ZMod 28573)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_28579 : Nat.Prime 28579 := by
  apply lucas_primality 28579 (2 : ZMod 28579)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 28579 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((433 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 28579)^14289 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 28579)^9526 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 28579)^2598 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 433 := Nat.prime_eq_prime_of_dvd_pow hq prime_433 hd
          subst q
          change (2 : ZMod 28579)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_28591 : Nat.Prime 28591 := by
  apply lucas_primality 28591 (3 : ZMod 28591)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 28591 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((953 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 28591)^14295 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 28591)^9530 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 28591)^5718 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 953 := Nat.prime_eq_prime_of_dvd_pow hq prime_953 hd
          subst q
          change (3 : ZMod 28591)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_28643 : Nat.Prime 28643 := by
  apply lucas_primality 28643 (2 : ZMod 28643)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 28643 - 1 = (2 : ℕ)^1 * ((14321 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 28643)^14321 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 14321 := Nat.prime_eq_prime_of_dvd_pow hq prime_14321 hd
      subst q
      change (2 : ZMod 28643)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_28793 : Nat.Prime 28793 := by
  apply lucas_primality 28793 (3 : ZMod 28793)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 28793 - 1 = (2 : ℕ)^3 * ((59 : ℕ)^1 * ((61 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 28793)^14396 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
        subst q
        change (3 : ZMod 28793)^488 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
        subst q
        change (3 : ZMod 28793)^472 ≠ 1
        reduce_mod_char
        decide

theorem prime_28817 : Nat.Prime 28817 := by
  apply lucas_primality 28817 (3 : ZMod 28817)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 28817 - 1 = (2 : ℕ)^4 * ((1801 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 28817)^14408 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1801 := Nat.prime_eq_prime_of_dvd_pow hq prime_1801 hd
      subst q
      change (3 : ZMod 28817)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_28867 : Nat.Prime 28867 := by
  apply lucas_primality 28867 (3 : ZMod 28867)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 28867 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((283 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 28867)^14433 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 28867)^9622 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (3 : ZMod 28867)^1698 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 283 := Nat.prime_eq_prime_of_dvd_pow hq prime_283 hd
          subst q
          change (3 : ZMod 28867)^102 ≠ 1
          reduce_mod_char
          decide

theorem prime_29077 : Nat.Prime 29077 := by
  apply lucas_primality 29077 (2 : ZMod 29077)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 29077 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((2423 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 29077)^14538 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 29077)^9692 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2423 := Nat.prime_eq_prime_of_dvd_pow hq prime_2423 hd
        subst q
        change (2 : ZMod 29077)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_29221 : Nat.Prime 29221 := by
  apply lucas_primality 29221 (2 : ZMod 29221)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 29221 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((487 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 29221)^14610 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 29221)^9740 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 29221)^5844 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 487 := Nat.prime_eq_prime_of_dvd_pow hq prime_487 hd
          subst q
          change (2 : ZMod 29221)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_29287 : Nat.Prime 29287 := by
  apply lucas_primality 29287 (5 : ZMod 29287)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 29287 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((1627 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 29287)^14643 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 29287)^9762 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1627 := Nat.prime_eq_prime_of_dvd_pow hq prime_1627 hd
        subst q
        change (5 : ZMod 29287)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_29297 : Nat.Prime 29297 := by
  apply lucas_primality 29297 (3 : ZMod 29297)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 29297 - 1 = (2 : ℕ)^4 * ((1831 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 29297)^14648 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1831 := Nat.prime_eq_prime_of_dvd_pow hq prime_1831 hd
      subst q
      change (3 : ZMod 29297)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_29387 : Nat.Prime 29387 := by
  apply lucas_primality 29387 (2 : ZMod 29387)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 29387 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((2099 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 29387)^14693 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 29387)^4198 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2099 := Nat.prime_eq_prime_of_dvd_pow hq prime_2099 hd
        subst q
        change (2 : ZMod 29387)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_29873 : Nat.Prime 29873 := by
  apply lucas_primality 29873 (3 : ZMod 29873)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 29873 - 1 = (2 : ℕ)^4 * ((1867 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 29873)^14936 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1867 := Nat.prime_eq_prime_of_dvd_pow hq prime_1867 hd
      subst q
      change (3 : ZMod 29873)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_29989 : Nat.Prime 29989 := by
  apply lucas_primality 29989 (2 : ZMod 29989)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 29989 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((7 : ℕ)^2 * ((17 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 29989)^14994 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 29989)^9996 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 29989)^4284 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 29989)^1764 ≠ 1
          reduce_mod_char
          decide

theorem prime_30137 : Nat.Prime 30137 := by
  apply lucas_primality 30137 (3 : ZMod 30137)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 30137 - 1 = (2 : ℕ)^3 * ((3767 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 30137)^15068 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3767 := Nat.prime_eq_prime_of_dvd_pow hq prime_3767 hd
      subst q
      change (3 : ZMod 30137)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_30203 : Nat.Prime 30203 := by
  apply lucas_primality 30203 (2 : ZMod 30203)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 30203 - 1 = (2 : ℕ)^1 * ((15101 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 30203)^15101 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 15101 := Nat.prime_eq_prime_of_dvd_pow hq prime_15101 hd
      subst q
      change (2 : ZMod 30203)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_30313 : Nat.Prime 30313 := by
  apply lucas_primality 30313 (5 : ZMod 30313)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 30313 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((421 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 30313)^15156 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 30313)^10104 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 421 := Nat.prime_eq_prime_of_dvd_pow hq prime_421 hd
        subst q
        change (5 : ZMod 30313)^72 ≠ 1
        reduce_mod_char
        decide

theorem prime_30323 : Nat.Prime 30323 := by
  apply lucas_primality 30323 (2 : ZMod 30323)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 30323 - 1 = (2 : ℕ)^1 * ((15161 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 30323)^15161 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 15161 := Nat.prime_eq_prime_of_dvd_pow hq prime_15161 hd
      subst q
      change (2 : ZMod 30323)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_30427 : Nat.Prime 30427 := by
  apply lucas_primality 30427 (5 : ZMod 30427)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 30427 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((461 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 30427)^15213 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 30427)^10142 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 30427)^2766 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 461 := Nat.prime_eq_prime_of_dvd_pow hq prime_461 hd
          subst q
          change (5 : ZMod 30427)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_30529 : Nat.Prime 30529 := by
  apply lucas_primality 30529 (13 : ZMod 30529)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 30529 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^2 * ((53 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 30529)^15264 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 30529)^10176 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
        subst q
        change (13 : ZMod 30529)^576 ≠ 1
        reduce_mod_char
        decide

theorem prime_30649 : Nat.Prime 30649 := by
  apply lucas_primality 30649 (7 : ZMod 30649)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 30649 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((1277 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 30649)^15324 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 30649)^10216 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1277 := Nat.prime_eq_prime_of_dvd_pow hq prime_1277 hd
        subst q
        change (7 : ZMod 30649)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_30677 : Nat.Prime 30677 := by
  apply lucas_primality 30677 (2 : ZMod 30677)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 30677 - 1 = (2 : ℕ)^2 * ((7669 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 30677)^15338 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 7669 := Nat.prime_eq_prime_of_dvd_pow hq prime_7669 hd
      subst q
      change (2 : ZMod 30677)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_30689 : Nat.Prime 30689 := by
  apply lucas_primality 30689 (3 : ZMod 30689)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 30689 - 1 = (2 : ℕ)^5 * ((7 : ℕ)^1 * ((137 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 30689)^15344 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 30689)^4384 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
        subst q
        change (3 : ZMod 30689)^224 ≠ 1
        reduce_mod_char
        decide

theorem prime_30757 : Nat.Prime 30757 := by
  apply lucas_primality 30757 (5 : ZMod 30757)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 30757 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((233 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 30757)^15378 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 30757)^10252 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 30757)^2796 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
          subst q
          change (5 : ZMod 30757)^132 ≠ 1
          reduce_mod_char
          decide

theorem prime_30773 : Nat.Prime 30773 := by
  apply lucas_primality 30773 (3 : ZMod 30773)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 30773 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^2 * ((157 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 30773)^15386 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 30773)^4396 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
        subst q
        change (3 : ZMod 30773)^196 ≠ 1
        reduce_mod_char
        decide

theorem prime_31181 : Nat.Prime 31181 := by
  apply lucas_primality 31181 (2 : ZMod 31181)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 31181 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((1559 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 31181)^15590 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 31181)^6236 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1559 := Nat.prime_eq_prime_of_dvd_pow hq prime_1559 hd
        subst q
        change (2 : ZMod 31181)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_31189 : Nat.Prime 31189 := by
  apply lucas_primality 31189 (13 : ZMod 31189)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 31189 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((113 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 31189)^15594 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 31189)^10396 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (13 : ZMod 31189)^1356 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
          subst q
          change (13 : ZMod 31189)^276 ≠ 1
          reduce_mod_char
          decide

theorem prime_31259 : Nat.Prime 31259 := by
  apply lucas_primality 31259 (2 : ZMod 31259)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 31259 - 1 = (2 : ℕ)^1 * ((15629 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 31259)^15629 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 15629 := Nat.prime_eq_prime_of_dvd_pow hq prime_15629 hd
      subst q
      change (2 : ZMod 31259)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_31333 : Nat.Prime 31333 := by
  apply lucas_primality 31333 (5 : ZMod 31333)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 31333 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((373 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 31333)^15666 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 31333)^10444 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 31333)^4476 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 373 := Nat.prime_eq_prime_of_dvd_pow hq prime_373 hd
          subst q
          change (5 : ZMod 31333)^84 ≠ 1
          reduce_mod_char
          decide

theorem prime_31337 : Nat.Prime 31337 := by
  apply lucas_primality 31337 (3 : ZMod 31337)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 31337 - 1 = (2 : ℕ)^3 * ((3917 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 31337)^15668 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3917 := Nat.prime_eq_prime_of_dvd_pow hq prime_3917 hd
      subst q
      change (3 : ZMod 31337)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_31357 : Nat.Prime 31357 := by
  apply lucas_primality 31357 (2 : ZMod 31357)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 31357 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((13 : ℕ)^1 * ((67 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 31357)^15678 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 31357)^10452 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 31357)^2412 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (2 : ZMod 31357)^468 ≠ 1
          reduce_mod_char
          decide

theorem prime_31489 : Nat.Prime 31489 := by
  apply lucas_primality 31489 (7 : ZMod 31489)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 31489 - 1 = (2 : ℕ)^8 * ((3 : ℕ)^1 * ((41 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 31489)^15744 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 31489)^10496 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
        subst q
        change (7 : ZMod 31489)^768 ≠ 1
        reduce_mod_char
        decide

theorem prime_31643 : Nat.Prime 31643 := by
  apply lucas_primality 31643 (2 : ZMod 31643)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 31643 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((1217 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 31643)^15821 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 31643)^2434 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1217 := Nat.prime_eq_prime_of_dvd_pow hq prime_1217 hd
        subst q
        change (2 : ZMod 31643)^26 ≠ 1
        reduce_mod_char
        decide

theorem prime_31649 : Nat.Prime 31649 := by
  apply lucas_primality 31649 (3 : ZMod 31649)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 31649 - 1 = (2 : ℕ)^5 * ((23 : ℕ)^1 * ((43 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 31649)^15824 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (3 : ZMod 31649)^1376 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
        subst q
        change (3 : ZMod 31649)^736 ≠ 1
        reduce_mod_char
        decide

theorem prime_31657 : Nat.Prime 31657 := by
  apply lucas_primality 31657 (5 : ZMod 31657)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 31657 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((1319 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 31657)^15828 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 31657)^10552 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1319 := Nat.prime_eq_prime_of_dvd_pow hq prime_1319 hd
        subst q
        change (5 : ZMod 31657)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_31723 : Nat.Prime 31723 := by
  apply lucas_primality 31723 (3 : ZMod 31723)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 31723 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((311 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 31723)^15861 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 31723)^10574 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (3 : ZMod 31723)^1866 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 311 := Nat.prime_eq_prime_of_dvd_pow hq prime_311 hd
          subst q
          change (3 : ZMod 31723)^102 ≠ 1
          reduce_mod_char
          decide

theorem prime_31793 : Nat.Prime 31793 := by
  apply lucas_primality 31793 (3 : ZMod 31793)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 31793 - 1 = (2 : ℕ)^4 * ((1987 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 31793)^15896 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1987 := Nat.prime_eq_prime_of_dvd_pow hq prime_1987 hd
      subst q
      change (3 : ZMod 31793)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_32099 : Nat.Prime 32099 := by
  apply lucas_primality 32099 (2 : ZMod 32099)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32099 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((1459 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 32099)^16049 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 32099)^2918 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1459 := Nat.prime_eq_prime_of_dvd_pow hq prime_1459 hd
        subst q
        change (2 : ZMod 32099)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_32191 : Nat.Prime 32191 := by
  apply lucas_primality 32191 (6 : ZMod 32191)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32191 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((29 : ℕ)^1 * ((37 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 32191)^16095 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 32191)^10730 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 32191)^6438 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (6 : ZMod 32191)^1110 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
            subst q
            change (6 : ZMod 32191)^870 ≠ 1
            reduce_mod_char
            decide

theorem prime_32237 : Nat.Prime 32237 := by
  apply lucas_primality 32237 (2 : ZMod 32237)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32237 - 1 = (2 : ℕ)^2 * ((8059 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 32237)^16118 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 8059 := Nat.prime_eq_prime_of_dvd_pow hq prime_8059 hd
      subst q
      change (2 : ZMod 32237)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_32303 : Nat.Prime 32303 := by
  apply lucas_primality 32303 (5 : ZMod 32303)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32303 - 1 = (2 : ℕ)^1 * ((31 : ℕ)^1 * ((521 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 32303)^16151 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (5 : ZMod 32303)^1042 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 521 := Nat.prime_eq_prime_of_dvd_pow hq prime_521 hd
        subst q
        change (5 : ZMod 32303)^62 ≠ 1
        reduce_mod_char
        decide

theorem prime_32413 : Nat.Prime 32413 := by
  apply lucas_primality 32413 (5 : ZMod 32413)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32413 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((37 : ℕ)^1 * ((73 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 32413)^16206 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 32413)^10804 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (5 : ZMod 32413)^876 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
          subst q
          change (5 : ZMod 32413)^444 ≠ 1
          reduce_mod_char
          decide

theorem prime_32503 : Nat.Prime 32503 := by
  apply lucas_primality 32503 (3 : ZMod 32503)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32503 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5417 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 32503)^16251 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 32503)^10834 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5417 := Nat.prime_eq_prime_of_dvd_pow hq prime_5417 hd
        subst q
        change (3 : ZMod 32503)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_32531 : Nat.Prime 32531 := by
  apply lucas_primality 32531 (2 : ZMod 32531)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32531 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((3253 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 32531)^16265 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 32531)^6506 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3253 := Nat.prime_eq_prime_of_dvd_pow hq prime_3253 hd
        subst q
        change (2 : ZMod 32531)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_32611 : Nat.Prime 32611 := by
  apply lucas_primality 32611 (3 : ZMod 32611)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32611 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((1087 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 32611)^16305 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 32611)^10870 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 32611)^6522 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1087 := Nat.prime_eq_prime_of_dvd_pow hq prime_1087 hd
          subst q
          change (3 : ZMod 32611)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_32707 : Nat.Prime 32707 := by
  apply lucas_primality 32707 (3 : ZMod 32707)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32707 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((23 : ℕ)^1 * ((79 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 32707)^16353 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 32707)^10902 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (3 : ZMod 32707)^1422 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (3 : ZMod 32707)^414 ≠ 1
          reduce_mod_char
          decide

theorem prime_32839 : Nat.Prime 32839 := by
  apply lucas_primality 32839 (6 : ZMod 32839)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32839 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((421 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 32839)^16419 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 32839)^10946 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (6 : ZMod 32839)^2526 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 421 := Nat.prime_eq_prime_of_dvd_pow hq prime_421 hd
          subst q
          change (6 : ZMod 32839)^78 ≠ 1
          reduce_mod_char
          decide

theorem prime_32983 : Nat.Prime 32983 := by
  apply lucas_primality 32983 (3 : ZMod 32983)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32983 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((239 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 32983)^16491 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 32983)^10994 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (3 : ZMod 32983)^1434 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 239 := Nat.prime_eq_prime_of_dvd_pow hq prime_239 hd
          subst q
          change (3 : ZMod 32983)^138 ≠ 1
          reduce_mod_char
          decide

theorem prime_32987 : Nat.Prime 32987 := by
  apply lucas_primality 32987 (2 : ZMod 32987)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32987 - 1 = (2 : ℕ)^1 * ((16493 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 32987)^16493 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 16493 := Nat.prime_eq_prime_of_dvd_pow hq prime_16493 hd
      subst q
      change (2 : ZMod 32987)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_33247 : Nat.Prime 33247 := by
  apply lucas_primality 33247 (5 : ZMod 33247)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 33247 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((1847 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 33247)^16623 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 33247)^11082 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1847 := Nat.prime_eq_prime_of_dvd_pow hq prime_1847 hd
        subst q
        change (5 : ZMod 33247)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_33349 : Nat.Prime 33349 := by
  apply lucas_primality 33349 (2 : ZMod 33349)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 33349 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((397 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 33349)^16674 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 33349)^11116 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 33349)^4764 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 397 := Nat.prime_eq_prime_of_dvd_pow hq prime_397 hd
          subst q
          change (2 : ZMod 33349)^84 ≠ 1
          reduce_mod_char
          decide

theorem prime_33403 : Nat.Prime 33403 := by
  apply lucas_primality 33403 (3 : ZMod 33403)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 33403 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((293 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 33403)^16701 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 33403)^11134 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (3 : ZMod 33403)^1758 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 293 := Nat.prime_eq_prime_of_dvd_pow hq prime_293 hd
          subst q
          change (3 : ZMod 33403)^114 ≠ 1
          reduce_mod_char
          decide

theorem prime_33457 : Nat.Prime 33457 := by
  apply lucas_primality 33457 (10 : ZMod 33457)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 33457 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((41 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 33457)^16728 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 33457)^11152 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (10 : ZMod 33457)^1968 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (10 : ZMod 33457)^816 ≠ 1
          reduce_mod_char
          decide

theorem prime_33623 : Nat.Prime 33623 := by
  apply lucas_primality 33623 (5 : ZMod 33623)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 33623 - 1 = (2 : ℕ)^1 * ((16811 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 33623)^16811 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 16811 := Nat.prime_eq_prime_of_dvd_pow hq prime_16811 hd
      subst q
      change (5 : ZMod 33623)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_33757 : Nat.Prime 33757 := by
  apply lucas_primality 33757 (2 : ZMod 33757)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 33757 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((29 : ℕ)^1 * ((97 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 33757)^16878 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 33757)^11252 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (2 : ZMod 33757)^1164 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
          subst q
          change (2 : ZMod 33757)^348 ≠ 1
          reduce_mod_char
          decide

theorem prime_33769 : Nat.Prime 33769 := by
  apply lucas_primality 33769 (11 : ZMod 33769)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 33769 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((67 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 33769)^16884 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 33769)^11256 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (11 : ZMod 33769)^4824 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (11 : ZMod 33769)^504 ≠ 1
          reduce_mod_char
          decide

theorem prime_33809 : Nat.Prime 33809 := by
  apply lucas_primality 33809 (3 : ZMod 33809)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 33809 - 1 = (2 : ℕ)^4 * ((2113 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 33809)^16904 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 2113 := Nat.prime_eq_prime_of_dvd_pow hq prime_2113 hd
      subst q
      change (3 : ZMod 33809)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_33937 : Nat.Prime 33937 := by
  apply lucas_primality 33937 (5 : ZMod 33937)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 33937 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((101 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 33937)^16968 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 33937)^11312 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 33937)^4848 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
          subst q
          change (5 : ZMod 33937)^336 ≠ 1
          reduce_mod_char
          decide

theorem prime_33997 : Nat.Prime 33997 := by
  apply lucas_primality 33997 (2 : ZMod 33997)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 33997 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((2833 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 33997)^16998 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 33997)^11332 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2833 := Nat.prime_eq_prime_of_dvd_pow hq prime_2833 hd
        subst q
        change (2 : ZMod 33997)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_34057 : Nat.Prime 34057 := by
  apply lucas_primality 34057 (5 : ZMod 34057)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34057 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((43 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 34057)^17028 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 34057)^11352 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 34057)^3096 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (5 : ZMod 34057)^792 ≠ 1
          reduce_mod_char
          decide

theorem prime_34141 : Nat.Prime 34141 := by
  apply lucas_primality 34141 (2 : ZMod 34141)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34141 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((569 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 34141)^17070 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 34141)^11380 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 34141)^6828 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 569 := Nat.prime_eq_prime_of_dvd_pow hq prime_569 hd
          subst q
          change (2 : ZMod 34141)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_34147 : Nat.Prime 34147 := by
  apply lucas_primality 34147 (3 : ZMod 34147)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34147 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((271 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 34147)^17073 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 34147)^11382 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 34147)^4878 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 271 := Nat.prime_eq_prime_of_dvd_pow hq prime_271 hd
          subst q
          change (3 : ZMod 34147)^126 ≠ 1
          reduce_mod_char
          decide

theorem prime_34253 : Nat.Prime 34253 := by
  apply lucas_primality 34253 (2 : ZMod 34253)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34253 - 1 = (2 : ℕ)^2 * ((8563 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 34253)^17126 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 8563 := Nat.prime_eq_prime_of_dvd_pow hq prime_8563 hd
      subst q
      change (2 : ZMod 34253)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_34303 : Nat.Prime 34303 := by
  apply lucas_primality 34303 (17 : ZMod 34303)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34303 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5717 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 34303)^17151 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 34303)^11434 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5717 := Nat.prime_eq_prime_of_dvd_pow hq prime_5717 hd
        subst q
        change (17 : ZMod 34303)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_34313 : Nat.Prime 34313 := by
  apply lucas_primality 34313 (3 : ZMod 34313)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34313 - 1 = (2 : ℕ)^3 * ((4289 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 34313)^17156 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 4289 := Nat.prime_eq_prime_of_dvd_pow hq prime_4289 hd
      subst q
      change (3 : ZMod 34313)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_34403 : Nat.Prime 34403 := by
  apply lucas_primality 34403 (2 : ZMod 34403)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34403 - 1 = (2 : ℕ)^1 * ((103 : ℕ)^1 * ((167 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 34403)^17201 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
        subst q
        change (2 : ZMod 34403)^334 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
        subst q
        change (2 : ZMod 34403)^206 ≠ 1
        reduce_mod_char
        decide

theorem prime_34649 : Nat.Prime 34649 := by
  apply lucas_primality 34649 (3 : ZMod 34649)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34649 - 1 = (2 : ℕ)^3 * ((61 : ℕ)^1 * ((71 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 34649)^17324 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
        subst q
        change (3 : ZMod 34649)^568 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
        subst q
        change (3 : ZMod 34649)^488 ≠ 1
        reduce_mod_char
        decide

theorem prime_34739 : Nat.Prime 34739 := by
  apply lucas_primality 34739 (6 : ZMod 34739)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34739 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((1579 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 34739)^17369 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (6 : ZMod 34739)^3158 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1579 := Nat.prime_eq_prime_of_dvd_pow hq prime_1579 hd
        subst q
        change (6 : ZMod 34739)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_34871 : Nat.Prime 34871 := by
  apply lucas_primality 34871 (7 : ZMod 34871)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34871 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((317 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 34871)^17435 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 34871)^6974 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (7 : ZMod 34871)^3170 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 317 := Nat.prime_eq_prime_of_dvd_pow hq prime_317 hd
          subst q
          change (7 : ZMod 34871)^110 ≠ 1
          reduce_mod_char
          decide

theorem prime_34877 : Nat.Prime 34877 := by
  apply lucas_primality 34877 (2 : ZMod 34877)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34877 - 1 = (2 : ℕ)^2 * ((8719 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 34877)^17438 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 8719 := Nat.prime_eq_prime_of_dvd_pow hq prime_8719 hd
      subst q
      change (2 : ZMod 34877)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_34913 : Nat.Prime 34913 := by
  apply lucas_primality 34913 (3 : ZMod 34913)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34913 - 1 = (2 : ℕ)^5 * ((1091 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 34913)^17456 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1091 := Nat.prime_eq_prime_of_dvd_pow hq prime_1091 hd
      subst q
      change (3 : ZMod 34913)^32 ≠ 1
      reduce_mod_char
      decide

theorem prime_34961 : Nat.Prime 34961 := by
  apply lucas_primality 34961 (3 : ZMod 34961)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34961 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((19 : ℕ)^1 * ((23 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 34961)^17480 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 34961)^6992 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (3 : ZMod 34961)^1840 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (3 : ZMod 34961)^1520 ≠ 1
          reduce_mod_char
          decide

theorem prime_34981 : Nat.Prime 34981 := by
  apply lucas_primality 34981 (2 : ZMod 34981)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34981 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((53 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 34981)^17490 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 34981)^11660 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 34981)^6996 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (2 : ZMod 34981)^3180 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
            subst q
            change (2 : ZMod 34981)^660 ≠ 1
            reduce_mod_char
            decide

theorem prime_35051 : Nat.Prime 35051 := by
  apply lucas_primality 35051 (2 : ZMod 35051)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 35051 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((701 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 35051)^17525 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 35051)^7010 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 701 := Nat.prime_eq_prime_of_dvd_pow hq prime_701 hd
        subst q
        change (2 : ZMod 35051)^50 ≠ 1
        reduce_mod_char
        decide

theorem prime_35089 : Nat.Prime 35089 := by
  apply lucas_primality 35089 (11 : ZMod 35089)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 35089 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((43 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 35089)^17544 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 35089)^11696 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (11 : ZMod 35089)^2064 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (11 : ZMod 35089)^816 ≠ 1
          reduce_mod_char
          decide

theorem prime_35141 : Nat.Prime 35141 := by
  apply lucas_primality 35141 (2 : ZMod 35141)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 35141 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((251 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 35141)^17570 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 35141)^7028 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 35141)^5020 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 251 := Nat.prime_eq_prime_of_dvd_pow hq prime_251 hd
          subst q
          change (2 : ZMod 35141)^140 ≠ 1
          reduce_mod_char
          decide

theorem prime_35257 : Nat.Prime 35257 := by
  apply lucas_primality 35257 (7 : ZMod 35257)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 35257 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((113 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 35257)^17628 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 35257)^11752 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (7 : ZMod 35257)^2712 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
          subst q
          change (7 : ZMod 35257)^312 ≠ 1
          reduce_mod_char
          decide

theorem prime_35267 : Nat.Prime 35267 := by
  apply lucas_primality 35267 (2 : ZMod 35267)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 35267 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((229 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 35267)^17633 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 35267)^5038 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 35267)^3206 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 229 := Nat.prime_eq_prime_of_dvd_pow hq prime_229 hd
          subst q
          change (2 : ZMod 35267)^154 ≠ 1
          reduce_mod_char
          decide

theorem prime_35521 : Nat.Prime 35521 := by
  apply lucas_primality 35521 (7 : ZMod 35521)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 35521 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((37 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 35521)^17760 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 35521)^11840 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 35521)^7104 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (7 : ZMod 35521)^960 ≠ 1
          reduce_mod_char
          decide

theorem prime_35533 : Nat.Prime 35533 := by
  apply lucas_primality 35533 (2 : ZMod 35533)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 35533 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((47 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 35533)^17766 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 35533)^11844 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 35533)^5076 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (2 : ZMod 35533)^756 ≠ 1
          reduce_mod_char
          decide

theorem prime_35831 : Nat.Prime 35831 := by
  apply lucas_primality 35831 (11 : ZMod 35831)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 35831 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((3583 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 35831)^17915 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 35831)^7166 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3583 := Nat.prime_eq_prime_of_dvd_pow hq prime_3583 hd
        subst q
        change (11 : ZMod 35831)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_35863 : Nat.Prime 35863 := by
  apply lucas_primality 35863 (3 : ZMod 35863)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 35863 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((43 : ℕ)^1 * ((139 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 35863)^17931 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 35863)^11954 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (3 : ZMod 35863)^834 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
          subst q
          change (3 : ZMod 35863)^258 ≠ 1
          reduce_mod_char
          decide

theorem prime_36097 : Nat.Prime 36097 := by
  apply lucas_primality 36097 (5 : ZMod 36097)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 36097 - 1 = (2 : ℕ)^8 * ((3 : ℕ)^1 * ((47 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 36097)^18048 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 36097)^12032 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (5 : ZMod 36097)^768 ≠ 1
        reduce_mod_char
        decide

theorem prime_36107 : Nat.Prime 36107 := by
  apply lucas_primality 36107 (2 : ZMod 36107)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 36107 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((2579 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 36107)^18053 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 36107)^5158 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2579 := Nat.prime_eq_prime_of_dvd_pow hq prime_2579 hd
        subst q
        change (2 : ZMod 36107)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_36217 : Nat.Prime 36217 := by
  apply lucas_primality 36217 (19 : ZMod 36217)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 36217 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((503 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 36217)^18108 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 36217)^12072 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 503 := Nat.prime_eq_prime_of_dvd_pow hq prime_503 hd
        subst q
        change (19 : ZMod 36217)^72 ≠ 1
        reduce_mod_char
        decide

theorem prime_36353 : Nat.Prime 36353 := by
  apply lucas_primality 36353 (3 : ZMod 36353)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 36353 - 1 = (2 : ℕ)^9 * ((71 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 36353)^18176 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
      subst q
      change (3 : ZMod 36353)^512 ≠ 1
      reduce_mod_char
      decide

theorem prime_36433 : Nat.Prime 36433 := by
  apply lucas_primality 36433 (5 : ZMod 36433)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 36433 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((23 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 36433)^18216 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 36433)^12144 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 36433)^3312 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (5 : ZMod 36433)^1584 ≠ 1
          reduce_mod_char
          decide

theorem prime_36457 : Nat.Prime 36457 := by
  apply lucas_primality 36457 (5 : ZMod 36457)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 36457 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((31 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 36457)^18228 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 36457)^12152 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 36457)^5208 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (5 : ZMod 36457)^1176 ≠ 1
          reduce_mod_char
          decide

theorem prime_36529 : Nat.Prime 36529 := by
  apply lucas_primality 36529 (7 : ZMod 36529)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 36529 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((761 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 36529)^18264 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 36529)^12176 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 761 := Nat.prime_eq_prime_of_dvd_pow hq prime_761 hd
        subst q
        change (7 : ZMod 36529)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_36583 : Nat.Prime 36583 := by
  apply lucas_primality 36583 (7 : ZMod 36583)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 36583 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((67 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 36583)^18291 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 36583)^12194 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 36583)^5226 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (7 : ZMod 36583)^2814 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
            subst q
            change (7 : ZMod 36583)^546 ≠ 1
            reduce_mod_char
            decide

theorem prime_36671 : Nat.Prime 36671 := by
  apply lucas_primality 36671 (13 : ZMod 36671)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 36671 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((19 : ℕ)^1 * ((193 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 36671)^18335 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (13 : ZMod 36671)^7334 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (13 : ZMod 36671)^1930 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
          subst q
          change (13 : ZMod 36671)^190 ≠ 1
          reduce_mod_char
          decide

theorem prime_36833 : Nat.Prime 36833 := by
  apply lucas_primality 36833 (3 : ZMod 36833)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 36833 - 1 = (2 : ℕ)^5 * ((1151 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 36833)^18416 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1151 := Nat.prime_eq_prime_of_dvd_pow hq prime_1151 hd
      subst q
      change (3 : ZMod 36833)^32 ≠ 1
      reduce_mod_char
      decide

theorem prime_36997 : Nat.Prime 36997 := by
  apply lucas_primality 36997 (2 : ZMod 36997)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 36997 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((3083 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 36997)^18498 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 36997)^12332 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3083 := Nat.prime_eq_prime_of_dvd_pow hq prime_3083 hd
        subst q
        change (2 : ZMod 36997)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_37117 : Nat.Prime 37117 := by
  apply lucas_primality 37117 (2 : ZMod 37117)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 37117 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((1031 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 37117)^18558 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 37117)^12372 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1031 := Nat.prime_eq_prime_of_dvd_pow hq prime_1031 hd
        subst q
        change (2 : ZMod 37117)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_37181 : Nat.Prime 37181 := by
  apply lucas_primality 37181 (2 : ZMod 37181)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 37181 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^2))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 37181)^18590 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 37181)^7436 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 37181)^3380 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 37181)^2860 ≠ 1
          reduce_mod_char
          decide

theorem prime_37217 : Nat.Prime 37217 := by
  apply lucas_primality 37217 (3 : ZMod 37217)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 37217 - 1 = (2 : ℕ)^5 * ((1163 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 37217)^18608 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1163 := Nat.prime_eq_prime_of_dvd_pow hq prime_1163 hd
      subst q
      change (3 : ZMod 37217)^32 ≠ 1
      reduce_mod_char
      decide

theorem prime_37361 : Nat.Prime 37361 := by
  apply lucas_primality 37361 (3 : ZMod 37361)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 37361 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((467 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 37361)^18680 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 37361)^7472 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 467 := Nat.prime_eq_prime_of_dvd_pow hq prime_467 hd
        subst q
        change (3 : ZMod 37361)^80 ≠ 1
        reduce_mod_char
        decide

theorem prime_37379 : Nat.Prime 37379 := by
  apply lucas_primality 37379 (2 : ZMod 37379)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 37379 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((1699 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 37379)^18689 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 37379)^3398 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1699 := Nat.prime_eq_prime_of_dvd_pow hq prime_1699 hd
        subst q
        change (2 : ZMod 37379)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_37501 : Nat.Prime 37501 := by
  apply lucas_primality 37501 (2 : ZMod 37501)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 37501 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^5)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 37501)^18750 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 37501)^12500 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 37501)^7500 ≠ 1
        reduce_mod_char
        decide

theorem prime_37591 : Nat.Prime 37591 := by
  apply lucas_primality 37591 (6 : ZMod 37591)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 37591 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((179 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 37591)^18795 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 37591)^12530 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 37591)^7518 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (6 : ZMod 37591)^5370 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 179 := Nat.prime_eq_prime_of_dvd_pow hq prime_179 hd
            subst q
            change (6 : ZMod 37591)^210 ≠ 1
            reduce_mod_char
            decide

theorem prime_37643 : Nat.Prime 37643 := by
  apply lucas_primality 37643 (2 : ZMod 37643)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 37643 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((29 : ℕ)^1 * ((59 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 37643)^18821 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 37643)^3422 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (2 : ZMod 37643)^1298 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (2 : ZMod 37643)^638 ≠ 1
          reduce_mod_char
          decide

theorem prime_37657 : Nat.Prime 37657 := by
  apply lucas_primality 37657 (5 : ZMod 37657)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 37657 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((523 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 37657)^18828 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 37657)^12552 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 523 := Nat.prime_eq_prime_of_dvd_pow hq prime_523 hd
        subst q
        change (5 : ZMod 37657)^72 ≠ 1
        reduce_mod_char
        decide

theorem prime_37993 : Nat.Prime 37993 := by
  apply lucas_primality 37993 (10 : ZMod 37993)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 37993 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((1583 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 37993)^18996 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 37993)^12664 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1583 := Nat.prime_eq_prime_of_dvd_pow hq prime_1583 hd
        subst q
        change (10 : ZMod 37993)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_38011 : Nat.Prime 38011 := by
  apply lucas_primality 38011 (2 : ZMod 38011)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 38011 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((181 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 38011)^19005 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 38011)^12670 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 38011)^7602 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (2 : ZMod 38011)^5430 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 181 := Nat.prime_eq_prime_of_dvd_pow hq prime_181 hd
            subst q
            change (2 : ZMod 38011)^210 ≠ 1
            reduce_mod_char
            decide

theorem prime_38047 : Nat.Prime 38047 := by
  apply lucas_primality 38047 (3 : ZMod 38047)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 38047 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((373 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 38047)^19023 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 38047)^12682 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (3 : ZMod 38047)^2238 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 373 := Nat.prime_eq_prime_of_dvd_pow hq prime_373 hd
          subst q
          change (3 : ZMod 38047)^102 ≠ 1
          reduce_mod_char
          decide

theorem prime_38239 : Nat.Prime 38239 := by
  apply lucas_primality 38239 (13 : ZMod 38239)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 38239 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((6373 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 38239)^19119 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 38239)^12746 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 6373 := Nat.prime_eq_prime_of_dvd_pow hq prime_6373 hd
        subst q
        change (13 : ZMod 38239)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_38371 : Nat.Prime 38371 := by
  apply lucas_primality 38371 (10 : ZMod 38371)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 38371 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((1279 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 38371)^19185 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 38371)^12790 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 38371)^7674 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1279 := Nat.prime_eq_prime_of_dvd_pow hq prime_1279 hd
          subst q
          change (10 : ZMod 38371)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_38377 : Nat.Prime 38377 := by
  apply lucas_primality 38377 (5 : ZMod 38377)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 38377 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((13 : ℕ)^1 * ((41 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 38377)^19188 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 38377)^12792 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (5 : ZMod 38377)^2952 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (5 : ZMod 38377)^936 ≠ 1
          reduce_mod_char
          decide

theorem prime_38393 : Nat.Prime 38393 := by
  apply lucas_primality 38393 (3 : ZMod 38393)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 38393 - 1 = (2 : ℕ)^3 * ((4799 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 38393)^19196 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 4799 := Nat.prime_eq_prime_of_dvd_pow hq prime_4799 hd
      subst q
      change (3 : ZMod 38393)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_38449 : Nat.Prime 38449 := by
  apply lucas_primality 38449 (13 : ZMod 38449)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 38449 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^3 * ((89 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 38449)^19224 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 38449)^12816 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
        subst q
        change (13 : ZMod 38449)^432 ≠ 1
        reduce_mod_char
        decide

theorem prime_38557 : Nat.Prime 38557 := by
  apply lucas_primality 38557 (2 : ZMod 38557)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 38557 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^4 * ((7 : ℕ)^1 * ((17 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 38557)^19278 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 38557)^12852 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 38557)^5508 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 38557)^2268 ≠ 1
          reduce_mod_char
          decide

theorem prime_38569 : Nat.Prime 38569 := by
  apply lucas_primality 38569 (14 : ZMod 38569)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 38569 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((1607 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 38569)^19284 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 38569)^12856 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1607 := Nat.prime_eq_prime_of_dvd_pow hq prime_1607 hd
        subst q
        change (14 : ZMod 38569)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_38609 : Nat.Prime 38609 := by
  apply lucas_primality 38609 (3 : ZMod 38609)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 38609 - 1 = (2 : ℕ)^4 * ((19 : ℕ)^1 * ((127 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 38609)^19304 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (3 : ZMod 38609)^2032 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
        subst q
        change (3 : ZMod 38609)^304 ≠ 1
        reduce_mod_char
        decide

theorem prime_38611 : Nat.Prime 38611 := by
  apply lucas_primality 38611 (3 : ZMod 38611)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 38611 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 38611)^19305 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 38611)^12870 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 38611)^7722 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (3 : ZMod 38611)^3510 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (3 : ZMod 38611)^2970 ≠ 1
            reduce_mod_char
            decide

theorem prime_38677 : Nat.Prime 38677 := by
  apply lucas_primality 38677 (5 : ZMod 38677)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 38677 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((293 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 38677)^19338 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 38677)^12892 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 38677)^3516 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 293 := Nat.prime_eq_prime_of_dvd_pow hq prime_293 hd
          subst q
          change (5 : ZMod 38677)^132 ≠ 1
          reduce_mod_char
          decide

theorem prime_38707 : Nat.Prime 38707 := by
  apply lucas_primality 38707 (2 : ZMod 38707)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 38707 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((6451 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 38707)^19353 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 38707)^12902 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 6451 := Nat.prime_eq_prime_of_dvd_pow hq prime_6451 hd
        subst q
        change (2 : ZMod 38707)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_38723 : Nat.Prime 38723 := by
  apply lucas_primality 38723 (2 : ZMod 38723)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 38723 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((1019 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 38723)^19361 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 38723)^2038 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1019 := Nat.prime_eq_prime_of_dvd_pow hq prime_1019 hd
        subst q
        change (2 : ZMod 38723)^38 ≠ 1
        reduce_mod_char
        decide

theorem prime_38861 : Nat.Prime 38861 := by
  apply lucas_primality 38861 (14 : ZMod 38861)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 38861 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((29 : ℕ)^1 * ((67 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 38861)^19430 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (14 : ZMod 38861)^7772 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (14 : ZMod 38861)^1340 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (14 : ZMod 38861)^580 ≠ 1
          reduce_mod_char
          decide

theorem prime_39107 : Nat.Prime 39107 := by
  apply lucas_primality 39107 (2 : ZMod 39107)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 39107 - 1 = (2 : ℕ)^1 * ((19553 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 39107)^19553 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 19553 := Nat.prime_eq_prime_of_dvd_pow hq prime_19553 hd
      subst q
      change (2 : ZMod 39107)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_39161 : Nat.Prime 39161 := by
  apply lucas_primality 39161 (3 : ZMod 39161)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 39161 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((89 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 39161)^19580 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 39161)^7832 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 39161)^3560 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (3 : ZMod 39161)^440 ≠ 1
          reduce_mod_char
          decide

theorem prime_39233 : Nat.Prime 39233 := by
  apply lucas_primality 39233 (3 : ZMod 39233)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 39233 - 1 = (2 : ℕ)^6 * ((613 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 39233)^19616 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 613 := Nat.prime_eq_prime_of_dvd_pow hq prime_613 hd
      subst q
      change (3 : ZMod 39233)^64 ≠ 1
      reduce_mod_char
      decide

theorem prime_39419 : Nat.Prime 39419 := by
  apply lucas_primality 39419 (2 : ZMod 39419)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 39419 - 1 = (2 : ℕ)^1 * ((19709 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 39419)^19709 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 19709 := Nat.prime_eq_prime_of_dvd_pow hq prime_19709 hd
      subst q
      change (2 : ZMod 39419)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_39631 : Nat.Prime 39631 := by
  apply lucas_primality 39631 (3 : ZMod 39631)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 39631 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((1321 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 39631)^19815 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 39631)^13210 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 39631)^7926 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1321 := Nat.prime_eq_prime_of_dvd_pow hq prime_1321 hd
          subst q
          change (3 : ZMod 39631)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_39779 : Nat.Prime 39779 := by
  apply lucas_primality 39779 (2 : ZMod 39779)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 39779 - 1 = (2 : ℕ)^1 * ((19889 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 39779)^19889 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 19889 := Nat.prime_eq_prime_of_dvd_pow hq prime_19889 hd
      subst q
      change (2 : ZMod 39779)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_39887 : Nat.Prime 39887 := by
  apply lucas_primality 39887 (7 : ZMod 39887)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 39887 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^2 * ((11 : ℕ)^1 * ((37 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 39887)^19943 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 39887)^5698 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (7 : ZMod 39887)^3626 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (7 : ZMod 39887)^1078 ≠ 1
          reduce_mod_char
          decide

theorem prime_40127 : Nat.Prime 40127 := by
  apply lucas_primality 40127 (5 : ZMod 40127)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 40127 - 1 = (2 : ℕ)^1 * ((20063 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 40127)^20063 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 20063 := Nat.prime_eq_prime_of_dvd_pow hq prime_20063 hd
      subst q
      change (5 : ZMod 40127)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_40231 : Nat.Prime 40231 := by
  apply lucas_primality 40231 (3 : ZMod 40231)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 40231 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((149 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 40231)^20115 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 40231)^13410 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 40231)^8046 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
          subst q
          change (3 : ZMod 40231)^270 ≠ 1
          reduce_mod_char
          decide

theorem prime_40343 : Nat.Prime 40343 := by
  apply lucas_primality 40343 (5 : ZMod 40343)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 40343 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((877 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 40343)^20171 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (5 : ZMod 40343)^1754 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 877 := Nat.prime_eq_prime_of_dvd_pow hq prime_877 hd
        subst q
        change (5 : ZMod 40343)^46 ≠ 1
        reduce_mod_char
        decide

theorem prime_40387 : Nat.Prime 40387 := by
  apply lucas_primality 40387 (2 : ZMod 40387)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 40387 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((53 : ℕ)^1 * ((127 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 40387)^20193 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 40387)^13462 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (2 : ZMod 40387)^762 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
          subst q
          change (2 : ZMod 40387)^318 ≠ 1
          reduce_mod_char
          decide

theorem prime_40507 : Nat.Prime 40507 := by
  apply lucas_primality 40507 (2 : ZMod 40507)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 40507 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((43 : ℕ)^1 * ((157 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 40507)^20253 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 40507)^13502 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (2 : ZMod 40507)^942 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
          subst q
          change (2 : ZMod 40507)^258 ≠ 1
          reduce_mod_char
          decide

theorem prime_40531 : Nat.Prime 40531 := by
  apply lucas_primality 40531 (2 : ZMod 40531)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 40531 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((193 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 40531)^20265 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 40531)^13510 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 40531)^8106 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (2 : ZMod 40531)^5790 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
            subst q
            change (2 : ZMod 40531)^210 ≠ 1
            reduce_mod_char
            decide

theorem prime_40801 : Nat.Prime 40801 := by
  apply lucas_primality 40801 (13 : ZMod 40801)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 40801 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((17 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 40801)^20400 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 40801)^13600 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 40801)^8160 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (13 : ZMod 40801)^2400 ≠ 1
          reduce_mod_char
          decide

theorem prime_40853 : Nat.Prime 40853 := by
  apply lucas_primality 40853 (2 : ZMod 40853)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 40853 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((1459 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 40853)^20426 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 40853)^5836 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1459 := Nat.prime_eq_prime_of_dvd_pow hq prime_1459 hd
        subst q
        change (2 : ZMod 40853)^28 ≠ 1
        reduce_mod_char
        decide

theorem prime_40903 : Nat.Prime 40903 := by
  apply lucas_primality 40903 (3 : ZMod 40903)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 40903 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((401 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 40903)^20451 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 40903)^13634 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (3 : ZMod 40903)^2406 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 401 := Nat.prime_eq_prime_of_dvd_pow hq prime_401 hd
          subst q
          change (3 : ZMod 40903)^102 ≠ 1
          reduce_mod_char
          decide

theorem prime_41051 : Nat.Prime 41051 := by
  apply lucas_primality 41051 (2 : ZMod 41051)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 41051 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((821 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 41051)^20525 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 41051)^8210 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 821 := Nat.prime_eq_prime_of_dvd_pow hq prime_821 hd
        subst q
        change (2 : ZMod 41051)^50 ≠ 1
        reduce_mod_char
        decide

theorem prime_41479 : Nat.Prime 41479 := by
  apply lucas_primality 41479 (3 : ZMod 41479)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 41479 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((31 : ℕ)^1 * ((223 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 41479)^20739 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 41479)^13826 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (3 : ZMod 41479)^1338 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 223 := Nat.prime_eq_prime_of_dvd_pow hq prime_223 hd
          subst q
          change (3 : ZMod 41479)^186 ≠ 1
          reduce_mod_char
          decide

theorem prime_41491 : Nat.Prime 41491 := by
  apply lucas_primality 41491 (13 : ZMod 41491)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 41491 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((461 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 41491)^20745 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 41491)^13830 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 41491)^8298 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 461 := Nat.prime_eq_prime_of_dvd_pow hq prime_461 hd
          subst q
          change (13 : ZMod 41491)^90 ≠ 1
          reduce_mod_char
          decide

theorem prime_41513 : Nat.Prime 41513 := by
  apply lucas_primality 41513 (3 : ZMod 41513)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 41513 - 1 = (2 : ℕ)^3 * ((5189 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 41513)^20756 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 5189 := Nat.prime_eq_prime_of_dvd_pow hq prime_5189 hd
      subst q
      change (3 : ZMod 41513)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_41687 : Nat.Prime 41687 := by
  apply lucas_primality 41687 (5 : ZMod 41687)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 41687 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((1097 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 41687)^20843 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (5 : ZMod 41687)^2194 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1097 := Nat.prime_eq_prime_of_dvd_pow hq prime_1097 hd
        subst q
        change (5 : ZMod 41687)^38 ≠ 1
        reduce_mod_char
        decide

theorem prime_41771 : Nat.Prime 41771 := by
  apply lucas_primality 41771 (2 : ZMod 41771)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 41771 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((4177 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 41771)^20885 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 41771)^8354 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4177 := Nat.prime_eq_prime_of_dvd_pow hq prime_4177 hd
        subst q
        change (2 : ZMod 41771)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_41893 : Nat.Prime 41893 := by
  apply lucas_primality 41893 (2 : ZMod 41893)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 41893 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((3491 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 41893)^20946 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 41893)^13964 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3491 := Nat.prime_eq_prime_of_dvd_pow hq prime_3491 hd
        subst q
        change (2 : ZMod 41893)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_42187 : Nat.Prime 42187 := by
  apply lucas_primality 42187 (13 : ZMod 42187)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 42187 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((79 : ℕ)^1 * ((89 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 42187)^21093 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 42187)^14062 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (13 : ZMod 42187)^534 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (13 : ZMod 42187)^474 ≠ 1
          reduce_mod_char
          decide

theorem prime_42299 : Nat.Prime 42299 := by
  apply lucas_primality 42299 (2 : ZMod 42299)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 42299 - 1 = (2 : ℕ)^1 * ((21149 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 42299)^21149 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 21149 := Nat.prime_eq_prime_of_dvd_pow hq prime_21149 hd
      subst q
      change (2 : ZMod 42299)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_42841 : Nat.Prime 42841 := by
  apply lucas_primality 42841 (23 : ZMod 42841)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 42841 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((17 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (23 : ZMod 42841)^21420 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (23 : ZMod 42841)^14280 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (23 : ZMod 42841)^8568 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (23 : ZMod 42841)^6120 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (23 : ZMod 42841)^2520 ≠ 1
            reduce_mod_char
            decide

theorem prime_42967 : Nat.Prime 42967 := by
  apply lucas_primality 42967 (3 : ZMod 42967)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 42967 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((31 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 42967)^21483 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 42967)^14322 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 42967)^6138 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (3 : ZMod 42967)^3906 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (3 : ZMod 42967)^1386 ≠ 1
            reduce_mod_char
            decide

theorem prime_42979 : Nat.Prime 42979 := by
  apply lucas_primality 42979 (3 : ZMod 42979)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 42979 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((19 : ℕ)^1 * ((29 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 42979)^21489 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 42979)^14326 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 42979)^3306 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (3 : ZMod 42979)^2262 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (3 : ZMod 42979)^1482 ≠ 1
            reduce_mod_char
            decide

theorem prime_43019 : Nat.Prime 43019 := by
  apply lucas_primality 43019 (2 : ZMod 43019)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 43019 - 1 = (2 : ℕ)^1 * ((137 : ℕ)^1 * ((157 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 43019)^21509 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
        subst q
        change (2 : ZMod 43019)^314 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
        subst q
        change (2 : ZMod 43019)^274 ≠ 1
        reduce_mod_char
        decide

theorem prime_43691 : Nat.Prime 43691 := by
  apply lucas_primality 43691 (6 : ZMod 43691)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 43691 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((257 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 43691)^21845 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 43691)^8738 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (6 : ZMod 43691)^2570 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 257 := Nat.prime_eq_prime_of_dvd_pow hq prime_257 hd
          subst q
          change (6 : ZMod 43691)^170 ≠ 1
          reduce_mod_char
          decide

theorem prime_43781 : Nat.Prime 43781 := by
  apply lucas_primality 43781 (2 : ZMod 43781)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 43781 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((199 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 43781)^21890 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 43781)^8756 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 43781)^3980 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 199 := Nat.prime_eq_prime_of_dvd_pow hq prime_199 hd
          subst q
          change (2 : ZMod 43781)^220 ≠ 1
          reduce_mod_char
          decide

theorem prime_43783 : Nat.Prime 43783 := by
  apply lucas_primality 43783 (3 : ZMod 43783)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 43783 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7297 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 43783)^21891 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 43783)^14594 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7297 := Nat.prime_eq_prime_of_dvd_pow hq prime_7297 hd
        subst q
        change (3 : ZMod 43783)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_44101 : Nat.Prime 44101 := by
  apply lucas_primality 44101 (6 : ZMod 44101)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 44101 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^2 * ((7 : ℕ)^2))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 44101)^22050 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 44101)^14700 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 44101)^8820 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 44101)^6300 ≠ 1
          reduce_mod_char
          decide

theorem prime_44111 : Nat.Prime 44111 := by
  apply lucas_primality 44111 (7 : ZMod 44111)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 44111 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((401 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 44111)^22055 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 44111)^8822 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (7 : ZMod 44111)^4010 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 401 := Nat.prime_eq_prime_of_dvd_pow hq prime_401 hd
          subst q
          change (7 : ZMod 44111)^110 ≠ 1
          reduce_mod_char
          decide

theorem prime_44203 : Nat.Prime 44203 := by
  apply lucas_primality 44203 (5 : ZMod 44203)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 44203 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((53 : ℕ)^1 * ((139 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 44203)^22101 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 44203)^14734 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (5 : ZMod 44203)^834 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
          subst q
          change (5 : ZMod 44203)^318 ≠ 1
          reduce_mod_char
          decide

theorem prime_44257 : Nat.Prime 44257 := by
  apply lucas_primality 44257 (5 : ZMod 44257)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 44257 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((461 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 44257)^22128 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 44257)^14752 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 461 := Nat.prime_eq_prime_of_dvd_pow hq prime_461 hd
        subst q
        change (5 : ZMod 44257)^96 ≠ 1
        reduce_mod_char
        decide

theorem prime_44263 : Nat.Prime 44263 := by
  apply lucas_primality 44263 (3 : ZMod 44263)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 44263 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((2459 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 44263)^22131 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 44263)^14754 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2459 := Nat.prime_eq_prime_of_dvd_pow hq prime_2459 hd
        subst q
        change (3 : ZMod 44263)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_44389 : Nat.Prime 44389 := by
  apply lucas_primality 44389 (2 : ZMod 44389)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 44389 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^4 * ((137 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 44389)^22194 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 44389)^14796 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
        subst q
        change (2 : ZMod 44389)^324 ≠ 1
        reduce_mod_char
        decide

theorem prime_44729 : Nat.Prime 44729 := by
  apply lucas_primality 44729 (3 : ZMod 44729)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 44729 - 1 = (2 : ℕ)^3 * ((5591 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 44729)^22364 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 5591 := Nat.prime_eq_prime_of_dvd_pow hq prime_5591 hd
      subst q
      change (3 : ZMod 44729)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_44773 : Nat.Prime 44773 := by
  apply lucas_primality 44773 (5 : ZMod 44773)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 44773 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((41 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 44773)^22386 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 44773)^14924 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 44773)^6396 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (5 : ZMod 44773)^3444 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (5 : ZMod 44773)^1092 ≠ 1
            reduce_mod_char
            decide

theorem prime_44851 : Nat.Prime 44851 := by
  apply lucas_primality 44851 (10 : ZMod 44851)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 44851 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((13 : ℕ)^1 * ((23 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 44851)^22425 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 44851)^14950 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 44851)^8970 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (10 : ZMod 44851)^3450 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (10 : ZMod 44851)^1950 ≠ 1
            reduce_mod_char
            decide

theorem prime_45281 : Nat.Prime 45281 := by
  apply lucas_primality 45281 (3 : ZMod 45281)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 45281 - 1 = (2 : ℕ)^5 * ((5 : ℕ)^1 * ((283 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 45281)^22640 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 45281)^9056 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 283 := Nat.prime_eq_prime_of_dvd_pow hq prime_283 hd
        subst q
        change (3 : ZMod 45281)^160 ≠ 1
        reduce_mod_char
        decide

theorem prime_45613 : Nat.Prime 45613 := by
  apply lucas_primality 45613 (2 : ZMod 45613)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 45613 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((181 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 45613)^22806 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 45613)^15204 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 45613)^6516 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 181 := Nat.prime_eq_prime_of_dvd_pow hq prime_181 hd
          subst q
          change (2 : ZMod 45613)^252 ≠ 1
          reduce_mod_char
          decide

theorem prime_45841 : Nat.Prime 45841 := by
  apply lucas_primality 45841 (7 : ZMod 45841)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 45841 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((191 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 45841)^22920 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 45841)^15280 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 45841)^9168 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
          subst q
          change (7 : ZMod 45841)^240 ≠ 1
          reduce_mod_char
          decide

theorem prime_45971 : Nat.Prime 45971 := by
  apply lucas_primality 45971 (2 : ZMod 45971)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 45971 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((4597 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 45971)^22985 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 45971)^9194 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4597 := Nat.prime_eq_prime_of_dvd_pow hq prime_4597 hd
        subst q
        change (2 : ZMod 45971)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_46153 : Nat.Prime 46153 := by
  apply lucas_primality 46153 (5 : ZMod 46153)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 46153 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((641 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 46153)^23076 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 46153)^15384 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 641 := Nat.prime_eq_prime_of_dvd_pow hq prime_641 hd
        subst q
        change (5 : ZMod 46153)^72 ≠ 1
        reduce_mod_char
        decide

end LegendreK6.Pratt
