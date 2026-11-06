import LegendreK6.Pratt.Block006

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LegendreK6.Pratt

theorem prime_46573 : Nat.Prime 46573 := by
  apply lucas_primality 46573 (2 : ZMod 46573)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 46573 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((3881 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 46573)^23286 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 46573)^15524 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3881 := Nat.prime_eq_prime_of_dvd_pow hq prime_3881 hd
        subst q
        change (2 : ZMod 46573)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_46663 : Nat.Prime 46663 := by
  apply lucas_primality 46663 (5 : ZMod 46663)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 46663 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((101 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 46663)^23331 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 46663)^15554 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 46663)^6666 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (5 : ZMod 46663)^4242 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
            subst q
            change (5 : ZMod 46663)^462 ≠ 1
            reduce_mod_char
            decide

theorem prime_47087 : Nat.Prime 47087 := by
  apply lucas_primality 47087 (5 : ZMod 47087)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 47087 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((1811 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 47087)^23543 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (5 : ZMod 47087)^3622 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1811 := Nat.prime_eq_prime_of_dvd_pow hq prime_1811 hd
        subst q
        change (5 : ZMod 47087)^26 ≠ 1
        reduce_mod_char
        decide

theorem prime_47149 : Nat.Prime 47149 := by
  apply lucas_primality 47149 (2 : ZMod 47149)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 47149 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((3929 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 47149)^23574 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 47149)^15716 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3929 := Nat.prime_eq_prime_of_dvd_pow hq prime_3929 hd
        subst q
        change (2 : ZMod 47149)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_47353 : Nat.Prime 47353 := by
  apply lucas_primality 47353 (5 : ZMod 47353)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 47353 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((1973 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 47353)^23676 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 47353)^15784 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1973 := Nat.prime_eq_prime_of_dvd_pow hq prime_1973 hd
        subst q
        change (5 : ZMod 47353)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_47441 : Nat.Prime 47441 := by
  apply lucas_primality 47441 (3 : ZMod 47441)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 47441 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((593 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 47441)^23720 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 47441)^9488 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 593 := Nat.prime_eq_prime_of_dvd_pow hq prime_593 hd
        subst q
        change (3 : ZMod 47441)^80 ≠ 1
        reduce_mod_char
        decide

theorem prime_47513 : Nat.Prime 47513 := by
  apply lucas_primality 47513 (3 : ZMod 47513)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 47513 - 1 = (2 : ℕ)^3 * ((5939 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 47513)^23756 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 5939 := Nat.prime_eq_prime_of_dvd_pow hq prime_5939 hd
      subst q
      change (3 : ZMod 47513)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_47713 : Nat.Prime 47713 := by
  apply lucas_primality 47713 (10 : ZMod 47713)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 47713 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((71 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 47713)^23856 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 47713)^15904 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (10 : ZMod 47713)^6816 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
          subst q
          change (10 : ZMod 47713)^672 ≠ 1
          reduce_mod_char
          decide

theorem prime_47807 : Nat.Prime 47807 := by
  apply lucas_primality 47807 (5 : ZMod 47807)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 47807 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((41 : ℕ)^1 * ((53 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 47807)^23903 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 47807)^4346 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (5 : ZMod 47807)^1166 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (5 : ZMod 47807)^902 ≠ 1
          reduce_mod_char
          decide

theorem prime_47939 : Nat.Prime 47939 := by
  apply lucas_primality 47939 (2 : ZMod 47939)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 47939 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((2179 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 47939)^23969 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 47939)^4358 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2179 := Nat.prime_eq_prime_of_dvd_pow hq prime_2179 hd
        subst q
        change (2 : ZMod 47939)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_48017 : Nat.Prime 48017 := by
  apply lucas_primality 48017 (3 : ZMod 48017)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 48017 - 1 = (2 : ℕ)^4 * ((3001 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 48017)^24008 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3001 := Nat.prime_eq_prime_of_dvd_pow hq prime_3001 hd
      subst q
      change (3 : ZMod 48017)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_48187 : Nat.Prime 48187 := by
  apply lucas_primality 48187 (2 : ZMod 48187)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 48187 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((2677 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 48187)^24093 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 48187)^16062 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2677 := Nat.prime_eq_prime_of_dvd_pow hq prime_2677 hd
        subst q
        change (2 : ZMod 48187)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_48221 : Nat.Prime 48221 := by
  apply lucas_primality 48221 (2 : ZMod 48221)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 48221 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((2411 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 48221)^24110 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 48221)^9644 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2411 := Nat.prime_eq_prime_of_dvd_pow hq prime_2411 hd
        subst q
        change (2 : ZMod 48221)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_48239 : Nat.Prime 48239 := by
  apply lucas_primality 48239 (7 : ZMod 48239)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 48239 - 1 = (2 : ℕ)^1 * ((89 : ℕ)^1 * ((271 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 48239)^24119 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
        subst q
        change (7 : ZMod 48239)^542 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 271 := Nat.prime_eq_prime_of_dvd_pow hq prime_271 hd
        subst q
        change (7 : ZMod 48239)^178 ≠ 1
        reduce_mod_char
        decide

theorem prime_48281 : Nat.Prime 48281 := by
  apply lucas_primality 48281 (3 : ZMod 48281)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 48281 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((71 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 48281)^24140 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 48281)^9656 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (3 : ZMod 48281)^2840 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
          subst q
          change (3 : ZMod 48281)^680 ≠ 1
          reduce_mod_char
          decide

theorem prime_48563 : Nat.Prime 48563 := by
  apply lucas_primality 48563 (2 : ZMod 48563)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 48563 - 1 = (2 : ℕ)^1 * ((24281 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 48563)^24281 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 24281 := Nat.prime_eq_prime_of_dvd_pow hq prime_24281 hd
      subst q
      change (2 : ZMod 48563)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_48593 : Nat.Prime 48593 := by
  apply lucas_primality 48593 (3 : ZMod 48593)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 48593 - 1 = (2 : ℕ)^4 * ((3037 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 48593)^24296 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3037 := Nat.prime_eq_prime_of_dvd_pow hq prime_3037 hd
      subst q
      change (3 : ZMod 48593)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_48817 : Nat.Prime 48817 := by
  apply lucas_primality 48817 (5 : ZMod 48817)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 48817 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^3 * ((113 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 48817)^24408 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 48817)^16272 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
        subst q
        change (5 : ZMod 48817)^432 ≠ 1
        reduce_mod_char
        decide

theorem prime_48889 : Nat.Prime 48889 := by
  apply lucas_primality 48889 (34 : ZMod 48889)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 48889 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((97 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (34 : ZMod 48889)^24444 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (34 : ZMod 48889)^16296 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (34 : ZMod 48889)^6984 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
          subst q
          change (34 : ZMod 48889)^504 ≠ 1
          reduce_mod_char
          decide

theorem prime_49171 : Nat.Prime 49171 := by
  apply lucas_primality 49171 (2 : ZMod 49171)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 49171 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((149 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 49171)^24585 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 49171)^16390 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 49171)^9834 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (2 : ZMod 49171)^4470 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
            subst q
            change (2 : ZMod 49171)^330 ≠ 1
            reduce_mod_char
            decide

theorem prime_49193 : Nat.Prime 49193 := by
  apply lucas_primality 49193 (3 : ZMod 49193)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 49193 - 1 = (2 : ℕ)^3 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((43 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 49193)^24596 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 49193)^4472 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 49193)^3784 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (3 : ZMod 49193)^1144 ≠ 1
          reduce_mod_char
          decide

theorem prime_49201 : Nat.Prime 49201 := by
  apply lucas_primality 49201 (7 : ZMod 49201)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 49201 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((41 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 49201)^24600 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 49201)^16400 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 49201)^9840 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (7 : ZMod 49201)^1200 ≠ 1
          reduce_mod_char
          decide

theorem prime_49279 : Nat.Prime 49279 := by
  apply lucas_primality 49279 (3 : ZMod 49279)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 49279 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((43 : ℕ)^1 * ((191 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 49279)^24639 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 49279)^16426 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (3 : ZMod 49279)^1146 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
          subst q
          change (3 : ZMod 49279)^258 ≠ 1
          reduce_mod_char
          decide

theorem prime_49639 : Nat.Prime 49639 := by
  apply lucas_primality 49639 (3 : ZMod 49639)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 49639 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((8273 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 49639)^24819 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 49639)^16546 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 8273 := Nat.prime_eq_prime_of_dvd_pow hq prime_8273 hd
        subst q
        change (3 : ZMod 49639)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_49919 : Nat.Prime 49919 := by
  apply lucas_primality 49919 (7 : ZMod 49919)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 49919 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((2269 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 49919)^24959 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (7 : ZMod 49919)^4538 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2269 := Nat.prime_eq_prime_of_dvd_pow hq prime_2269 hd
        subst q
        change (7 : ZMod 49919)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_50023 : Nat.Prime 50023 := by
  apply lucas_primality 50023 (3 : ZMod 50023)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 50023 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((397 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 50023)^25011 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 50023)^16674 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 50023)^7146 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 397 := Nat.prime_eq_prime_of_dvd_pow hq prime_397 hd
          subst q
          change (3 : ZMod 50023)^126 ≠ 1
          reduce_mod_char
          decide

theorem prime_50147 : Nat.Prime 50147 := by
  apply lucas_primality 50147 (2 : ZMod 50147)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 50147 - 1 = (2 : ℕ)^1 * ((25073 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 50147)^25073 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 25073 := Nat.prime_eq_prime_of_dvd_pow hq prime_25073 hd
      subst q
      change (2 : ZMod 50147)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_50377 : Nat.Prime 50377 := by
  apply lucas_primality 50377 (5 : ZMod 50377)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 50377 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((2099 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 50377)^25188 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 50377)^16792 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2099 := Nat.prime_eq_prime_of_dvd_pow hq prime_2099 hd
        subst q
        change (5 : ZMod 50377)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_50383 : Nat.Prime 50383 := by
  apply lucas_primality 50383 (3 : ZMod 50383)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 50383 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((311 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 50383)^25191 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 50383)^16794 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 311 := Nat.prime_eq_prime_of_dvd_pow hq prime_311 hd
        subst q
        change (3 : ZMod 50383)^162 ≠ 1
        reduce_mod_char
        decide

theorem prime_50497 : Nat.Prime 50497 := by
  apply lucas_primality 50497 (5 : ZMod 50497)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 50497 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^1 * ((263 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 50497)^25248 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 50497)^16832 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 263 := Nat.prime_eq_prime_of_dvd_pow hq prime_263 hd
        subst q
        change (5 : ZMod 50497)^192 ≠ 1
        reduce_mod_char
        decide

theorem prime_50593 : Nat.Prime 50593 := by
  apply lucas_primality 50593 (5 : ZMod 50593)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 50593 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((31 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 50593)^25296 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 50593)^16864 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (5 : ZMod 50593)^2976 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (5 : ZMod 50593)^1632 ≠ 1
          reduce_mod_char
          decide

theorem prime_50599 : Nat.Prime 50599 := by
  apply lucas_primality 50599 (3 : ZMod 50599)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 50599 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((937 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 50599)^25299 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 50599)^16866 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 937 := Nat.prime_eq_prime_of_dvd_pow hq prime_937 hd
        subst q
        change (3 : ZMod 50599)^54 ≠ 1
        reduce_mod_char
        decide

theorem prime_50627 : Nat.Prime 50627 := by
  apply lucas_primality 50627 (2 : ZMod 50627)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 50627 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((1489 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 50627)^25313 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 50627)^2978 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1489 := Nat.prime_eq_prime_of_dvd_pow hq prime_1489 hd
        subst q
        change (2 : ZMod 50627)^34 ≠ 1
        reduce_mod_char
        decide

theorem prime_50647 : Nat.Prime 50647 := by
  apply lucas_primality 50647 (3 : ZMod 50647)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 50647 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((367 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 50647)^25323 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 50647)^16882 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (3 : ZMod 50647)^2202 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 367 := Nat.prime_eq_prime_of_dvd_pow hq prime_367 hd
          subst q
          change (3 : ZMod 50647)^138 ≠ 1
          reduce_mod_char
          decide

theorem prime_50671 : Nat.Prime 50671 := by
  apply lucas_primality 50671 (11 : ZMod 50671)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 50671 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((563 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 50671)^25335 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 50671)^16890 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 50671)^10134 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 563 := Nat.prime_eq_prime_of_dvd_pow hq prime_563 hd
          subst q
          change (11 : ZMod 50671)^90 ≠ 1
          reduce_mod_char
          decide

theorem prime_50773 : Nat.Prime 50773 := by
  apply lucas_primality 50773 (11 : ZMod 50773)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 50773 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((4231 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 50773)^25386 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 50773)^16924 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4231 := Nat.prime_eq_prime_of_dvd_pow hq prime_4231 hd
        subst q
        change (11 : ZMod 50773)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_51001 : Nat.Prime 51001 := by
  apply lucas_primality 51001 (7 : ZMod 51001)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 51001 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^3 * ((17 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 51001)^25500 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 51001)^17000 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 51001)^10200 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (7 : ZMod 51001)^3000 ≠ 1
          reduce_mod_char
          decide

theorem prime_51109 : Nat.Prime 51109 := by
  apply lucas_primality 51109 (10 : ZMod 51109)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 51109 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((4259 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 51109)^25554 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 51109)^17036 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4259 := Nat.prime_eq_prime_of_dvd_pow hq prime_4259 hd
        subst q
        change (10 : ZMod 51109)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_51151 : Nat.Prime 51151 := by
  apply lucas_primality 51151 (3 : ZMod 51151)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 51151 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((11 : ℕ)^1 * ((31 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 51151)^25575 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 51151)^17050 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 51151)^10230 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (3 : ZMod 51151)^4650 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (3 : ZMod 51151)^1650 ≠ 1
            reduce_mod_char
            decide

theorem prime_51343 : Nat.Prime 51343 := by
  apply lucas_primality 51343 (5 : ZMod 51343)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 51343 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((43 : ℕ)^1 * ((199 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 51343)^25671 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 51343)^17114 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (5 : ZMod 51343)^1194 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 199 := Nat.prime_eq_prime_of_dvd_pow hq prime_199 hd
          subst q
          change (5 : ZMod 51343)^258 ≠ 1
          reduce_mod_char
          decide

theorem prime_51437 : Nat.Prime 51437 := by
  apply lucas_primality 51437 (2 : ZMod 51437)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 51437 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((167 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 51437)^25718 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 51437)^7348 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 51437)^4676 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
          subst q
          change (2 : ZMod 51437)^308 ≠ 1
          reduce_mod_char
          decide

theorem prime_51473 : Nat.Prime 51473 := by
  apply lucas_primality 51473 (3 : ZMod 51473)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 51473 - 1 = (2 : ℕ)^4 * ((3217 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 51473)^25736 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3217 := Nat.prime_eq_prime_of_dvd_pow hq prime_3217 hd
      subst q
      change (3 : ZMod 51473)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_51479 : Nat.Prime 51479 := by
  apply lucas_primality 51479 (7 : ZMod 51479)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 51479 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((3677 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 51479)^25739 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 51479)^7354 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3677 := Nat.prime_eq_prime_of_dvd_pow hq prime_3677 hd
        subst q
        change (7 : ZMod 51479)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_51487 : Nat.Prime 51487 := by
  apply lucas_primality 51487 (3 : ZMod 51487)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 51487 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((8581 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 51487)^25743 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 51487)^17162 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 8581 := Nat.prime_eq_prime_of_dvd_pow hq prime_8581 hd
        subst q
        change (3 : ZMod 51487)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_51749 : Nat.Prime 51749 := by
  apply lucas_primality 51749 (2 : ZMod 51749)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 51749 - 1 = (2 : ℕ)^2 * ((17 : ℕ)^1 * ((761 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 51749)^25874 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 51749)^3044 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 761 := Nat.prime_eq_prime_of_dvd_pow hq prime_761 hd
        subst q
        change (2 : ZMod 51749)^68 ≠ 1
        reduce_mod_char
        decide

theorem prime_52189 : Nat.Prime 52189 := by
  apply lucas_primality 52189 (13 : ZMod 52189)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 52189 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((4349 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 52189)^26094 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 52189)^17396 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4349 := Nat.prime_eq_prime_of_dvd_pow hq prime_4349 hd
        subst q
        change (13 : ZMod 52189)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_52223 : Nat.Prime 52223 := by
  apply lucas_primality 52223 (5 : ZMod 52223)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 52223 - 1 = (2 : ℕ)^1 * ((26111 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 52223)^26111 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 26111 := Nat.prime_eq_prime_of_dvd_pow hq prime_26111 hd
      subst q
      change (5 : ZMod 52223)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_52361 : Nat.Prime 52361 := by
  apply lucas_primality 52361 (6 : ZMod 52361)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 52361 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((17 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 52361)^26180 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 52361)^10472 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 52361)^7480 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (6 : ZMod 52361)^4760 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (6 : ZMod 52361)^3080 ≠ 1
            reduce_mod_char
            decide

theorem prime_52691 : Nat.Prime 52691 := by
  apply lucas_primality 52691 (2 : ZMod 52691)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 52691 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((479 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 52691)^26345 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 52691)^10538 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 52691)^4790 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 479 := Nat.prime_eq_prime_of_dvd_pow hq prime_479 hd
          subst q
          change (2 : ZMod 52691)^110 ≠ 1
          reduce_mod_char
          decide

theorem prime_52697 : Nat.Prime 52697 := by
  apply lucas_primality 52697 (3 : ZMod 52697)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 52697 - 1 = (2 : ℕ)^3 * ((7 : ℕ)^1 * ((941 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 52697)^26348 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 52697)^7528 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 941 := Nat.prime_eq_prime_of_dvd_pow hq prime_941 hd
        subst q
        change (3 : ZMod 52697)^56 ≠ 1
        reduce_mod_char
        decide

theorem prime_53149 : Nat.Prime 53149 := by
  apply lucas_primality 53149 (6 : ZMod 53149)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 53149 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((43 : ℕ)^1 * ((103 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 53149)^26574 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 53149)^17716 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (6 : ZMod 53149)^1236 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
          subst q
          change (6 : ZMod 53149)^516 ≠ 1
          reduce_mod_char
          decide

theorem prime_53267 : Nat.Prime 53267 := by
  apply lucas_primality 53267 (2 : ZMod 53267)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 53267 - 1 = (2 : ℕ)^1 * ((26633 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 53267)^26633 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 26633 := Nat.prime_eq_prime_of_dvd_pow hq prime_26633 hd
      subst q
      change (2 : ZMod 53267)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_53353 : Nat.Prime 53353 := by
  apply lucas_primality 53353 (7 : ZMod 53353)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 53353 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((13 : ℕ)^1 * ((19 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 53353)^26676 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 53353)^17784 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (7 : ZMod 53353)^4104 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (7 : ZMod 53353)^2808 ≠ 1
          reduce_mod_char
          decide

theorem prime_53407 : Nat.Prime 53407 := by
  apply lucas_primality 53407 (5 : ZMod 53407)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 53407 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((23 : ℕ)^1 * ((43 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 53407)^26703 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 53407)^17802 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (5 : ZMod 53407)^2322 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (5 : ZMod 53407)^1242 ≠ 1
          reduce_mod_char
          decide

theorem prime_53453 : Nat.Prime 53453 := by
  apply lucas_primality 53453 (2 : ZMod 53453)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 53453 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((23 : ℕ)^1 * ((83 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 53453)^26726 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 53453)^7636 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 53453)^2324 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
          subst q
          change (2 : ZMod 53453)^644 ≠ 1
          reduce_mod_char
          decide

theorem prime_53639 : Nat.Prime 53639 := by
  apply lucas_primality 53639 (11 : ZMod 53639)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 53639 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((2063 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 53639)^26819 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (11 : ZMod 53639)^4126 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2063 := Nat.prime_eq_prime_of_dvd_pow hq prime_2063 hd
        subst q
        change (11 : ZMod 53639)^26 ≠ 1
        reduce_mod_char
        decide

theorem prime_53681 : Nat.Prime 53681 := by
  apply lucas_primality 53681 (3 : ZMod 53681)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 53681 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((61 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 53681)^26840 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 53681)^10736 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 53681)^4880 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (3 : ZMod 53681)^880 ≠ 1
          reduce_mod_char
          decide

theorem prime_54133 : Nat.Prime 54133 := by
  apply lucas_primality 54133 (5 : ZMod 54133)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 54133 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((347 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 54133)^27066 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 54133)^18044 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (5 : ZMod 54133)^4164 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 347 := Nat.prime_eq_prime_of_dvd_pow hq prime_347 hd
          subst q
          change (5 : ZMod 54133)^156 ≠ 1
          reduce_mod_char
          decide

theorem prime_54377 : Nat.Prime 54377 := by
  apply lucas_primality 54377 (5 : ZMod 54377)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 54377 - 1 = (2 : ℕ)^3 * ((7 : ℕ)^1 * ((971 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 54377)^27188 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 54377)^7768 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 971 := Nat.prime_eq_prime_of_dvd_pow hq prime_971 hd
        subst q
        change (5 : ZMod 54377)^56 ≠ 1
        reduce_mod_char
        decide

theorem prime_54517 : Nat.Prime 54517 := by
  apply lucas_primality 54517 (5 : ZMod 54517)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 54517 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((59 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 54517)^27258 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 54517)^18172 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 54517)^7788 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (5 : ZMod 54517)^4956 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
            subst q
            change (5 : ZMod 54517)^924 ≠ 1
            reduce_mod_char
            decide

theorem prime_54601 : Nat.Prime 54601 := by
  apply lucas_primality 54601 (22 : ZMod 54601)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 54601 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((7 : ℕ)^1 * ((13 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (22 : ZMod 54601)^27300 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (22 : ZMod 54601)^18200 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (22 : ZMod 54601)^10920 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (22 : ZMod 54601)^7800 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (22 : ZMod 54601)^4200 ≠ 1
            reduce_mod_char
            decide

theorem prime_54881 : Nat.Prime 54881 := by
  apply lucas_primality 54881 (3 : ZMod 54881)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 54881 - 1 = (2 : ℕ)^5 * ((5 : ℕ)^1 * ((7 : ℕ)^3)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 54881)^27440 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 54881)^10976 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 54881)^7840 ≠ 1
        reduce_mod_char
        decide

theorem prime_55339 : Nat.Prime 55339 := by
  apply lucas_primality 55339 (2 : ZMod 55339)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 55339 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((401 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 55339)^27669 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 55339)^18446 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 55339)^2406 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 401 := Nat.prime_eq_prime_of_dvd_pow hq prime_401 hd
          subst q
          change (2 : ZMod 55339)^138 ≠ 1
          reduce_mod_char
          decide

theorem prime_55411 : Nat.Prime 55411 := by
  apply lucas_primality 55411 (2 : ZMod 55411)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 55411 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((1847 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 55411)^27705 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 55411)^18470 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 55411)^11082 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1847 := Nat.prime_eq_prime_of_dvd_pow hq prime_1847 hd
          subst q
          change (2 : ZMod 55411)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_55721 : Nat.Prime 55721 := by
  apply lucas_primality 55721 (3 : ZMod 55721)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 55721 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((199 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 55721)^27860 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 55721)^11144 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 55721)^7960 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 199 := Nat.prime_eq_prime_of_dvd_pow hq prime_199 hd
          subst q
          change (3 : ZMod 55721)^280 ≠ 1
          reduce_mod_char
          decide

theorem prime_55837 : Nat.Prime 55837 := by
  apply lucas_primality 55837 (5 : ZMod 55837)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 55837 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((11 : ℕ)^1 * ((47 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 55837)^27918 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 55837)^18612 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 55837)^5076 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (5 : ZMod 55837)^1188 ≠ 1
          reduce_mod_char
          decide

theorem prime_56087 : Nat.Prime 56087 := by
  apply lucas_primality 56087 (5 : ZMod 56087)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 56087 - 1 = (2 : ℕ)^1 * ((29 : ℕ)^1 * ((967 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 56087)^28043 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (5 : ZMod 56087)^1934 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 967 := Nat.prime_eq_prime_of_dvd_pow hq prime_967 hd
        subst q
        change (5 : ZMod 56087)^58 ≠ 1
        reduce_mod_char
        decide

theorem prime_56171 : Nat.Prime 56171 := by
  apply lucas_primality 56171 (2 : ZMod 56171)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 56171 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((41 : ℕ)^1 * ((137 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 56171)^28085 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 56171)^11234 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (2 : ZMod 56171)^1370 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
          subst q
          change (2 : ZMod 56171)^410 ≠ 1
          reduce_mod_char
          decide

theorem prime_56209 : Nat.Prime 56209 := by
  apply lucas_primality 56209 (7 : ZMod 56209)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 56209 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((1171 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 56209)^28104 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 56209)^18736 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1171 := Nat.prime_eq_prime_of_dvd_pow hq prime_1171 hd
        subst q
        change (7 : ZMod 56209)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_56473 : Nat.Prime 56473 := by
  apply lucas_primality 56473 (5 : ZMod 56473)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 56473 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((181 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 56473)^28236 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 56473)^18824 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (5 : ZMod 56473)^4344 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 181 := Nat.prime_eq_prime_of_dvd_pow hq prime_181 hd
          subst q
          change (5 : ZMod 56473)^312 ≠ 1
          reduce_mod_char
          decide

theorem prime_56687 : Nat.Prime 56687 := by
  apply lucas_primality 56687 (5 : ZMod 56687)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 56687 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((4049 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 56687)^28343 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 56687)^8098 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4049 := Nat.prime_eq_prime_of_dvd_pow hq prime_4049 hd
        subst q
        change (5 : ZMod 56687)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_56821 : Nat.Prime 56821 := by
  apply lucas_primality 56821 (6 : ZMod 56821)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 56821 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((947 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 56821)^28410 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 56821)^18940 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 56821)^11364 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 947 := Nat.prime_eq_prime_of_dvd_pow hq prime_947 hd
          subst q
          change (6 : ZMod 56821)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_56999 : Nat.Prime 56999 := by
  apply lucas_primality 56999 (13 : ZMod 56999)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 56999 - 1 = (2 : ℕ)^1 * ((28499 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 56999)^28499 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 28499 := Nat.prime_eq_prime_of_dvd_pow hq prime_28499 hd
      subst q
      change (13 : ZMod 56999)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_57037 : Nat.Prime 57037 := by
  apply lucas_primality 57037 (5 : ZMod 57037)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 57037 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((97 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 57037)^28518 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 57037)^19012 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 57037)^8148 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
          subst q
          change (5 : ZMod 57037)^588 ≠ 1
          reduce_mod_char
          decide

theorem prime_57223 : Nat.Prime 57223 := by
  apply lucas_primality 57223 (3 : ZMod 57223)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 57223 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((17 : ℕ)^2))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 57223)^28611 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 57223)^19074 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 57223)^5202 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (3 : ZMod 57223)^3366 ≠ 1
          reduce_mod_char
          decide

theorem prime_57349 : Nat.Prime 57349 := by
  apply lucas_primality 57349 (2 : ZMod 57349)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 57349 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^5 * ((59 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 57349)^28674 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 57349)^19116 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
        subst q
        change (2 : ZMod 57349)^972 ≠ 1
        reduce_mod_char
        decide

theorem prime_57467 : Nat.Prime 57467 := by
  apply lucas_primality 57467 (2 : ZMod 57467)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 57467 - 1 = (2 : ℕ)^1 * ((59 : ℕ)^1 * ((487 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 57467)^28733 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
        subst q
        change (2 : ZMod 57467)^974 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 487 := Nat.prime_eq_prime_of_dvd_pow hq prime_487 hd
        subst q
        change (2 : ZMod 57467)^118 ≠ 1
        reduce_mod_char
        decide

theorem prime_57587 : Nat.Prime 57587 := by
  apply lucas_primality 57587 (2 : ZMod 57587)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 57587 - 1 = (2 : ℕ)^1 * ((28793 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 57587)^28793 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 28793 := Nat.prime_eq_prime_of_dvd_pow hq prime_28793 hd
      subst q
      change (2 : ZMod 57587)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_57737 : Nat.Prime 57737 := by
  apply lucas_primality 57737 (3 : ZMod 57737)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 57737 - 1 = (2 : ℕ)^3 * ((7 : ℕ)^1 * ((1031 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 57737)^28868 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 57737)^8248 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1031 := Nat.prime_eq_prime_of_dvd_pow hq prime_1031 hd
        subst q
        change (3 : ZMod 57737)^56 ≠ 1
        reduce_mod_char
        decide

theorem prime_57881 : Nat.Prime 57881 := by
  apply lucas_primality 57881 (3 : ZMod 57881)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 57881 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((1447 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 57881)^28940 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 57881)^11576 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1447 := Nat.prime_eq_prime_of_dvd_pow hq prime_1447 hd
        subst q
        change (3 : ZMod 57881)^40 ≠ 1
        reduce_mod_char
        decide

theorem prime_57991 : Nat.Prime 57991 := by
  apply lucas_primality 57991 (6 : ZMod 57991)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 57991 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((1933 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 57991)^28995 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 57991)^19330 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 57991)^11598 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1933 := Nat.prime_eq_prime_of_dvd_pow hq prime_1933 hd
          subst q
          change (6 : ZMod 57991)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_58603 : Nat.Prime 58603 := by
  apply lucas_primality 58603 (2 : ZMod 58603)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 58603 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((9767 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 58603)^29301 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 58603)^19534 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 9767 := Nat.prime_eq_prime_of_dvd_pow hq prime_9767 hd
        subst q
        change (2 : ZMod 58603)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_58687 : Nat.Prime 58687 := by
  apply lucas_primality 58687 (6 : ZMod 58687)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 58687 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((9781 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 58687)^29343 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 58687)^19562 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 9781 := Nat.prime_eq_prime_of_dvd_pow hq prime_9781 hd
        subst q
        change (6 : ZMod 58687)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_58771 : Nat.Prime 58771 := by
  apply lucas_primality 58771 (11 : ZMod 58771)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 58771 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((653 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 58771)^29385 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 58771)^19590 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 58771)^11754 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 653 := Nat.prime_eq_prime_of_dvd_pow hq prime_653 hd
          subst q
          change (11 : ZMod 58771)^90 ≠ 1
          reduce_mod_char
          decide

theorem prime_58901 : Nat.Prime 58901 := by
  apply lucas_primality 58901 (2 : ZMod 58901)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 58901 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((19 : ℕ)^1 * ((31 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 58901)^29450 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 58901)^11780 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 58901)^3100 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (2 : ZMod 58901)^1900 ≠ 1
          reduce_mod_char
          decide

theorem prime_59119 : Nat.Prime 59119 := by
  apply lucas_primality 59119 (3 : ZMod 59119)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 59119 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((59 : ℕ)^1 * ((167 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 59119)^29559 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 59119)^19706 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (3 : ZMod 59119)^1002 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
          subst q
          change (3 : ZMod 59119)^354 ≠ 1
          reduce_mod_char
          decide

theorem prime_59167 : Nat.Prime 59167 := by
  apply lucas_primality 59167 (3 : ZMod 59167)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 59167 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((19 : ℕ)^1 * ((173 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 59167)^29583 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 59167)^19722 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (3 : ZMod 59167)^3114 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
          subst q
          change (3 : ZMod 59167)^342 ≠ 1
          reduce_mod_char
          decide

theorem prime_59341 : Nat.Prime 59341 := by
  apply lucas_primality 59341 (14 : ZMod 59341)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 59341 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((23 : ℕ)^1 * ((43 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 59341)^29670 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 59341)^19780 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (14 : ZMod 59341)^11868 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (14 : ZMod 59341)^2580 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (14 : ZMod 59341)^1380 ≠ 1
            reduce_mod_char
            decide

theorem prime_60259 : Nat.Prime 60259 := by
  apply lucas_primality 60259 (3 : ZMod 60259)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 60259 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^2 * ((83 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 60259)^30129 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 60259)^20086 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 60259)^5478 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
          subst q
          change (3 : ZMod 60259)^726 ≠ 1
          reduce_mod_char
          decide

theorem prime_60343 : Nat.Prime 60343 := by
  apply lucas_primality 60343 (3 : ZMod 60343)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 60343 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((89 : ℕ)^1 * ((113 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 60343)^30171 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 60343)^20114 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (3 : ZMod 60343)^678 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
          subst q
          change (3 : ZMod 60343)^534 ≠ 1
          reduce_mod_char
          decide

theorem prime_60611 : Nat.Prime 60611 := by
  apply lucas_primality 60611 (10 : ZMod 60611)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 60611 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((19 : ℕ)^1 * ((29 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 60611)^30305 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (10 : ZMod 60611)^12122 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (10 : ZMod 60611)^5510 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (10 : ZMod 60611)^3190 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (10 : ZMod 60611)^2090 ≠ 1
            reduce_mod_char
            decide

theorem prime_60647 : Nat.Prime 60647 := by
  apply lucas_primality 60647 (5 : ZMod 60647)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 60647 - 1 = (2 : ℕ)^1 * ((30323 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 60647)^30323 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 30323 := Nat.prime_eq_prime_of_dvd_pow hq prime_30323 hd
      subst q
      change (5 : ZMod 60647)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_60727 : Nat.Prime 60727 := by
  apply lucas_primality 60727 (5 : ZMod 60727)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 60727 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((29 : ℕ)^1 * ((349 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 60727)^30363 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 60727)^20242 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (5 : ZMod 60727)^2094 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 349 := Nat.prime_eq_prime_of_dvd_pow hq prime_349 hd
          subst q
          change (5 : ZMod 60727)^174 ≠ 1
          reduce_mod_char
          decide

theorem prime_60761 : Nat.Prime 60761 := by
  apply lucas_primality 60761 (6 : ZMod 60761)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 60761 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((7 : ℕ)^2 * ((31 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 60761)^30380 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 60761)^12152 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 60761)^8680 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (6 : ZMod 60761)^1960 ≠ 1
          reduce_mod_char
          decide

theorem prime_60919 : Nat.Prime 60919 := by
  apply lucas_primality 60919 (3 : ZMod 60919)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 60919 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((71 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 60919)^30459 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 60919)^20306 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 60919)^5538 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (3 : ZMod 60919)^4686 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
            subst q
            change (3 : ZMod 60919)^858 ≠ 1
            reduce_mod_char
            decide

theorem prime_61121 : Nat.Prime 61121 := by
  apply lucas_primality 61121 (3 : ZMod 61121)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 61121 - 1 = (2 : ℕ)^6 * ((5 : ℕ)^1 * ((191 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 61121)^30560 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 61121)^12224 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
        subst q
        change (3 : ZMod 61121)^320 ≠ 1
        reduce_mod_char
        decide

theorem prime_61253 : Nat.Prime 61253 := by
  apply lucas_primality 61253 (2 : ZMod 61253)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 61253 - 1 = (2 : ℕ)^2 * ((15313 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 61253)^30626 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 15313 := Nat.prime_eq_prime_of_dvd_pow hq prime_15313 hd
      subst q
      change (2 : ZMod 61253)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_61837 : Nat.Prime 61837 := by
  apply lucas_primality 61837 (6 : ZMod 61837)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 61837 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5153 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 61837)^30918 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 61837)^20612 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5153 := Nat.prime_eq_prime_of_dvd_pow hq prime_5153 hd
        subst q
        change (6 : ZMod 61837)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_62081 : Nat.Prime 62081 := by
  apply lucas_primality 62081 (6 : ZMod 62081)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 62081 - 1 = (2 : ℕ)^7 * ((5 : ℕ)^1 * ((97 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 62081)^31040 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 62081)^12416 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
        subst q
        change (6 : ZMod 62081)^640 ≠ 1
        reduce_mod_char
        decide

theorem prime_62131 : Nat.Prime 62131 := by
  apply lucas_primality 62131 (2 : ZMod 62131)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 62131 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((19 : ℕ)^1 * ((109 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 62131)^31065 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 62131)^20710 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 62131)^12426 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (2 : ZMod 62131)^3270 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
            subst q
            change (2 : ZMod 62131)^570 ≠ 1
            reduce_mod_char
            decide

theorem prime_62213 : Nat.Prime 62213 := by
  apply lucas_primality 62213 (2 : ZMod 62213)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 62213 - 1 = (2 : ℕ)^2 * ((103 : ℕ)^1 * ((151 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 62213)^31106 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
        subst q
        change (2 : ZMod 62213)^604 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
        subst q
        change (2 : ZMod 62213)^412 ≠ 1
        reduce_mod_char
        decide

theorem prime_62233 : Nat.Prime 62233 := by
  apply lucas_primality 62233 (7 : ZMod 62233)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 62233 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((2593 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 62233)^31116 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 62233)^20744 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2593 := Nat.prime_eq_prime_of_dvd_pow hq prime_2593 hd
        subst q
        change (7 : ZMod 62233)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_62401 : Nat.Prime 62401 := by
  apply lucas_primality 62401 (17 : ZMod 62401)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 62401 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((13 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 62401)^31200 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 62401)^20800 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (17 : ZMod 62401)^12480 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (17 : ZMod 62401)^4800 ≠ 1
          reduce_mod_char
          decide

theorem prime_62533 : Nat.Prime 62533 := by
  apply lucas_primality 62533 (2 : ZMod 62533)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 62533 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^4 * ((193 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 62533)^31266 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 62533)^20844 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
        subst q
        change (2 : ZMod 62533)^324 ≠ 1
        reduce_mod_char
        decide

theorem prime_62549 : Nat.Prime 62549 := by
  apply lucas_primality 62549 (2 : ZMod 62549)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 62549 - 1 = (2 : ℕ)^2 * ((19 : ℕ)^1 * ((823 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 62549)^31274 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 62549)^3292 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 823 := Nat.prime_eq_prime_of_dvd_pow hq prime_823 hd
        subst q
        change (2 : ZMod 62549)^76 ≠ 1
        reduce_mod_char
        decide

theorem prime_62819 : Nat.Prime 62819 := by
  apply lucas_primality 62819 (2 : ZMod 62819)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 62819 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^2 * ((641 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 62819)^31409 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 62819)^8974 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 641 := Nat.prime_eq_prime_of_dvd_pow hq prime_641 hd
        subst q
        change (2 : ZMod 62819)^98 ≠ 1
        reduce_mod_char
        decide

theorem prime_62929 : Nat.Prime 62929 := by
  apply lucas_primality 62929 (14 : ZMod 62929)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 62929 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((19 : ℕ)^1 * ((23 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 62929)^31464 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 62929)^20976 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (14 : ZMod 62929)^3312 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (14 : ZMod 62929)^2736 ≠ 1
          reduce_mod_char
          decide

theorem prime_63131 : Nat.Prime 63131 := by
  apply lucas_primality 63131 (2 : ZMod 63131)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 63131 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((59 : ℕ)^1 * ((107 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 63131)^31565 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 63131)^12626 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (2 : ZMod 63131)^1070 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
          subst q
          change (2 : ZMod 63131)^590 ≠ 1
          reduce_mod_char
          decide

theorem prime_63299 : Nat.Prime 63299 := by
  apply lucas_primality 63299 (2 : ZMod 63299)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 63299 - 1 = (2 : ℕ)^1 * ((31649 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 63299)^31649 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 31649 := Nat.prime_eq_prime_of_dvd_pow hq prime_31649 hd
      subst q
      change (2 : ZMod 63299)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_63577 : Nat.Prime 63577 := by
  apply lucas_primality 63577 (5 : ZMod 63577)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 63577 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((883 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 63577)^31788 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 63577)^21192 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 883 := Nat.prime_eq_prime_of_dvd_pow hq prime_883 hd
        subst q
        change (5 : ZMod 63577)^72 ≠ 1
        reduce_mod_char
        decide

theorem prime_63601 : Nat.Prime 63601 := by
  apply lucas_primality 63601 (7 : ZMod 63601)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 63601 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((53 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 63601)^31800 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 63601)^21200 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 63601)^12720 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (7 : ZMod 63601)^1200 ≠ 1
          reduce_mod_char
          decide

theorem prime_63611 : Nat.Prime 63611 := by
  apply lucas_primality 63611 (2 : ZMod 63611)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 63611 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((6361 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 63611)^31805 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 63611)^12722 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 6361 := Nat.prime_eq_prime_of_dvd_pow hq prime_6361 hd
        subst q
        change (2 : ZMod 63611)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_63667 : Nat.Prime 63667 := by
  apply lucas_primality 63667 (2 : ZMod 63667)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 63667 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^5 * ((131 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 63667)^31833 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 63667)^21222 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
        subst q
        change (2 : ZMod 63667)^486 ≠ 1
        reduce_mod_char
        decide

theorem prime_63781 : Nat.Prime 63781 := by
  apply lucas_primality 63781 (2 : ZMod 63781)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 63781 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((1063 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 63781)^31890 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 63781)^21260 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 63781)^12756 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1063 := Nat.prime_eq_prime_of_dvd_pow hq prime_1063 hd
          subst q
          change (2 : ZMod 63781)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_64189 : Nat.Prime 64189 := by
  apply lucas_primality 64189 (2 : ZMod 64189)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 64189 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((1783 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 64189)^32094 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 64189)^21396 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1783 := Nat.prime_eq_prime_of_dvd_pow hq prime_1783 hd
        subst q
        change (2 : ZMod 64189)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_64373 : Nat.Prime 64373 := by
  apply lucas_primality 64373 (2 : ZMod 64373)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 64373 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((11 : ℕ)^2 * ((19 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 64373)^32186 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 64373)^9196 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 64373)^5852 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 64373)^3388 ≠ 1
          reduce_mod_char
          decide

theorem prime_64621 : Nat.Prime 64621 := by
  apply lucas_primality 64621 (6 : ZMod 64621)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 64621 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((359 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 64621)^32310 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 64621)^21540 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 64621)^12924 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 359 := Nat.prime_eq_prime_of_dvd_pow hq prime_359 hd
          subst q
          change (6 : ZMod 64621)^180 ≠ 1
          reduce_mod_char
          decide

theorem prime_64679 : Nat.Prime 64679 := by
  apply lucas_primality 64679 (17 : ZMod 64679)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 64679 - 1 = (2 : ℕ)^1 * ((73 : ℕ)^1 * ((443 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 64679)^32339 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
        subst q
        change (17 : ZMod 64679)^886 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 443 := Nat.prime_eq_prime_of_dvd_pow hq prime_443 hd
        subst q
        change (17 : ZMod 64679)^146 ≠ 1
        reduce_mod_char
        decide

theorem prime_64717 : Nat.Prime 64717 := by
  apply lucas_primality 64717 (2 : ZMod 64717)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 64717 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5393 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 64717)^32358 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 64717)^21572 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5393 := Nat.prime_eq_prime_of_dvd_pow hq prime_5393 hd
        subst q
        change (2 : ZMod 64717)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_65257 : Nat.Prime 65257 := by
  apply lucas_primality 65257 (5 : ZMod 65257)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 65257 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((2719 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 65257)^32628 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 65257)^21752 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2719 := Nat.prime_eq_prime_of_dvd_pow hq prime_2719 hd
        subst q
        change (5 : ZMod 65257)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_65371 : Nat.Prime 65371 := by
  apply lucas_primality 65371 (2 : ZMod 65371)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 65371 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((2179 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 65371)^32685 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 65371)^21790 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 65371)^13074 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2179 := Nat.prime_eq_prime_of_dvd_pow hq prime_2179 hd
          subst q
          change (2 : ZMod 65371)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_65407 : Nat.Prime 65407 := by
  apply lucas_primality 65407 (3 : ZMod 65407)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 65407 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((991 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 65407)^32703 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 65407)^21802 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 65407)^5946 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 991 := Nat.prime_eq_prime_of_dvd_pow hq prime_991 hd
          subst q
          change (3 : ZMod 65407)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_65539 : Nat.Prime 65539 := by
  apply lucas_primality 65539 (2 : ZMod 65539)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 65539 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((331 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 65539)^32769 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 65539)^21846 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 65539)^5958 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 331 := Nat.prime_eq_prime_of_dvd_pow hq prime_331 hd
          subst q
          change (2 : ZMod 65539)^198 ≠ 1
          reduce_mod_char
          decide

theorem prime_66361 : Nat.Prime 66361 := by
  apply lucas_primality 66361 (17 : ZMod 66361)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 66361 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((79 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 66361)^33180 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 66361)^22120 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (17 : ZMod 66361)^13272 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (17 : ZMod 66361)^9480 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
            subst q
            change (17 : ZMod 66361)^840 ≠ 1
            reduce_mod_char
            decide

theorem prime_66713 : Nat.Prime 66713 := by
  apply lucas_primality 66713 (3 : ZMod 66713)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 66713 - 1 = (2 : ℕ)^3 * ((31 : ℕ)^1 * ((269 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 66713)^33356 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (3 : ZMod 66713)^2152 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
        subst q
        change (3 : ZMod 66713)^248 ≠ 1
        reduce_mod_char
        decide

theorem prime_66919 : Nat.Prime 66919 := by
  apply lucas_primality 66919 (6 : ZMod 66919)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 66919 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((587 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 66919)^33459 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 66919)^22306 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (6 : ZMod 66919)^3522 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 587 := Nat.prime_eq_prime_of_dvd_pow hq prime_587 hd
          subst q
          change (6 : ZMod 66919)^114 ≠ 1
          reduce_mod_char
          decide

theorem prime_67189 : Nat.Prime 67189 := by
  apply lucas_primality 67189 (6 : ZMod 67189)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 67189 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((509 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 67189)^33594 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 67189)^22396 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (6 : ZMod 67189)^6108 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 509 := Nat.prime_eq_prime_of_dvd_pow hq prime_509 hd
          subst q
          change (6 : ZMod 67189)^132 ≠ 1
          reduce_mod_char
          decide

theorem prime_67247 : Nat.Prime 67247 := by
  apply lucas_primality 67247 (5 : ZMod 67247)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 67247 - 1 = (2 : ℕ)^1 * ((33623 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 67247)^33623 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 33623 := Nat.prime_eq_prime_of_dvd_pow hq prime_33623 hd
      subst q
      change (5 : ZMod 67247)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_67433 : Nat.Prime 67433 := by
  apply lucas_primality 67433 (3 : ZMod 67433)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 67433 - 1 = (2 : ℕ)^3 * ((8429 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 67433)^33716 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 8429 := Nat.prime_eq_prime_of_dvd_pow hq prime_8429 hd
      subst q
      change (3 : ZMod 67433)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_67619 : Nat.Prime 67619 := by
  apply lucas_primality 67619 (2 : ZMod 67619)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 67619 - 1 = (2 : ℕ)^1 * ((33809 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 67619)^33809 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 33809 := Nat.prime_eq_prime_of_dvd_pow hq prime_33809 hd
      subst q
      change (2 : ZMod 67619)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_67679 : Nat.Prime 67679 := by
  apply lucas_primality 67679 (19 : ZMod 67679)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 67679 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((19 : ℕ)^1 * ((137 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 67679)^33839 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (19 : ZMod 67679)^5206 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (19 : ZMod 67679)^3562 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
          subst q
          change (19 : ZMod 67679)^494 ≠ 1
          reduce_mod_char
          decide

theorem prime_67733 : Nat.Prime 67733 := by
  apply lucas_primality 67733 (2 : ZMod 67733)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 67733 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((41 : ℕ)^1 * ((59 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 67733)^33866 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 67733)^9676 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (2 : ZMod 67733)^1652 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (2 : ZMod 67733)^1148 ≠ 1
          reduce_mod_char
          decide

theorem prime_67801 : Nat.Prime 67801 := by
  apply lucas_primality 67801 (11 : ZMod 67801)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 67801 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((113 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 67801)^33900 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 67801)^22600 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 67801)^13560 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
          subst q
          change (11 : ZMod 67801)^600 ≠ 1
          reduce_mod_char
          decide

theorem prime_68329 : Nat.Prime 68329 := by
  apply lucas_primality 68329 (11 : ZMod 68329)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 68329 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((13 : ℕ)^1 * ((73 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 68329)^34164 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 68329)^22776 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (11 : ZMod 68329)^5256 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
          subst q
          change (11 : ZMod 68329)^936 ≠ 1
          reduce_mod_char
          decide

theorem prime_68899 : Nat.Prime 68899 := by
  apply lucas_primality 68899 (2 : ZMod 68899)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 68899 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11483 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 68899)^34449 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 68899)^22966 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 11483 := Nat.prime_eq_prime_of_dvd_pow hq prime_11483 hd
        subst q
        change (2 : ZMod 68899)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_69439 : Nat.Prime 69439 := by
  apply lucas_primality 69439 (3 : ZMod 69439)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 69439 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((71 : ℕ)^1 * ((163 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 69439)^34719 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 69439)^23146 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
          subst q
          change (3 : ZMod 69439)^978 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
          subst q
          change (3 : ZMod 69439)^426 ≠ 1
          reduce_mod_char
          decide

theorem prime_69959 : Nat.Prime 69959 := by
  apply lucas_primality 69959 (7 : ZMod 69959)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 69959 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((19 : ℕ)^1 * ((263 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 69959)^34979 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 69959)^9994 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (7 : ZMod 69959)^3682 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 263 := Nat.prime_eq_prime_of_dvd_pow hq prime_263 hd
          subst q
          change (7 : ZMod 69959)^266 ≠ 1
          reduce_mod_char
          decide

theorem prime_70099 : Nat.Prime 70099 := by
  apply lucas_primality 70099 (3 : ZMod 70099)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 70099 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((1669 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 70099)^35049 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 70099)^23366 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 70099)^10014 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1669 := Nat.prime_eq_prime_of_dvd_pow hq prime_1669 hd
          subst q
          change (3 : ZMod 70099)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_70327 : Nat.Prime 70327 := by
  apply lucas_primality 70327 (11 : ZMod 70327)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 70327 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((3907 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 70327)^35163 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 70327)^23442 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3907 := Nat.prime_eq_prime_of_dvd_pow hq prime_3907 hd
        subst q
        change (11 : ZMod 70327)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_71119 : Nat.Prime 71119 := by
  apply lucas_primality 71119 (3 : ZMod 71119)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 71119 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((439 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 71119)^35559 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 71119)^23706 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 439 := Nat.prime_eq_prime_of_dvd_pow hq prime_439 hd
        subst q
        change (3 : ZMod 71119)^162 ≠ 1
        reduce_mod_char
        decide

theorem prime_71359 : Nat.Prime 71359 := by
  apply lucas_primality 71359 (6 : ZMod 71359)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 71359 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((1699 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 71359)^35679 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 71359)^23786 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 71359)^10194 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1699 := Nat.prime_eq_prime_of_dvd_pow hq prime_1699 hd
          subst q
          change (6 : ZMod 71359)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_71647 : Nat.Prime 71647 := by
  apply lucas_primality 71647 (3 : ZMod 71647)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 71647 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11941 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 71647)^35823 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 71647)^23882 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 11941 := Nat.prime_eq_prime_of_dvd_pow hq prime_11941 hd
        subst q
        change (3 : ZMod 71647)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_72053 : Nat.Prime 72053 := by
  apply lucas_primality 72053 (2 : ZMod 72053)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 72053 - 1 = (2 : ℕ)^2 * ((18013 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 72053)^36026 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 18013 := Nat.prime_eq_prime_of_dvd_pow hq prime_18013 hd
      subst q
      change (2 : ZMod 72053)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_72227 : Nat.Prime 72227 := by
  apply lucas_primality 72227 (2 : ZMod 72227)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 72227 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^2 * ((11 : ℕ)^1 * ((67 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 72227)^36113 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 72227)^10318 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 72227)^6566 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (2 : ZMod 72227)^1078 ≠ 1
          reduce_mod_char
          decide

theorem prime_72533 : Nat.Prime 72533 := by
  apply lucas_primality 72533 (2 : ZMod 72533)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 72533 - 1 = (2 : ℕ)^2 * ((18133 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 72533)^36266 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 18133 := Nat.prime_eq_prime_of_dvd_pow hq prime_18133 hd
      subst q
      change (2 : ZMod 72533)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_73331 : Nat.Prime 73331 := by
  apply lucas_primality 73331 (2 : ZMod 73331)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 73331 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7333 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 73331)^36665 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 73331)^14666 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7333 := Nat.prime_eq_prime_of_dvd_pow hq prime_7333 hd
        subst q
        change (2 : ZMod 73331)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_73453 : Nat.Prime 73453 := by
  apply lucas_primality 73453 (2 : ZMod 73453)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 73453 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((6121 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 73453)^36726 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 73453)^24484 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 6121 := Nat.prime_eq_prime_of_dvd_pow hq prime_6121 hd
        subst q
        change (2 : ZMod 73453)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_73651 : Nat.Prime 73651 := by
  apply lucas_primality 73651 (2 : ZMod 73651)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 73651 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((491 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 73651)^36825 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 73651)^24550 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 73651)^14730 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 491 := Nat.prime_eq_prime_of_dvd_pow hq prime_491 hd
          subst q
          change (2 : ZMod 73651)^150 ≠ 1
          reduce_mod_char
          decide

theorem prime_73973 : Nat.Prime 73973 := by
  apply lucas_primality 73973 (2 : ZMod 73973)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 73973 - 1 = (2 : ℕ)^2 * ((18493 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 73973)^36986 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 18493 := Nat.prime_eq_prime_of_dvd_pow hq prime_18493 hd
      subst q
      change (2 : ZMod 73973)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_74381 : Nat.Prime 74381 := by
  apply lucas_primality 74381 (2 : ZMod 74381)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 74381 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((3719 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 74381)^37190 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 74381)^14876 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3719 := Nat.prime_eq_prime_of_dvd_pow hq prime_3719 hd
        subst q
        change (2 : ZMod 74381)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_74413 : Nat.Prime 74413 := by
  apply lucas_primality 74413 (5 : ZMod 74413)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 74413 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((13 : ℕ)^1 * ((53 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 74413)^37206 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 74413)^24804 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (5 : ZMod 74413)^5724 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (5 : ZMod 74413)^1404 ≠ 1
          reduce_mod_char
          decide

theorem prime_74449 : Nat.Prime 74449 := by
  apply lucas_primality 74449 (13 : ZMod 74449)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 74449 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((47 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 74449)^37224 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 74449)^24816 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (13 : ZMod 74449)^6768 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (13 : ZMod 74449)^1584 ≠ 1
          reduce_mod_char
          decide

theorem prime_74713 : Nat.Prime 74713 := by
  apply lucas_primality 74713 (10 : ZMod 74713)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 74713 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((283 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 74713)^37356 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 74713)^24904 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (10 : ZMod 74713)^6792 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 283 := Nat.prime_eq_prime_of_dvd_pow hq prime_283 hd
          subst q
          change (10 : ZMod 74713)^264 ≠ 1
          reduce_mod_char
          decide

theorem prime_74759 : Nat.Prime 74759 := by
  apply lucas_primality 74759 (11 : ZMod 74759)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 74759 - 1 = (2 : ℕ)^1 * ((37379 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 74759)^37379 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 37379 := Nat.prime_eq_prime_of_dvd_pow hq prime_37379 hd
      subst q
      change (11 : ZMod 74759)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_74771 : Nat.Prime 74771 := by
  apply lucas_primality 74771 (2 : ZMod 74771)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 74771 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7477 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 74771)^37385 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 74771)^14954 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7477 := Nat.prime_eq_prime_of_dvd_pow hq prime_7477 hd
        subst q
        change (2 : ZMod 74771)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_74779 : Nat.Prime 74779 := by
  apply lucas_primality 74779 (2 : ZMod 74779)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 74779 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^2 * ((103 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 74779)^37389 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 74779)^24926 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 74779)^6798 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
          subst q
          change (2 : ZMod 74779)^726 ≠ 1
          reduce_mod_char
          decide

theorem prime_75029 : Nat.Prime 75029 := by
  apply lucas_primality 75029 (2 : ZMod 75029)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 75029 - 1 = (2 : ℕ)^2 * ((18757 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 75029)^37514 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 18757 := Nat.prime_eq_prime_of_dvd_pow hq prime_18757 hd
      subst q
      change (2 : ZMod 75029)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_75367 : Nat.Prime 75367 := by
  apply lucas_primality 75367 (3 : ZMod 75367)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 75367 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((53 : ℕ)^1 * ((79 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 75367)^37683 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 75367)^25122 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (3 : ZMod 75367)^1422 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (3 : ZMod 75367)^954 ≠ 1
          reduce_mod_char
          decide

theorem prime_75539 : Nat.Prime 75539 := by
  apply lucas_primality 75539 (2 : ZMod 75539)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 75539 - 1 = (2 : ℕ)^1 * ((179 : ℕ)^1 * ((211 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 75539)^37769 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 179 := Nat.prime_eq_prime_of_dvd_pow hq prime_179 hd
        subst q
        change (2 : ZMod 75539)^422 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 211 := Nat.prime_eq_prime_of_dvd_pow hq prime_211 hd
        subst q
        change (2 : ZMod 75539)^358 ≠ 1
        reduce_mod_char
        decide

theorem prime_75611 : Nat.Prime 75611 := by
  apply lucas_primality 75611 (2 : ZMod 75611)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 75611 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7561 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 75611)^37805 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 75611)^15122 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7561 := Nat.prime_eq_prime_of_dvd_pow hq prime_7561 hd
        subst q
        change (2 : ZMod 75611)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_75833 : Nat.Prime 75833 := by
  apply lucas_primality 75833 (3 : ZMod 75833)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 75833 - 1 = (2 : ℕ)^3 * ((9479 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 75833)^37916 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 9479 := Nat.prime_eq_prime_of_dvd_pow hq prime_9479 hd
      subst q
      change (3 : ZMod 75833)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_75869 : Nat.Prime 75869 := by
  apply lucas_primality 75869 (2 : ZMod 75869)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 75869 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((1459 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 75869)^37934 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 75869)^5836 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1459 := Nat.prime_eq_prime_of_dvd_pow hq prime_1459 hd
        subst q
        change (2 : ZMod 75869)^52 ≠ 1
        reduce_mod_char
        decide

theorem prime_76207 : Nat.Prime 76207 := by
  apply lucas_primality 76207 (3 : ZMod 76207)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 76207 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((977 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 76207)^38103 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 76207)^25402 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 76207)^5862 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 977 := Nat.prime_eq_prime_of_dvd_pow hq prime_977 hd
          subst q
          change (3 : ZMod 76207)^78 ≠ 1
          reduce_mod_char
          decide

theorem prime_76421 : Nat.Prime 76421 := by
  apply lucas_primality 76421 (3 : ZMod 76421)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 76421 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((3821 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 76421)^38210 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 76421)^15284 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3821 := Nat.prime_eq_prime_of_dvd_pow hq prime_3821 hd
        subst q
        change (3 : ZMod 76421)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_76733 : Nat.Prime 76733 := by
  apply lucas_primality 76733 (2 : ZMod 76733)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 76733 - 1 = (2 : ℕ)^2 * ((19183 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 76733)^38366 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 19183 := Nat.prime_eq_prime_of_dvd_pow hq prime_19183 hd
      subst q
      change (2 : ZMod 76733)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_76847 : Nat.Prime 76847 := by
  apply lucas_primality 76847 (5 : ZMod 76847)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 76847 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((499 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 76847)^38423 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 76847)^10978 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 76847)^6986 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 499 := Nat.prime_eq_prime_of_dvd_pow hq prime_499 hd
          subst q
          change (5 : ZMod 76847)^154 ≠ 1
          reduce_mod_char
          decide

theorem prime_77249 : Nat.Prime 77249 := by
  apply lucas_primality 77249 (3 : ZMod 77249)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 77249 - 1 = (2 : ℕ)^6 * ((17 : ℕ)^1 * ((71 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 77249)^38624 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (3 : ZMod 77249)^4544 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
        subst q
        change (3 : ZMod 77249)^1088 ≠ 1
        reduce_mod_char
        decide

theorem prime_77369 : Nat.Prime 77369 := by
  apply lucas_primality 77369 (3 : ZMod 77369)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 77369 - 1 = (2 : ℕ)^3 * ((19 : ℕ)^1 * ((509 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 77369)^38684 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (3 : ZMod 77369)^4072 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 509 := Nat.prime_eq_prime_of_dvd_pow hq prime_509 hd
        subst q
        change (3 : ZMod 77369)^152 ≠ 1
        reduce_mod_char
        decide

theorem prime_77587 : Nat.Prime 77587 := by
  apply lucas_primality 77587 (2 : ZMod 77587)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 77587 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((67 : ℕ)^1 * ((193 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 77587)^38793 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 77587)^25862 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (2 : ZMod 77587)^1158 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
          subst q
          change (2 : ZMod 77587)^402 ≠ 1
          reduce_mod_char
          decide

theorem prime_77813 : Nat.Prime 77813 := by
  apply lucas_primality 77813 (2 : ZMod 77813)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 77813 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^2 * ((397 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 77813)^38906 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 77813)^11116 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 397 := Nat.prime_eq_prime_of_dvd_pow hq prime_397 hd
        subst q
        change (2 : ZMod 77813)^196 ≠ 1
        reduce_mod_char
        decide

theorem prime_78203 : Nat.Prime 78203 := by
  apply lucas_primality 78203 (2 : ZMod 78203)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 78203 - 1 = (2 : ℕ)^1 * ((61 : ℕ)^1 * ((641 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 78203)^39101 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
        subst q
        change (2 : ZMod 78203)^1282 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 641 := Nat.prime_eq_prime_of_dvd_pow hq prime_641 hd
        subst q
        change (2 : ZMod 78203)^122 ≠ 1
        reduce_mod_char
        decide

theorem prime_78241 : Nat.Prime 78241 := by
  apply lucas_primality 78241 (19 : ZMod 78241)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 78241 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((163 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 78241)^39120 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 78241)^26080 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (19 : ZMod 78241)^15648 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
          subst q
          change (19 : ZMod 78241)^480 ≠ 1
          reduce_mod_char
          decide

theorem prime_78301 : Nat.Prime 78301 := by
  apply lucas_primality 78301 (6 : ZMod 78301)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 78301 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((5 : ℕ)^2 * ((29 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 78301)^39150 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 78301)^26100 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 78301)^15660 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (6 : ZMod 78301)^2700 ≠ 1
          reduce_mod_char
          decide

theorem prime_78593 : Nat.Prime 78593 := by
  apply lucas_primality 78593 (3 : ZMod 78593)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 78593 - 1 = (2 : ℕ)^8 * ((307 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 78593)^39296 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 307 := Nat.prime_eq_prime_of_dvd_pow hq prime_307 hd
      subst q
      change (3 : ZMod 78593)^256 ≠ 1
      reduce_mod_char
      decide

theorem prime_78779 : Nat.Prime 78779 := by
  apply lucas_primality 78779 (2 : ZMod 78779)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 78779 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((17 : ℕ)^1 * ((331 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 78779)^39389 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 78779)^11254 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 78779)^4634 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 331 := Nat.prime_eq_prime_of_dvd_pow hq prime_331 hd
          subst q
          change (2 : ZMod 78779)^238 ≠ 1
          reduce_mod_char
          decide

theorem prime_78803 : Nat.Prime 78803 := by
  apply lucas_primality 78803 (2 : ZMod 78803)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 78803 - 1 = (2 : ℕ)^1 * ((31 : ℕ)^2 * ((41 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 78803)^39401 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (2 : ZMod 78803)^2542 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
        subst q
        change (2 : ZMod 78803)^1922 ≠ 1
        reduce_mod_char
        decide

theorem prime_79087 : Nat.Prime 79087 := by
  apply lucas_primality 79087 (3 : ZMod 79087)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 79087 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((269 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 79087)^39543 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 79087)^26362 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 79087)^11298 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
          subst q
          change (3 : ZMod 79087)^294 ≠ 1
          reduce_mod_char
          decide

theorem prime_79193 : Nat.Prime 79193 := by
  apply lucas_primality 79193 (3 : ZMod 79193)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 79193 - 1 = (2 : ℕ)^3 * ((19 : ℕ)^1 * ((521 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 79193)^39596 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (3 : ZMod 79193)^4168 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 521 := Nat.prime_eq_prime_of_dvd_pow hq prime_521 hd
        subst q
        change (3 : ZMod 79193)^152 ≠ 1
        reduce_mod_char
        decide

theorem prime_79201 : Nat.Prime 79201 := by
  apply lucas_primality 79201 (13 : ZMod 79201)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 79201 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^2 * ((5 : ℕ)^2 * ((11 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 79201)^39600 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 79201)^26400 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 79201)^15840 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (13 : ZMod 79201)^7200 ≠ 1
          reduce_mod_char
          decide

theorem prime_79349 : Nat.Prime 79349 := by
  apply lucas_primality 79349 (2 : ZMod 79349)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 79349 - 1 = (2 : ℕ)^2 * ((83 : ℕ)^1 * ((239 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 79349)^39674 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
        subst q
        change (2 : ZMod 79349)^956 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 239 := Nat.prime_eq_prime_of_dvd_pow hq prime_239 hd
        subst q
        change (2 : ZMod 79349)^332 ≠ 1
        reduce_mod_char
        decide

theorem prime_79397 : Nat.Prime 79397 := by
  apply lucas_primality 79397 (2 : ZMod 79397)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 79397 - 1 = (2 : ℕ)^2 * ((23 : ℕ)^1 * ((863 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 79397)^39698 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (2 : ZMod 79397)^3452 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 863 := Nat.prime_eq_prime_of_dvd_pow hq prime_863 hd
        subst q
        change (2 : ZMod 79397)^92 ≠ 1
        reduce_mod_char
        decide

theorem prime_79433 : Nat.Prime 79433 := by
  apply lucas_primality 79433 (3 : ZMod 79433)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 79433 - 1 = (2 : ℕ)^3 * ((9929 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 79433)^39716 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 9929 := Nat.prime_eq_prime_of_dvd_pow hq prime_9929 hd
      subst q
      change (3 : ZMod 79433)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_79561 : Nat.Prime 79561 := by
  apply lucas_primality 79561 (7 : ZMod 79561)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 79561 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((17 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 79561)^39780 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 79561)^26520 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 79561)^15912 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (7 : ZMod 79561)^6120 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (7 : ZMod 79561)^4680 ≠ 1
            reduce_mod_char
            decide

theorem prime_79609 : Nat.Prime 79609 := by
  apply lucas_primality 79609 (14 : ZMod 79609)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 79609 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((31 : ℕ)^1 * ((107 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 79609)^39804 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 79609)^26536 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (14 : ZMod 79609)^2568 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
          subst q
          change (14 : ZMod 79609)^744 ≠ 1
          reduce_mod_char
          decide

theorem prime_79613 : Nat.Prime 79613 := by
  apply lucas_primality 79613 (2 : ZMod 79613)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 79613 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((1531 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 79613)^39806 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 79613)^6124 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1531 := Nat.prime_eq_prime_of_dvd_pow hq prime_1531 hd
        subst q
        change (2 : ZMod 79613)^52 ≠ 1
        reduce_mod_char
        decide

theorem prime_79621 : Nat.Prime 79621 := by
  apply lucas_primality 79621 (2 : ZMod 79621)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 79621 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((1327 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 79621)^39810 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 79621)^26540 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 79621)^15924 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1327 := Nat.prime_eq_prime_of_dvd_pow hq prime_1327 hd
          subst q
          change (2 : ZMod 79621)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_79817 : Nat.Prime 79817 := by
  apply lucas_primality 79817 (3 : ZMod 79817)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 79817 - 1 = (2 : ℕ)^3 * ((11 : ℕ)^1 * ((907 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 79817)^39908 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 79817)^7256 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 907 := Nat.prime_eq_prime_of_dvd_pow hq prime_907 hd
        subst q
        change (3 : ZMod 79817)^88 ≠ 1
        reduce_mod_char
        decide

theorem prime_79841 : Nat.Prime 79841 := by
  apply lucas_primality 79841 (3 : ZMod 79841)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 79841 - 1 = (2 : ℕ)^5 * ((5 : ℕ)^1 * ((499 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 79841)^39920 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 79841)^15968 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 499 := Nat.prime_eq_prime_of_dvd_pow hq prime_499 hd
        subst q
        change (3 : ZMod 79841)^160 ≠ 1
        reduce_mod_char
        decide

theorem prime_80687 : Nat.Prime 80687 := by
  apply lucas_primality 80687 (5 : ZMod 80687)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 80687 - 1 = (2 : ℕ)^1 * ((40343 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 80687)^40343 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 40343 := Nat.prime_eq_prime_of_dvd_pow hq prime_40343 hd
      subst q
      change (5 : ZMod 80687)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_80701 : Nat.Prime 80701 := by
  apply lucas_primality 80701 (2 : ZMod 80701)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 80701 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((269 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 80701)^40350 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 80701)^26900 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 80701)^16140 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
          subst q
          change (2 : ZMod 80701)^300 ≠ 1
          reduce_mod_char
          decide

theorem prime_81019 : Nat.Prime 81019 := by
  apply lucas_primality 81019 (2 : ZMod 81019)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 81019 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((643 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 81019)^40509 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 81019)^27006 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 81019)^11574 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 643 := Nat.prime_eq_prime_of_dvd_pow hq prime_643 hd
          subst q
          change (2 : ZMod 81019)^126 ≠ 1
          reduce_mod_char
          decide

theorem prime_81181 : Nat.Prime 81181 := by
  apply lucas_primality 81181 (6 : ZMod 81181)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 81181 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((41 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 81181)^40590 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 81181)^27060 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 81181)^16236 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (6 : ZMod 81181)^7380 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (6 : ZMod 81181)^1980 ≠ 1
            reduce_mod_char
            decide

theorem prime_81671 : Nat.Prime 81671 := by
  apply lucas_primality 81671 (7 : ZMod 81671)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 81671 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((8167 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 81671)^40835 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 81671)^16334 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 8167 := Nat.prime_eq_prime_of_dvd_pow hq prime_8167 hd
        subst q
        change (7 : ZMod 81671)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_81707 : Nat.Prime 81707 := by
  apply lucas_primality 81707 (2 : ZMod 81707)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 81707 - 1 = (2 : ℕ)^1 * ((40853 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 81707)^40853 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 40853 := Nat.prime_eq_prime_of_dvd_pow hq prime_40853 hd
      subst q
      change (2 : ZMod 81707)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_81799 : Nat.Prime 81799 := by
  apply lucas_primality 81799 (3 : ZMod 81799)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 81799 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13633 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 81799)^40899 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 81799)^27266 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13633 := Nat.prime_eq_prime_of_dvd_pow hq prime_13633 hd
        subst q
        change (3 : ZMod 81799)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_81847 : Nat.Prime 81847 := by
  apply lucas_primality 81847 (3 : ZMod 81847)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 81847 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((4547 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 81847)^40923 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 81847)^27282 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4547 := Nat.prime_eq_prime_of_dvd_pow hq prime_4547 hd
        subst q
        change (3 : ZMod 81847)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_81883 : Nat.Prime 81883 := by
  apply lucas_primality 81883 (3 : ZMod 81883)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 81883 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((4549 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 81883)^40941 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 81883)^27294 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4549 := Nat.prime_eq_prime_of_dvd_pow hq prime_4549 hd
        subst q
        change (3 : ZMod 81883)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_81929 : Nat.Prime 81929 := by
  apply lucas_primality 81929 (3 : ZMod 81929)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 81929 - 1 = (2 : ℕ)^3 * ((7 : ℕ)^2 * ((11 : ℕ)^1 * ((19 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 81929)^40964 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 81929)^11704 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 81929)^7448 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (3 : ZMod 81929)^4312 ≠ 1
          reduce_mod_char
          decide

theorem prime_82729 : Nat.Prime 82729 := by
  apply lucas_primality 82729 (7 : ZMod 82729)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 82729 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((383 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 82729)^41364 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 82729)^27576 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 383 := Nat.prime_eq_prime_of_dvd_pow hq prime_383 hd
        subst q
        change (7 : ZMod 82729)^216 ≠ 1
        reduce_mod_char
        decide

theorem prime_83273 : Nat.Prime 83273 := by
  apply lucas_primality 83273 (3 : ZMod 83273)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 83273 - 1 = (2 : ℕ)^3 * ((7 : ℕ)^1 * ((1487 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 83273)^41636 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 83273)^11896 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1487 := Nat.prime_eq_prime_of_dvd_pow hq prime_1487 hd
        subst q
        change (3 : ZMod 83273)^56 ≠ 1
        reduce_mod_char
        decide

end LegendreK6.Pratt
