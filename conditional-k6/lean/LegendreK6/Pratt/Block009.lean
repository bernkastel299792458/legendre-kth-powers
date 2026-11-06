import LegendreK6.Pratt.Block008

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LegendreK6.Pratt

theorem prime_153623 : Nat.Prime 153623 := by
  apply lucas_primality 153623 (5 : ZMod 153623)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 153623 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((10973 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 153623)^76811 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 153623)^21946 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 10973 := Nat.prime_eq_prime_of_dvd_pow hq prime_10973 hd
        subst q
        change (5 : ZMod 153623)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_154229 : Nat.Prime 154229 := by
  apply lucas_primality 154229 (2 : ZMod 154229)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 154229 - 1 = (2 : ℕ)^2 * ((38557 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 154229)^77114 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 38557 := Nat.prime_eq_prime_of_dvd_pow hq prime_38557 hd
      subst q
      change (2 : ZMod 154229)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_154417 : Nat.Prime 154417 := by
  apply lucas_primality 154417 (10 : ZMod 154417)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 154417 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((3217 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 154417)^77208 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 154417)^51472 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3217 := Nat.prime_eq_prime_of_dvd_pow hq prime_3217 hd
        subst q
        change (10 : ZMod 154417)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_155209 : Nat.Prime 155209 := by
  apply lucas_primality 155209 (7 : ZMod 155209)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 155209 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((29 : ℕ)^1 * ((223 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 155209)^77604 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 155209)^51736 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (7 : ZMod 155209)^5352 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 223 := Nat.prime_eq_prime_of_dvd_pow hq prime_223 hd
          subst q
          change (7 : ZMod 155209)^696 ≠ 1
          reduce_mod_char
          decide

theorem prime_155509 : Nat.Prime 155509 := by
  apply lucas_primality 155509 (2 : ZMod 155509)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 155509 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((12959 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 155509)^77754 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 155509)^51836 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 12959 := Nat.prime_eq_prime_of_dvd_pow hq prime_12959 hd
        subst q
        change (2 : ZMod 155509)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_155777 : Nat.Prime 155777 := by
  apply lucas_primality 155777 (3 : ZMod 155777)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 155777 - 1 = (2 : ℕ)^7 * ((1217 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 155777)^77888 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1217 := Nat.prime_eq_prime_of_dvd_pow hq prime_1217 hd
      subst q
      change (3 : ZMod 155777)^128 ≠ 1
      reduce_mod_char
      decide

theorem prime_155797 : Nat.Prime 155797 := by
  apply lucas_primality 155797 (2 : ZMod 155797)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 155797 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((12983 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 155797)^77898 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 155797)^51932 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 12983 := Nat.prime_eq_prime_of_dvd_pow hq prime_12983 hd
        subst q
        change (2 : ZMod 155797)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_156151 : Nat.Prime 156151 := by
  apply lucas_primality 156151 (3 : ZMod 156151)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 156151 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^2 * ((347 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 156151)^78075 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 156151)^52050 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 156151)^31230 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 347 := Nat.prime_eq_prime_of_dvd_pow hq prime_347 hd
          subst q
          change (3 : ZMod 156151)^450 ≠ 1
          reduce_mod_char
          decide

theorem prime_156511 : Nat.Prime 156511 := by
  apply lucas_primality 156511 (3 : ZMod 156511)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 156511 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((37 : ℕ)^1 * ((47 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 156511)^78255 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 156511)^52170 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 156511)^31302 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
            subst q
            change (3 : ZMod 156511)^4230 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
            subst q
            change (3 : ZMod 156511)^3330 ≠ 1
            reduce_mod_char
            decide

theorem prime_156619 : Nat.Prime 156619 := by
  apply lucas_primality 156619 (11 : ZMod 156619)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 156619 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((113 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 156619)^78309 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 156619)^52206 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (11 : ZMod 156619)^22374 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (11 : ZMod 156619)^14238 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
            subst q
            change (11 : ZMod 156619)^1386 ≠ 1
            reduce_mod_char
            decide

theorem prime_157127 : Nat.Prime 157127 := by
  apply lucas_primality 157127 (5 : ZMod 157127)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 157127 - 1 = (2 : ℕ)^1 * ((251 : ℕ)^1 * ((313 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 157127)^78563 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 251 := Nat.prime_eq_prime_of_dvd_pow hq prime_251 hd
        subst q
        change (5 : ZMod 157127)^626 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 313 := Nat.prime_eq_prime_of_dvd_pow hq prime_313 hd
        subst q
        change (5 : ZMod 157127)^502 ≠ 1
        reduce_mod_char
        decide

theorem prime_157133 : Nat.Prime 157133 := by
  apply lucas_primality 157133 (2 : ZMod 157133)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 157133 - 1 = (2 : ℕ)^2 * ((163 : ℕ)^1 * ((241 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 157133)^78566 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
        subst q
        change (2 : ZMod 157133)^964 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 241 := Nat.prime_eq_prime_of_dvd_pow hq prime_241 hd
        subst q
        change (2 : ZMod 157133)^652 ≠ 1
        reduce_mod_char
        decide

theorem prime_157867 : Nat.Prime 157867 := by
  apply lucas_primality 157867 (2 : ZMod 157867)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 157867 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((83 : ℕ)^1 * ((317 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 157867)^78933 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 157867)^52622 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
          subst q
          change (2 : ZMod 157867)^1902 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 317 := Nat.prime_eq_prime_of_dvd_pow hq prime_317 hd
          subst q
          change (2 : ZMod 157867)^498 ≠ 1
          reduce_mod_char
          decide

theorem prime_158243 : Nat.Prime 158243 := by
  apply lucas_primality 158243 (2 : ZMod 158243)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 158243 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((89 : ℕ)^1 * ((127 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 158243)^79121 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 158243)^22606 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (2 : ZMod 158243)^1778 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
          subst q
          change (2 : ZMod 158243)^1246 ≠ 1
          reduce_mod_char
          decide

theorem prime_159097 : Nat.Prime 159097 := by
  apply lucas_primality 159097 (5 : ZMod 159097)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 159097 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((947 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 159097)^79548 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 159097)^53032 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 159097)^22728 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 947 := Nat.prime_eq_prime_of_dvd_pow hq prime_947 hd
          subst q
          change (5 : ZMod 159097)^168 ≠ 1
          reduce_mod_char
          decide

theorem prime_159683 : Nat.Prime 159683 := by
  apply lucas_primality 159683 (2 : ZMod 159683)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 159683 - 1 = (2 : ℕ)^1 * ((79841 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 159683)^79841 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 79841 := Nat.prime_eq_prime_of_dvd_pow hq prime_79841 hd
      subst q
      change (2 : ZMod 159683)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_161561 : Nat.Prime 161561 := by
  apply lucas_primality 161561 (3 : ZMod 161561)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 161561 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((577 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 161561)^80780 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 161561)^32312 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 161561)^23080 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 577 := Nat.prime_eq_prime_of_dvd_pow hq prime_577 hd
          subst q
          change (3 : ZMod 161561)^280 ≠ 1
          reduce_mod_char
          decide

theorem prime_161591 : Nat.Prime 161591 := by
  apply lucas_primality 161591 (11 : ZMod 161591)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 161591 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((113 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 161591)^80795 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 161591)^32318 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (11 : ZMod 161591)^14690 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (11 : ZMod 161591)^12430 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
            subst q
            change (11 : ZMod 161591)^1430 ≠ 1
            reduce_mod_char
            decide

theorem prime_161879 : Nat.Prime 161879 := by
  apply lucas_primality 161879 (7 : ZMod 161879)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 161879 - 1 = (2 : ℕ)^1 * ((29 : ℕ)^1 * ((2791 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 161879)^80939 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (7 : ZMod 161879)^5582 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2791 := Nat.prime_eq_prime_of_dvd_pow hq prime_2791 hd
        subst q
        change (7 : ZMod 161879)^58 ≠ 1
        reduce_mod_char
        decide

theorem prime_162343 : Nat.Prime 162343 := by
  apply lucas_primality 162343 (3 : ZMod 162343)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 162343 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((29 : ℕ)^1 * ((311 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 162343)^81171 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 162343)^54114 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (3 : ZMod 162343)^5598 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 311 := Nat.prime_eq_prime_of_dvd_pow hq prime_311 hd
          subst q
          change (3 : ZMod 162343)^522 ≠ 1
          reduce_mod_char
          decide

theorem prime_162553 : Nat.Prime 162553 := by
  apply lucas_primality 162553 (10 : ZMod 162553)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 162553 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((521 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 162553)^81276 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 162553)^54184 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (10 : ZMod 162553)^12504 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 521 := Nat.prime_eq_prime_of_dvd_pow hq prime_521 hd
          subst q
          change (10 : ZMod 162553)^312 ≠ 1
          reduce_mod_char
          decide

theorem prime_163859 : Nat.Prime 163859 := by
  apply lucas_primality 163859 (2 : ZMod 163859)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 163859 - 1 = (2 : ℕ)^1 * ((81929 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 163859)^81929 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 81929 := Nat.prime_eq_prime_of_dvd_pow hq prime_81929 hd
      subst q
      change (2 : ZMod 163859)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_166273 : Nat.Prime 166273 := by
  apply lucas_primality 166273 (5 : ZMod 166273)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 166273 - 1 = (2 : ℕ)^7 * ((3 : ℕ)^1 * ((433 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 166273)^83136 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 166273)^55424 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 433 := Nat.prime_eq_prime_of_dvd_pow hq prime_433 hd
        subst q
        change (5 : ZMod 166273)^384 ≠ 1
        reduce_mod_char
        decide

theorem prime_166643 : Nat.Prime 166643 := by
  apply lucas_primality 166643 (2 : ZMod 166643)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 166643 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((11903 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 166643)^83321 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 166643)^23806 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 11903 := Nat.prime_eq_prime_of_dvd_pow hq prime_11903 hd
        subst q
        change (2 : ZMod 166643)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_166667 : Nat.Prime 166667 := by
  apply lucas_primality 166667 (2 : ZMod 166667)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 166667 - 1 = (2 : ℕ)^1 * ((167 : ℕ)^1 * ((499 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 166667)^83333 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
        subst q
        change (2 : ZMod 166667)^998 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 499 := Nat.prime_eq_prime_of_dvd_pow hq prime_499 hd
        subst q
        change (2 : ZMod 166667)^334 ≠ 1
        reduce_mod_char
        decide

theorem prime_167953 : Nat.Prime 167953 := by
  apply lucas_primality 167953 (5 : ZMod 167953)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 167953 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((3499 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 167953)^83976 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 167953)^55984 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3499 := Nat.prime_eq_prime_of_dvd_pow hq prime_3499 hd
        subst q
        change (5 : ZMod 167953)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_168457 : Nat.Prime 168457 := by
  apply lucas_primality 168457 (5 : ZMod 168457)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 168457 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((7019 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 168457)^84228 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 168457)^56152 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7019 := Nat.prime_eq_prime_of_dvd_pow hq prime_7019 hd
        subst q
        change (5 : ZMod 168457)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_169483 : Nat.Prime 169483 := by
  apply lucas_primality 169483 (3 : ZMod 169483)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 169483 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((47 : ℕ)^1 * ((601 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 169483)^84741 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 169483)^56494 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (3 : ZMod 169483)^3606 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 601 := Nat.prime_eq_prime_of_dvd_pow hq prime_601 hd
          subst q
          change (3 : ZMod 169483)^282 ≠ 1
          reduce_mod_char
          decide

theorem prime_169553 : Nat.Prime 169553 := by
  apply lucas_primality 169553 (3 : ZMod 169553)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 169553 - 1 = (2 : ℕ)^4 * ((10597 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 169553)^84776 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 10597 := Nat.prime_eq_prime_of_dvd_pow hq prime_10597 hd
      subst q
      change (3 : ZMod 169553)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_170647 : Nat.Prime 170647 := by
  apply lucas_primality 170647 (6 : ZMod 170647)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 170647 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((17 : ℕ)^1 * ((239 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 170647)^85323 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 170647)^56882 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 170647)^24378 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (6 : ZMod 170647)^10038 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 239 := Nat.prime_eq_prime_of_dvd_pow hq prime_239 hd
            subst q
            change (6 : ZMod 170647)^714 ≠ 1
            reduce_mod_char
            decide

theorem prime_171719 : Nat.Prime 171719 := by
  apply lucas_primality 171719 (7 : ZMod 171719)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 171719 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((3733 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 171719)^85859 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (7 : ZMod 171719)^7466 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3733 := Nat.prime_eq_prime_of_dvd_pow hq prime_3733 hd
        subst q
        change (7 : ZMod 171719)^46 ≠ 1
        reduce_mod_char
        decide

theorem prime_171869 : Nat.Prime 171869 := by
  apply lucas_primality 171869 (2 : ZMod 171869)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 171869 - 1 = (2 : ℕ)^2 * ((42967 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 171869)^85934 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 42967 := Nat.prime_eq_prime_of_dvd_pow hq prime_42967 hd
      subst q
      change (2 : ZMod 171869)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_172399 : Nat.Prime 172399 := by
  apply lucas_primality 172399 (6 : ZMod 172399)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 172399 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((59 : ℕ)^1 * ((487 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 172399)^86199 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 172399)^57466 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (6 : ZMod 172399)^2922 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 487 := Nat.prime_eq_prime_of_dvd_pow hq prime_487 hd
          subst q
          change (6 : ZMod 172399)^354 ≠ 1
          reduce_mod_char
          decide

theorem prime_172411 : Nat.Prime 172411 := by
  apply lucas_primality 172411 (3 : ZMod 172411)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 172411 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((821 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 172411)^86205 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 172411)^57470 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 172411)^34482 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (3 : ZMod 172411)^24630 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 821 := Nat.prime_eq_prime_of_dvd_pow hq prime_821 hd
            subst q
            change (3 : ZMod 172411)^210 ≠ 1
            reduce_mod_char
            decide

theorem prime_172673 : Nat.Prime 172673 := by
  apply lucas_primality 172673 (3 : ZMod 172673)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 172673 - 1 = (2 : ℕ)^7 * ((19 : ℕ)^1 * ((71 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 172673)^86336 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (3 : ZMod 172673)^9088 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
        subst q
        change (3 : ZMod 172673)^2432 ≠ 1
        reduce_mod_char
        decide

theorem prime_174149 : Nat.Prime 174149 := by
  apply lucas_primality 174149 (2 : ZMod 174149)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 174149 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((17 : ℕ)^1 * ((197 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 174149)^87074 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 174149)^13396 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 174149)^10244 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
          subst q
          change (2 : ZMod 174149)^884 ≠ 1
          reduce_mod_char
          decide

theorem prime_174289 : Nat.Prime 174289 := by
  apply lucas_primality 174289 (13 : ZMod 174289)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 174289 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((3631 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 174289)^87144 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 174289)^58096 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3631 := Nat.prime_eq_prime_of_dvd_pow hq prime_3631 hd
        subst q
        change (13 : ZMod 174289)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_175601 : Nat.Prime 175601 := by
  apply lucas_primality 175601 (3 : ZMod 175601)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 175601 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^2 * ((439 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 175601)^87800 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 175601)^35120 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 439 := Nat.prime_eq_prime_of_dvd_pow hq prime_439 hd
        subst q
        change (3 : ZMod 175601)^400 ≠ 1
        reduce_mod_char
        decide

theorem prime_175723 : Nat.Prime 175723 := by
  apply lucas_primality 175723 (2 : ZMod 175723)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 175723 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((29287 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 175723)^87861 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 175723)^58574 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 29287 := Nat.prime_eq_prime_of_dvd_pow hq prime_29287 hd
        subst q
        change (2 : ZMod 175723)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_175783 : Nat.Prime 175783 := by
  apply lucas_primality 175783 (3 : ZMod 175783)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 175783 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((29297 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 175783)^87891 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 175783)^58594 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 29297 := Nat.prime_eq_prime_of_dvd_pow hq prime_29297 hd
        subst q
        change (3 : ZMod 175783)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_175837 : Nat.Prime 175837 := by
  apply lucas_primality 175837 (2 : ZMod 175837)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 175837 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((14653 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 175837)^87918 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 175837)^58612 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 14653 := Nat.prime_eq_prime_of_dvd_pow hq prime_14653 hd
        subst q
        change (2 : ZMod 175837)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_176573 : Nat.Prime 176573 := by
  apply lucas_primality 176573 (2 : ZMod 176573)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 176573 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((4013 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 176573)^88286 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 176573)^16052 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4013 := Nat.prime_eq_prime_of_dvd_pow hq prime_4013 hd
        subst q
        change (2 : ZMod 176573)^44 ≠ 1
        reduce_mod_char
        decide

theorem prime_176819 : Nat.Prime 176819 := by
  apply lucas_primality 176819 (2 : ZMod 176819)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 176819 - 1 = (2 : ℕ)^1 * ((211 : ℕ)^1 * ((419 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 176819)^88409 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 211 := Nat.prime_eq_prime_of_dvd_pow hq prime_211 hd
        subst q
        change (2 : ZMod 176819)^838 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 419 := Nat.prime_eq_prime_of_dvd_pow hq prime_419 hd
        subst q
        change (2 : ZMod 176819)^422 ≠ 1
        reduce_mod_char
        decide

theorem prime_178441 : Nat.Prime 178441 := by
  apply lucas_primality 178441 (11 : ZMod 178441)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 178441 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((1487 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 178441)^89220 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 178441)^59480 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 178441)^35688 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1487 := Nat.prime_eq_prime_of_dvd_pow hq prime_1487 hd
          subst q
          change (11 : ZMod 178441)^120 ≠ 1
          reduce_mod_char
          decide

theorem prime_179083 : Nat.Prime 179083 := by
  apply lucas_primality 179083 (5 : ZMod 179083)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 179083 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((9949 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 179083)^89541 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 179083)^59694 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 9949 := Nat.prime_eq_prime_of_dvd_pow hq prime_9949 hd
        subst q
        change (5 : ZMod 179083)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_179689 : Nat.Prime 179689 := by
  apply lucas_primality 179689 (7 : ZMod 179689)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 179689 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((7487 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 179689)^89844 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 179689)^59896 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7487 := Nat.prime_eq_prime_of_dvd_pow hq prime_7487 hd
        subst q
        change (7 : ZMod 179689)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_180749 : Nat.Prime 180749 := by
  apply lucas_primality 180749 (2 : ZMod 180749)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 180749 - 1 = (2 : ℕ)^2 * ((73 : ℕ)^1 * ((619 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 180749)^90374 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
        subst q
        change (2 : ZMod 180749)^2476 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 619 := Nat.prime_eq_prime_of_dvd_pow hq prime_619 hd
        subst q
        change (2 : ZMod 180749)^292 ≠ 1
        reduce_mod_char
        decide

theorem prime_181387 : Nat.Prime 181387 := by
  apply lucas_primality 181387 (2 : ZMod 181387)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 181387 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((3359 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 181387)^90693 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 181387)^60462 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3359 := Nat.prime_eq_prime_of_dvd_pow hq prime_3359 hd
        subst q
        change (2 : ZMod 181387)^54 ≠ 1
        reduce_mod_char
        decide

theorem prime_181763 : Nat.Prime 181763 := by
  apply lucas_primality 181763 (2 : ZMod 181763)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 181763 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((12983 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 181763)^90881 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 181763)^25966 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 12983 := Nat.prime_eq_prime_of_dvd_pow hq prime_12983 hd
        subst q
        change (2 : ZMod 181763)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_182773 : Nat.Prime 182773 := by
  apply lucas_primality 182773 (6 : ZMod 182773)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 182773 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5077 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 182773)^91386 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 182773)^60924 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5077 := Nat.prime_eq_prime_of_dvd_pow hq prime_5077 hd
        subst q
        change (6 : ZMod 182773)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_182899 : Nat.Prime 182899 := by
  apply lucas_primality 182899 (10 : ZMod 182899)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 182899 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((1129 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 182899)^91449 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 182899)^60966 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1129 := Nat.prime_eq_prime_of_dvd_pow hq prime_1129 hd
        subst q
        change (10 : ZMod 182899)^162 ≠ 1
        reduce_mod_char
        decide

theorem prime_183373 : Nat.Prime 183373 := by
  apply lucas_primality 183373 (2 : ZMod 183373)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 183373 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((37 : ℕ)^1 * ((59 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 183373)^91686 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 183373)^61124 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 183373)^26196 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
            subst q
            change (2 : ZMod 183373)^4956 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
            subst q
            change (2 : ZMod 183373)^3108 ≠ 1
            reduce_mod_char
            decide

theorem prime_184271 : Nat.Prime 184271 := by
  apply lucas_primality 184271 (19 : ZMod 184271)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 184271 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((18427 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 184271)^92135 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (19 : ZMod 184271)^36854 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 18427 := Nat.prime_eq_prime_of_dvd_pow hq prime_18427 hd
        subst q
        change (19 : ZMod 184271)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_184417 : Nat.Prime 184417 := by
  apply lucas_primality 184417 (10 : ZMod 184417)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 184417 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((113 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 184417)^92208 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 184417)^61472 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (10 : ZMod 184417)^10848 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
          subst q
          change (10 : ZMod 184417)^1632 ≠ 1
          reduce_mod_char
          decide

theorem prime_184517 : Nat.Prime 184517 := by
  apply lucas_primality 184517 (2 : ZMod 184517)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 184517 - 1 = (2 : ℕ)^2 * ((163 : ℕ)^1 * ((283 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 184517)^92258 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
        subst q
        change (2 : ZMod 184517)^1132 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 283 := Nat.prime_eq_prime_of_dvd_pow hq prime_283 hd
        subst q
        change (2 : ZMod 184517)^652 ≠ 1
        reduce_mod_char
        decide

theorem prime_184649 : Nat.Prime 184649 := by
  apply lucas_primality 184649 (3 : ZMod 184649)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 184649 - 1 = (2 : ℕ)^3 * ((23081 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 184649)^92324 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 23081 := Nat.prime_eq_prime_of_dvd_pow hq prime_23081 hd
      subst q
      change (3 : ZMod 184649)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_185069 : Nat.Prime 185069 := by
  apply lucas_primality 185069 (2 : ZMod 185069)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 185069 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((3559 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 185069)^92534 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 185069)^14236 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3559 := Nat.prime_eq_prime_of_dvd_pow hq prime_3559 hd
        subst q
        change (2 : ZMod 185069)^52 ≠ 1
        reduce_mod_char
        decide

theorem prime_188261 : Nat.Prime 188261 := by
  apply lucas_primality 188261 (2 : ZMod 188261)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 188261 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((9413 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 188261)^94130 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 188261)^37652 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 9413 := Nat.prime_eq_prime_of_dvd_pow hq prime_9413 hd
        subst q
        change (2 : ZMod 188261)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_188791 : Nat.Prime 188791 := by
  apply lucas_primality 188791 (7 : ZMod 188791)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 188791 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((29 : ℕ)^1 * ((31 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 188791)^94395 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 188791)^62930 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 188791)^37758 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (7 : ZMod 188791)^26970 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
              subst q
              change (7 : ZMod 188791)^6510 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
              subst q
              change (7 : ZMod 188791)^6090 ≠ 1
              reduce_mod_char
              decide

theorem prime_189473 : Nat.Prime 189473 := by
  apply lucas_primality 189473 (3 : ZMod 189473)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 189473 - 1 = (2 : ℕ)^5 * ((31 : ℕ)^1 * ((191 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 189473)^94736 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (3 : ZMod 189473)^6112 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
        subst q
        change (3 : ZMod 189473)^992 ≠ 1
        reduce_mod_char
        decide

theorem prime_189671 : Nat.Prime 189671 := by
  apply lucas_primality 189671 (11 : ZMod 189671)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 189671 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((1459 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 189671)^94835 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 189671)^37934 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (11 : ZMod 189671)^14590 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1459 := Nat.prime_eq_prime_of_dvd_pow hq prime_1459 hd
          subst q
          change (11 : ZMod 189671)^130 ≠ 1
          reduce_mod_char
          decide

theorem prime_189691 : Nat.Prime 189691 := by
  apply lucas_primality 189691 (10 : ZMod 189691)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 189691 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((6323 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 189691)^94845 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 189691)^63230 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 189691)^37938 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 6323 := Nat.prime_eq_prime_of_dvd_pow hq prime_6323 hd
          subst q
          change (10 : ZMod 189691)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_189859 : Nat.Prime 189859 := by
  apply lucas_primality 189859 (2 : ZMod 189859)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 189859 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((31643 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 189859)^94929 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 189859)^63286 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 31643 := Nat.prime_eq_prime_of_dvd_pow hq prime_31643 hd
        subst q
        change (2 : ZMod 189859)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_189901 : Nat.Prime 189901 := by
  apply lucas_primality 189901 (2 : ZMod 189901)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 189901 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^2 * ((211 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 189901)^94950 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 189901)^63300 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 189901)^37980 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 211 := Nat.prime_eq_prime_of_dvd_pow hq prime_211 hd
          subst q
          change (2 : ZMod 189901)^900 ≠ 1
          reduce_mod_char
          decide

theorem prime_190901 : Nat.Prime 190901 := by
  apply lucas_primality 190901 (2 : ZMod 190901)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 190901 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((23 : ℕ)^1 * ((83 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 190901)^95450 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 190901)^38180 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 190901)^8300 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
          subst q
          change (2 : ZMod 190901)^2300 ≠ 1
          reduce_mod_char
          decide

theorem prime_191519 : Nat.Prime 191519 := by
  apply lucas_primality 191519 (11 : ZMod 191519)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 191519 - 1 = (2 : ℕ)^1 * ((31 : ℕ)^1 * ((3089 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 191519)^95759 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (11 : ZMod 191519)^6178 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3089 := Nat.prime_eq_prime_of_dvd_pow hq prime_3089 hd
        subst q
        change (11 : ZMod 191519)^62 ≠ 1
        reduce_mod_char
        decide

theorem prime_191531 : Nat.Prime 191531 := by
  apply lucas_primality 191531 (2 : ZMod 191531)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 191531 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((107 : ℕ)^1 * ((179 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 191531)^95765 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 191531)^38306 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
          subst q
          change (2 : ZMod 191531)^1790 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 179 := Nat.prime_eq_prime_of_dvd_pow hq prime_179 hd
          subst q
          change (2 : ZMod 191531)^1070 ≠ 1
          reduce_mod_char
          decide

theorem prime_191551 : Nat.Prime 191551 := by
  apply lucas_primality 191551 (3 : ZMod 191551)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 191551 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((1277 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 191551)^95775 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 191551)^63850 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 191551)^38310 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1277 := Nat.prime_eq_prime_of_dvd_pow hq prime_1277 hd
          subst q
          change (3 : ZMod 191551)^150 ≠ 1
          reduce_mod_char
          decide

theorem prime_191783 : Nat.Prime 191783 := by
  apply lucas_primality 191783 (5 : ZMod 191783)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 191783 - 1 = (2 : ℕ)^1 * ((95891 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 191783)^95891 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 95891 := Nat.prime_eq_prime_of_dvd_pow hq prime_95891 hd
      subst q
      change (5 : ZMod 191783)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_193153 : Nat.Prime 193153 := by
  apply lucas_primality 193153 (5 : ZMod 193153)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 193153 - 1 = (2 : ℕ)^7 * ((3 : ℕ)^1 * ((503 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 193153)^96576 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 193153)^64384 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 503 := Nat.prime_eq_prime_of_dvd_pow hq prime_503 hd
        subst q
        change (5 : ZMod 193153)^384 ≠ 1
        reduce_mod_char
        decide

theorem prime_194371 : Nat.Prime 194371 := by
  apply lucas_primality 194371 (2 : ZMod 194371)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 194371 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((19 : ℕ)^1 * ((31 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 194371)^97185 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 194371)^64790 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 194371)^38874 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (2 : ZMod 194371)^17670 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
              subst q
              change (2 : ZMod 194371)^10230 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
              subst q
              change (2 : ZMod 194371)^6270 ≠ 1
              reduce_mod_char
              decide

theorem prime_194591 : Nat.Prime 194591 := by
  apply lucas_primality 194591 (11 : ZMod 194591)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 194591 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((29 : ℕ)^1 * ((61 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 194591)^97295 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 194591)^38918 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (11 : ZMod 194591)^17690 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (11 : ZMod 194591)^6710 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
            subst q
            change (11 : ZMod 194591)^3190 ≠ 1
            reduce_mod_char
            decide

theorem prime_195077 : Nat.Prime 195077 := by
  apply lucas_primality 195077 (2 : ZMod 195077)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 195077 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((6967 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 195077)^97538 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 195077)^27868 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 6967 := Nat.prime_eq_prime_of_dvd_pow hq prime_6967 hd
        subst q
        change (2 : ZMod 195077)^28 ≠ 1
        reduce_mod_char
        decide

theorem prime_195089 : Nat.Prime 195089 := by
  apply lucas_primality 195089 (3 : ZMod 195089)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 195089 - 1 = (2 : ℕ)^4 * ((89 : ℕ)^1 * ((137 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 195089)^97544 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
        subst q
        change (3 : ZMod 195089)^2192 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
        subst q
        change (3 : ZMod 195089)^1424 ≠ 1
        reduce_mod_char
        decide

theorem prime_196879 : Nat.Prime 196879 := by
  apply lucas_primality 196879 (6 : ZMod 196879)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 196879 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((19 : ℕ)^1 * ((157 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 196879)^98439 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 196879)^65626 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (6 : ZMod 196879)^17898 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (6 : ZMod 196879)^10362 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
            subst q
            change (6 : ZMod 196879)^1254 ≠ 1
            reduce_mod_char
            decide

theorem prime_197341 : Nat.Prime 197341 := by
  apply lucas_primality 197341 (2 : ZMod 197341)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 197341 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((23 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 197341)^98670 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 197341)^65780 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 197341)^39468 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (2 : ZMod 197341)^17940 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
              subst q
              change (2 : ZMod 197341)^15180 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
              subst q
              change (2 : ZMod 197341)^8580 ≠ 1
              reduce_mod_char
              decide

theorem prime_199489 : Nat.Prime 199489 := by
  apply lucas_primality 199489 (14 : ZMod 199489)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 199489 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^1 * ((1039 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 199489)^99744 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 199489)^66496 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1039 := Nat.prime_eq_prime_of_dvd_pow hq prime_1039 hd
        subst q
        change (14 : ZMod 199489)^192 ≠ 1
        reduce_mod_char
        decide

theorem prime_201011 : Nat.Prime 201011 := by
  apply lucas_primality 201011 (2 : ZMod 201011)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 201011 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((20101 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 201011)^100505 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 201011)^40202 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 20101 := Nat.prime_eq_prime_of_dvd_pow hq prime_20101 hd
        subst q
        change (2 : ZMod 201011)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_201451 : Nat.Prime 201451 := by
  apply lucas_primality 201451 (2 : ZMod 201451)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 201451 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((17 : ℕ)^1 * ((79 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 201451)^100725 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 201451)^67150 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 201451)^40290 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (2 : ZMod 201451)^11850 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
            subst q
            change (2 : ZMod 201451)^2550 ≠ 1
            reduce_mod_char
            decide

theorem prime_201581 : Nat.Prime 201581 := by
  apply lucas_primality 201581 (2 : ZMod 201581)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 201581 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((10079 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 201581)^100790 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 201581)^40316 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 10079 := Nat.prime_eq_prime_of_dvd_pow hq prime_10079 hd
        subst q
        change (2 : ZMod 201581)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_203363 : Nat.Prime 203363 := by
  apply lucas_primality 203363 (2 : ZMod 203363)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 203363 - 1 = (2 : ℕ)^1 * ((101681 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 203363)^101681 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 101681 := Nat.prime_eq_prime_of_dvd_pow hq prime_101681 hd
      subst q
      change (2 : ZMod 203363)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_204437 : Nat.Prime 204437 := by
  apply lucas_primality 204437 (2 : ZMod 204437)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 204437 - 1 = (2 : ℕ)^2 * ((51109 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 204437)^102218 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 51109 := Nat.prime_eq_prime_of_dvd_pow hq prime_51109 hd
      subst q
      change (2 : ZMod 204437)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_205211 : Nat.Prime 205211 := by
  apply lucas_primality 205211 (2 : ZMod 205211)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 205211 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((20521 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 205211)^102605 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 205211)^41042 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 20521 := Nat.prime_eq_prime_of_dvd_pow hq prime_20521 hd
        subst q
        change (2 : ZMod 205211)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_205307 : Nat.Prime 205307 := by
  apply lucas_primality 205307 (2 : ZMod 205307)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 205307 - 1 = (2 : ℕ)^1 * ((102653 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 205307)^102653 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 102653 := Nat.prime_eq_prime_of_dvd_pow hq prime_102653 hd
      subst q
      change (2 : ZMod 205307)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_205477 : Nat.Prime 205477 := by
  apply lucas_primality 205477 (5 : ZMod 205477)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 205477 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((17123 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 205477)^102738 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 205477)^68492 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 17123 := Nat.prime_eq_prime_of_dvd_pow hq prime_17123 hd
        subst q
        change (5 : ZMod 205477)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_205703 : Nat.Prime 205703 := by
  apply lucas_primality 205703 (5 : ZMod 205703)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 205703 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^2 * ((2099 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 205703)^102851 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 205703)^29386 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2099 := Nat.prime_eq_prime_of_dvd_pow hq prime_2099 hd
        subst q
        change (5 : ZMod 205703)^98 ≠ 1
        reduce_mod_char
        decide

theorem prime_207967 : Nat.Prime 207967 := by
  apply lucas_primality 207967 (3 : ZMod 207967)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 207967 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((23 : ℕ)^1 * ((137 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 207967)^103983 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 207967)^69322 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 207967)^18906 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (3 : ZMod 207967)^9042 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
            subst q
            change (3 : ZMod 207967)^1518 ≠ 1
            reduce_mod_char
            decide

theorem prime_208121 : Nat.Prime 208121 := by
  apply lucas_primality 208121 (3 : ZMod 208121)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 208121 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((11 : ℕ)^2 * ((43 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 208121)^104060 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 208121)^41624 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 208121)^18920 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (3 : ZMod 208121)^4840 ≠ 1
          reduce_mod_char
          decide

theorem prime_209717 : Nat.Prime 209717 := by
  apply lucas_primality 209717 (2 : ZMod 209717)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 209717 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((37 : ℕ)^1 * ((109 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 209717)^104858 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 209717)^16132 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (2 : ZMod 209717)^5668 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
          subst q
          change (2 : ZMod 209717)^1924 ≠ 1
          reduce_mod_char
          decide

theorem prime_210283 : Nat.Prime 210283 := by
  apply lucas_primality 210283 (2 : ZMod 210283)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 210283 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((101 : ℕ)^1 * ((347 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 210283)^105141 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 210283)^70094 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
          subst q
          change (2 : ZMod 210283)^2082 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 347 := Nat.prime_eq_prime_of_dvd_pow hq prime_347 hd
          subst q
          change (2 : ZMod 210283)^606 ≠ 1
          reduce_mod_char
          decide

theorem prime_211247 : Nat.Prime 211247 := by
  apply lucas_primality 211247 (5 : ZMod 211247)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 211247 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((79 : ℕ)^1 * ((191 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 211247)^105623 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 211247)^30178 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (5 : ZMod 211247)^2674 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
          subst q
          change (5 : ZMod 211247)^1106 ≠ 1
          reduce_mod_char
          decide

theorem prime_211661 : Nat.Prime 211661 := by
  apply lucas_primality 211661 (2 : ZMod 211661)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 211661 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((19 : ℕ)^1 * ((557 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 211661)^105830 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 211661)^42332 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 211661)^11140 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 557 := Nat.prime_eq_prime_of_dvd_pow hq prime_557 hd
          subst q
          change (2 : ZMod 211661)^380 ≠ 1
          reduce_mod_char
          decide

theorem prime_213067 : Nat.Prime 213067 := by
  apply lucas_primality 213067 (2 : ZMod 213067)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 213067 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((19 : ℕ)^1 * ((89 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 213067)^106533 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 213067)^71022 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 213067)^30438 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (2 : ZMod 213067)^11214 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
            subst q
            change (2 : ZMod 213067)^2394 ≠ 1
            reduce_mod_char
            decide

theorem prime_213791 : Nat.Prime 213791 := by
  apply lucas_primality 213791 (13 : ZMod 213791)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 213791 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((21379 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 213791)^106895 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (13 : ZMod 213791)^42758 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 21379 := Nat.prime_eq_prime_of_dvd_pow hq prime_21379 hd
        subst q
        change (13 : ZMod 213791)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_214363 : Nat.Prime 214363 := by
  apply lucas_primality 214363 (7 : ZMod 214363)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 214363 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((11909 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 214363)^107181 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 214363)^71454 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 11909 := Nat.prime_eq_prime_of_dvd_pow hq prime_11909 hd
        subst q
        change (7 : ZMod 214363)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_214391 : Nat.Prime 214391 := by
  apply lucas_primality 214391 (7 : ZMod 214391)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 214391 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((1949 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 214391)^107195 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 214391)^42878 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (7 : ZMod 214391)^19490 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1949 := Nat.prime_eq_prime_of_dvd_pow hq prime_1949 hd
          subst q
          change (7 : ZMod 214391)^110 ≠ 1
          reduce_mod_char
          decide

theorem prime_214457 : Nat.Prime 214457 := by
  apply lucas_primality 214457 (6 : ZMod 214457)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 214457 - 1 = (2 : ℕ)^3 * ((11 : ℕ)^1 * ((2437 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 214457)^107228 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (6 : ZMod 214457)^19496 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2437 := Nat.prime_eq_prime_of_dvd_pow hq prime_2437 hd
        subst q
        change (6 : ZMod 214457)^88 ≠ 1
        reduce_mod_char
        decide

theorem prime_215279 : Nat.Prime 215279 := by
  apply lucas_primality 215279 (7 : ZMod 215279)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 215279 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((15377 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 215279)^107639 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 215279)^30754 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 15377 := Nat.prime_eq_prime_of_dvd_pow hq prime_15377 hd
        subst q
        change (7 : ZMod 215279)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_216119 : Nat.Prime 216119 := by
  apply lucas_primality 216119 (7 : ZMod 216119)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 216119 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((43 : ℕ)^1 * ((359 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 216119)^108059 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 216119)^30874 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (7 : ZMod 216119)^5026 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 359 := Nat.prime_eq_prime_of_dvd_pow hq prime_359 hd
          subst q
          change (7 : ZMod 216119)^602 ≠ 1
          reduce_mod_char
          decide

theorem prime_218083 : Nat.Prime 218083 := by
  apply lucas_primality 218083 (2 : ZMod 218083)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 218083 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((1913 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 218083)^109041 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 218083)^72694 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 218083)^11478 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1913 := Nat.prime_eq_prime_of_dvd_pow hq prime_1913 hd
          subst q
          change (2 : ZMod 218083)^114 ≠ 1
          reduce_mod_char
          decide

theorem prime_218527 : Nat.Prime 218527 := by
  apply lucas_primality 218527 (3 : ZMod 218527)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 218527 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^2 * ((43 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 218527)^109263 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 218527)^72842 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 218527)^31218 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (3 : ZMod 218527)^19866 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (3 : ZMod 218527)^5082 ≠ 1
            reduce_mod_char
            decide

theorem prime_218947 : Nat.Prime 218947 := by
  apply lucas_primality 218947 (2 : ZMod 218947)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 218947 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((401 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 218947)^109473 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 218947)^72982 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 218947)^31278 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (2 : ZMod 218947)^16842 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 401 := Nat.prime_eq_prime_of_dvd_pow hq prime_401 hd
            subst q
            change (2 : ZMod 218947)^546 ≠ 1
            reduce_mod_char
            decide

theorem prime_220189 : Nat.Prime 220189 := by
  apply lucas_primality 220189 (2 : ZMod 220189)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 220189 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((59 : ℕ)^1 * ((311 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 220189)^110094 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 220189)^73396 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (2 : ZMod 220189)^3732 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 311 := Nat.prime_eq_prime_of_dvd_pow hq prime_311 hd
          subst q
          change (2 : ZMod 220189)^708 ≠ 1
          reduce_mod_char
          decide

theorem prime_220783 : Nat.Prime 220783 := by
  apply lucas_primality 220783 (5 : ZMod 220783)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 220783 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((31 : ℕ)^1 * ((1187 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 220783)^110391 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 220783)^73594 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (5 : ZMod 220783)^7122 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1187 := Nat.prime_eq_prime_of_dvd_pow hq prime_1187 hd
          subst q
          change (5 : ZMod 220783)^186 ≠ 1
          reduce_mod_char
          decide

theorem prime_221747 : Nat.Prime 221747 := by
  apply lucas_primality 221747 (2 : ZMod 221747)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 221747 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((47 : ℕ)^1 * ((337 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 221747)^110873 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 221747)^31678 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (2 : ZMod 221747)^4718 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 337 := Nat.prime_eq_prime_of_dvd_pow hq prime_337 hd
          subst q
          change (2 : ZMod 221747)^658 ≠ 1
          reduce_mod_char
          decide

theorem prime_223087 : Nat.Prime 223087 := by
  apply lucas_primality 223087 (7 : ZMod 223087)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 223087 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((37181 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 223087)^111543 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 223087)^74362 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 37181 := Nat.prime_eq_prime_of_dvd_pow hq prime_37181 hd
        subst q
        change (7 : ZMod 223087)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_223361 : Nat.Prime 223361 := by
  apply lucas_primality 223361 (3 : ZMod 223361)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 223361 - 1 = (2 : ℕ)^7 * ((5 : ℕ)^1 * ((349 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 223361)^111680 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 223361)^44672 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 349 := Nat.prime_eq_prime_of_dvd_pow hq prime_349 hd
        subst q
        change (3 : ZMod 223361)^640 ≠ 1
        reduce_mod_char
        decide

theorem prime_223903 : Nat.Prime 223903 := by
  apply lucas_primality 223903 (6 : ZMod 223903)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 223903 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((1777 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 223903)^111951 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 223903)^74634 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 223903)^31986 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1777 := Nat.prime_eq_prime_of_dvd_pow hq prime_1777 hd
          subst q
          change (6 : ZMod 223903)^126 ≠ 1
          reduce_mod_char
          decide

theorem prime_224527 : Nat.Prime 224527 := by
  apply lucas_primality 224527 (5 : ZMod 224527)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 224527 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((1627 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 224527)^112263 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 224527)^74842 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (5 : ZMod 224527)^9762 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1627 := Nat.prime_eq_prime_of_dvd_pow hq prime_1627 hd
          subst q
          change (5 : ZMod 224527)^138 ≠ 1
          reduce_mod_char
          decide

theorem prime_224699 : Nat.Prime 224699 := by
  apply lucas_primality 224699 (2 : ZMod 224699)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 224699 - 1 = (2 : ℕ)^1 * ((112349 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 224699)^112349 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 112349 := Nat.prime_eq_prime_of_dvd_pow hq prime_112349 hd
      subst q
      change (2 : ZMod 224699)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_224881 : Nat.Prime 224881 := by
  apply lucas_primality 224881 (7 : ZMod 224881)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 224881 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((937 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 224881)^112440 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 224881)^74960 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 224881)^44976 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 937 := Nat.prime_eq_prime_of_dvd_pow hq prime_937 hd
          subst q
          change (7 : ZMod 224881)^240 ≠ 1
          reduce_mod_char
          decide

theorem prime_225499 : Nat.Prime 225499 := by
  apply lucas_primality 225499 (10 : ZMod 225499)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 225499 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((13 : ℕ)^1 * ((59 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 225499)^112749 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 225499)^75166 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (10 : ZMod 225499)^32214 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (10 : ZMod 225499)^17346 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
            subst q
            change (10 : ZMod 225499)^3822 ≠ 1
            reduce_mod_char
            decide

theorem prime_226141 : Nat.Prime 226141 := by
  apply lucas_primality 226141 (2 : ZMod 226141)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 226141 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((3769 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 226141)^113070 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 226141)^75380 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 226141)^45228 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3769 := Nat.prime_eq_prime_of_dvd_pow hq prime_3769 hd
          subst q
          change (2 : ZMod 226141)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_227053 : Nat.Prime 227053 := by
  apply lucas_primality 227053 (2 : ZMod 227053)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 227053 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((17 : ℕ)^1 * ((53 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 227053)^113526 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 227053)^75684 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 227053)^32436 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (2 : ZMod 227053)^13356 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
            subst q
            change (2 : ZMod 227053)^4284 ≠ 1
            reduce_mod_char
            decide

theorem prime_227251 : Nat.Prime 227251 := by
  apply lucas_primality 227251 (3 : ZMod 227251)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 227251 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^3 * ((101 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 227251)^113625 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 227251)^75750 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 227251)^45450 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
          subst q
          change (3 : ZMod 227251)^2250 ≠ 1
          reduce_mod_char
          decide

theorem prime_227303 : Nat.Prime 227303 := by
  apply lucas_primality 227303 (5 : ZMod 227303)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 227303 - 1 = (2 : ℕ)^1 * ((29 : ℕ)^1 * ((3919 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 227303)^113651 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (5 : ZMod 227303)^7838 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3919 := Nat.prime_eq_prime_of_dvd_pow hq prime_3919 hd
        subst q
        change (5 : ZMod 227303)^58 ≠ 1
        reduce_mod_char
        decide

theorem prime_227459 : Nat.Prime 227459 := by
  apply lucas_primality 227459 (2 : ZMod 227459)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 227459 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^2 * ((11 : ℕ)^1 * ((211 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 227459)^113729 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 227459)^32494 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 227459)^20678 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 211 := Nat.prime_eq_prime_of_dvd_pow hq prime_211 hd
          subst q
          change (2 : ZMod 227459)^1078 ≠ 1
          reduce_mod_char
          decide

theorem prime_227603 : Nat.Prime 227603 := by
  apply lucas_primality 227603 (2 : ZMod 227603)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 227603 - 1 = (2 : ℕ)^1 * ((31 : ℕ)^1 * ((3671 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 227603)^113801 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (2 : ZMod 227603)^7342 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3671 := Nat.prime_eq_prime_of_dvd_pow hq prime_3671 hd
        subst q
        change (2 : ZMod 227603)^62 ≠ 1
        reduce_mod_char
        decide

theorem prime_227873 : Nat.Prime 227873 := by
  apply lucas_primality 227873 (3 : ZMod 227873)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 227873 - 1 = (2 : ℕ)^5 * ((7121 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 227873)^113936 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 7121 := Nat.prime_eq_prime_of_dvd_pow hq prime_7121 hd
      subst q
      change (3 : ZMod 227873)^32 ≠ 1
      reduce_mod_char
      decide

theorem prime_228023 : Nat.Prime 228023 := by
  apply lucas_primality 228023 (5 : ZMod 228023)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 228023 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((4957 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 228023)^114011 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (5 : ZMod 228023)^9914 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4957 := Nat.prime_eq_prime_of_dvd_pow hq prime_4957 hd
        subst q
        change (5 : ZMod 228023)^46 ≠ 1
        reduce_mod_char
        decide

theorem prime_228251 : Nat.Prime 228251 := by
  apply lucas_primality 228251 (2 : ZMod 228251)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 228251 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^3 * ((11 : ℕ)^1 * ((83 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 228251)^114125 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 228251)^45650 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 228251)^20750 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
          subst q
          change (2 : ZMod 228251)^2750 ≠ 1
          reduce_mod_char
          decide

theorem prime_228469 : Nat.Prime 228469 := by
  apply lucas_primality 228469 (6 : ZMod 228469)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 228469 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((79 : ℕ)^1 * ((241 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 228469)^114234 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 228469)^76156 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (6 : ZMod 228469)^2892 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 241 := Nat.prime_eq_prime_of_dvd_pow hq prime_241 hd
          subst q
          change (6 : ZMod 228469)^948 ≠ 1
          reduce_mod_char
          decide

theorem prime_228509 : Nat.Prime 228509 := by
  apply lucas_primality 228509 (2 : ZMod 228509)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 228509 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((8161 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 228509)^114254 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 228509)^32644 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 8161 := Nat.prime_eq_prime_of_dvd_pow hq prime_8161 hd
        subst q
        change (2 : ZMod 228509)^28 ≠ 1
        reduce_mod_char
        decide

theorem prime_228913 : Nat.Prime 228913 := by
  apply lucas_primality 228913 (5 : ZMod 228913)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 228913 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((251 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 228913)^114456 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 228913)^76304 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (5 : ZMod 228913)^12048 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 251 := Nat.prime_eq_prime_of_dvd_pow hq prime_251 hd
          subst q
          change (5 : ZMod 228913)^912 ≠ 1
          reduce_mod_char
          decide

theorem prime_229283 : Nat.Prime 229283 := by
  apply lucas_primality 229283 (2 : ZMod 229283)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 229283 - 1 = (2 : ℕ)^1 * ((114641 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 229283)^114641 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 114641 := Nat.prime_eq_prime_of_dvd_pow hq prime_114641 hd
      subst q
      change (2 : ZMod 229283)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_229781 : Nat.Prime 229781 := by
  apply lucas_primality 229781 (2 : ZMod 229781)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 229781 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((11489 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 229781)^114890 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 229781)^45956 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 11489 := Nat.prime_eq_prime_of_dvd_pow hq prime_11489 hd
        subst q
        change (2 : ZMod 229781)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_230761 : Nat.Prime 230761 := by
  apply lucas_primality 230761 (13 : ZMod 230761)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 230761 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((641 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 230761)^115380 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 230761)^76920 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 230761)^46152 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 641 := Nat.prime_eq_prime_of_dvd_pow hq prime_641 hd
          subst q
          change (13 : ZMod 230761)^360 ≠ 1
          reduce_mod_char
          decide

theorem prime_233021 : Nat.Prime 233021 := by
  apply lucas_primality 233021 (2 : ZMod 233021)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 233021 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((61 : ℕ)^1 * ((191 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 233021)^116510 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 233021)^46604 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (2 : ZMod 233021)^3820 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
          subst q
          change (2 : ZMod 233021)^1220 ≠ 1
          reduce_mod_char
          decide

theorem prime_233297 : Nat.Prime 233297 := by
  apply lucas_primality 233297 (3 : ZMod 233297)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 233297 - 1 = (2 : ℕ)^4 * ((7 : ℕ)^1 * ((2083 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 233297)^116648 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 233297)^33328 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2083 := Nat.prime_eq_prime_of_dvd_pow hq prime_2083 hd
        subst q
        change (3 : ZMod 233297)^112 ≠ 1
        reduce_mod_char
        decide

theorem prime_233509 : Nat.Prime 233509 := by
  apply lucas_primality 233509 (2 : ZMod 233509)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 233509 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((29 : ℕ)^1 * ((61 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 233509)^116754 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 233509)^77836 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 233509)^21228 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (2 : ZMod 233509)^8052 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
            subst q
            change (2 : ZMod 233509)^3828 ≠ 1
            reduce_mod_char
            decide

theorem prime_234931 : Nat.Prime 234931 := by
  apply lucas_primality 234931 (3 : ZMod 234931)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 234931 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((41 : ℕ)^1 * ((191 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 234931)^117465 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 234931)^78310 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 234931)^46986 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (3 : ZMod 234931)^5730 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
            subst q
            change (3 : ZMod 234931)^1230 ≠ 1
            reduce_mod_char
            decide

theorem prime_235007 : Nat.Prime 235007 := by
  apply lucas_primality 235007 (5 : ZMod 235007)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 235007 - 1 = (2 : ℕ)^1 * ((117503 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 235007)^117503 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 117503 := Nat.prime_eq_prime_of_dvd_pow hq prime_117503 hd
      subst q
      change (5 : ZMod 235007)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_237043 : Nat.Prime 237043 := by
  apply lucas_primality 237043 (3 : ZMod 237043)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 237043 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((13 : ℕ)^1 * ((1013 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 237043)^118521 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 237043)^79014 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 237043)^18234 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1013 := Nat.prime_eq_prime_of_dvd_pow hq prime_1013 hd
          subst q
          change (3 : ZMod 237043)^234 ≠ 1
          reduce_mod_char
          decide

theorem prime_238321 : Nat.Prime 238321 := by
  apply lucas_primality 238321 (13 : ZMod 238321)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 238321 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((331 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 238321)^119160 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 238321)^79440 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 238321)^47664 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 331 := Nat.prime_eq_prime_of_dvd_pow hq prime_331 hd
          subst q
          change (13 : ZMod 238321)^720 ≠ 1
          reduce_mod_char
          decide

theorem prime_238481 : Nat.Prime 238481 := by
  apply lucas_primality 238481 (3 : ZMod 238481)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 238481 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((271 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 238481)^119240 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 238481)^47696 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 238481)^21680 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 271 := Nat.prime_eq_prime_of_dvd_pow hq prime_271 hd
          subst q
          change (3 : ZMod 238481)^880 ≠ 1
          reduce_mod_char
          decide

theorem prime_238727 : Nat.Prime 238727 := by
  apply lucas_primality 238727 (5 : ZMod 238727)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 238727 - 1 = (2 : ℕ)^1 * ((119363 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 238727)^119363 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 119363 := Nat.prime_eq_prime_of_dvd_pow hq prime_119363 hd
      subst q
      change (5 : ZMod 238727)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_239429 : Nat.Prime 239429 := by
  apply lucas_primality 239429 (2 : ZMod 239429)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 239429 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((17 : ℕ)^1 * ((503 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 239429)^119714 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 239429)^34204 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 239429)^14084 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 503 := Nat.prime_eq_prime_of_dvd_pow hq prime_503 hd
          subst q
          change (2 : ZMod 239429)^476 ≠ 1
          reduce_mod_char
          decide

theorem prime_241037 : Nat.Prime 241037 := by
  apply lucas_primality 241037 (2 : ZMod 241037)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 241037 - 1 = (2 : ℕ)^2 * ((60259 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 241037)^120518 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 60259 := Nat.prime_eq_prime_of_dvd_pow hq prime_60259 hd
      subst q
      change (2 : ZMod 241037)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_241667 : Nat.Prime 241667 := by
  apply lucas_primality 241667 (2 : ZMod 241667)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 241667 - 1 = (2 : ℕ)^1 * ((120833 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 241667)^120833 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 120833 := Nat.prime_eq_prime_of_dvd_pow hq prime_120833 hd
      subst q
      change (2 : ZMod 241667)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_242129 : Nat.Prime 242129 := by
  apply lucas_primality 242129 (3 : ZMod 242129)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 242129 - 1 = (2 : ℕ)^4 * ((37 : ℕ)^1 * ((409 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 242129)^121064 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (3 : ZMod 242129)^6544 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 409 := Nat.prime_eq_prime_of_dvd_pow hq prime_409 hd
        subst q
        change (3 : ZMod 242129)^592 ≠ 1
        reduce_mod_char
        decide

theorem prime_243031 : Nat.Prime 243031 := by
  apply lucas_primality 243031 (23 : ZMod 243031)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 243031 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((8101 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (23 : ZMod 243031)^121515 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (23 : ZMod 243031)^81010 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (23 : ZMod 243031)^48606 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 8101 := Nat.prime_eq_prime_of_dvd_pow hq prime_8101 hd
          subst q
          change (23 : ZMod 243031)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_245411 : Nat.Prime 245411 := by
  apply lucas_primality 245411 (2 : ZMod 245411)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 245411 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((23 : ℕ)^1 * ((97 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 245411)^122705 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 245411)^49082 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 245411)^22310 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (2 : ZMod 245411)^10670 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
            subst q
            change (2 : ZMod 245411)^2530 ≠ 1
            reduce_mod_char
            decide

theorem prime_245419 : Nat.Prime 245419 := by
  apply lucas_primality 245419 (2 : ZMod 245419)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 245419 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((40903 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 245419)^122709 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 245419)^81806 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 40903 := Nat.prime_eq_prime_of_dvd_pow hq prime_40903 hd
        subst q
        change (2 : ZMod 245419)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_246167 : Nat.Prime 246167 := by
  apply lucas_primality 246167 (5 : ZMod 246167)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 246167 - 1 = (2 : ℕ)^1 * ((123083 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 246167)^123083 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 123083 := Nat.prime_eq_prime_of_dvd_pow hq prime_123083 hd
      subst q
      change (5 : ZMod 246167)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_247781 : Nat.Prime 247781 := by
  apply lucas_primality 247781 (2 : ZMod 247781)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 247781 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((953 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 247781)^123890 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 247781)^49556 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 247781)^19060 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 953 := Nat.prime_eq_prime_of_dvd_pow hq prime_953 hd
          subst q
          change (2 : ZMod 247781)^260 ≠ 1
          reduce_mod_char
          decide

theorem prime_248071 : Nat.Prime 248071 := by
  apply lucas_primality 248071 (3 : ZMod 248071)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 248071 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((8269 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 248071)^124035 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 248071)^82690 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 248071)^49614 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 8269 := Nat.prime_eq_prime_of_dvd_pow hq prime_8269 hd
          subst q
          change (3 : ZMod 248071)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_249503 : Nat.Prime 249503 := by
  apply lucas_primality 249503 (5 : ZMod 249503)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 249503 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^2 * ((1031 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 249503)^124751 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 249503)^22682 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1031 := Nat.prime_eq_prime_of_dvd_pow hq prime_1031 hd
        subst q
        change (5 : ZMod 249503)^242 ≠ 1
        reduce_mod_char
        decide

theorem prime_250049 : Nat.Prime 250049 := by
  apply lucas_primality 250049 (3 : ZMod 250049)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 250049 - 1 = (2 : ℕ)^6 * ((3907 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 250049)^125024 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3907 := Nat.prime_eq_prime_of_dvd_pow hq prime_3907 hd
      subst q
      change (3 : ZMod 250049)^64 ≠ 1
      reduce_mod_char
      decide

theorem prime_250073 : Nat.Prime 250073 := by
  apply lucas_primality 250073 (3 : ZMod 250073)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 250073 - 1 = (2 : ℕ)^3 * ((31259 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 250073)^125036 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 31259 := Nat.prime_eq_prime_of_dvd_pow hq prime_31259 hd
      subst q
      change (3 : ZMod 250073)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_250993 : Nat.Prime 250993 := by
  apply lucas_primality 250993 (5 : ZMod 250993)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 250993 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((83 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 250993)^125496 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 250993)^83664 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 250993)^35856 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
          subst q
          change (5 : ZMod 250993)^3024 ≠ 1
          reduce_mod_char
          decide

theorem prime_252001 : Nat.Prime 252001 := by
  apply lucas_primality 252001 (11 : ZMod 252001)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 252001 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^2 * ((5 : ℕ)^3 * ((7 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 252001)^126000 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 252001)^84000 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 252001)^50400 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (11 : ZMod 252001)^36000 ≠ 1
          reduce_mod_char
          decide

theorem prime_253789 : Nat.Prime 253789 := by
  apply lucas_primality 253789 (2 : ZMod 253789)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 253789 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((21149 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 253789)^126894 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 253789)^84596 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 21149 := Nat.prime_eq_prime_of_dvd_pow hq prime_21149 hd
        subst q
        change (2 : ZMod 253789)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_256121 : Nat.Prime 256121 := by
  apply lucas_primality 256121 (3 : ZMod 256121)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 256121 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((19 : ℕ)^1 * ((337 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 256121)^128060 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 256121)^51224 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (3 : ZMod 256121)^13480 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 337 := Nat.prime_eq_prime_of_dvd_pow hq prime_337 hd
          subst q
          change (3 : ZMod 256121)^760 ≠ 1
          reduce_mod_char
          decide

theorem prime_257281 : Nat.Prime 257281 := by
  apply lucas_primality 257281 (7 : ZMod 257281)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 257281 - 1 = (2 : ℕ)^8 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((67 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 257281)^128640 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 257281)^85760 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 257281)^51456 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (7 : ZMod 257281)^3840 ≠ 1
          reduce_mod_char
          decide

theorem prime_257401 : Nat.Prime 257401 := by
  apply lucas_primality 257401 (29 : ZMod 257401)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 257401 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((5 : ℕ)^2 * ((11 : ℕ)^1 * ((13 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (29 : ZMod 257401)^128700 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (29 : ZMod 257401)^85800 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (29 : ZMod 257401)^51480 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (29 : ZMod 257401)^23400 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (29 : ZMod 257401)^19800 ≠ 1
            reduce_mod_char
            decide

theorem prime_258521 : Nat.Prime 258521 := by
  apply lucas_primality 258521 (11 : ZMod 258521)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 258521 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((23 : ℕ)^1 * ((281 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 258521)^129260 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 258521)^51704 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (11 : ZMod 258521)^11240 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 281 := Nat.prime_eq_prime_of_dvd_pow hq prime_281 hd
          subst q
          change (11 : ZMod 258521)^920 ≠ 1
          reduce_mod_char
          decide

theorem prime_259771 : Nat.Prime 259771 := by
  apply lucas_primality 259771 (2 : ZMod 259771)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 259771 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((1237 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 259771)^129885 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 259771)^86590 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 259771)^51954 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (2 : ZMod 259771)^37110 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1237 := Nat.prime_eq_prime_of_dvd_pow hq prime_1237 hd
            subst q
            change (2 : ZMod 259771)^210 ≠ 1
            reduce_mod_char
            decide

theorem prime_260017 : Nat.Prime 260017 := by
  apply lucas_primality 260017 (5 : ZMod 260017)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 260017 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((5417 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 260017)^130008 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 260017)^86672 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5417 := Nat.prime_eq_prime_of_dvd_pow hq prime_5417 hd
        subst q
        change (5 : ZMod 260017)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_261887 : Nat.Prime 261887 := by
  apply lucas_primality 261887 (5 : ZMod 261887)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 261887 - 1 = (2 : ℕ)^1 * ((37 : ℕ)^1 * ((3539 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 261887)^130943 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (5 : ZMod 261887)^7078 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3539 := Nat.prime_eq_prime_of_dvd_pow hq prime_3539 hd
        subst q
        change (5 : ZMod 261887)^74 ≠ 1
        reduce_mod_char
        decide

theorem prime_262139 : Nat.Prime 262139 := by
  apply lucas_primality 262139 (2 : ZMod 262139)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 262139 - 1 = (2 : ℕ)^1 * ((53 : ℕ)^1 * ((2473 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 262139)^131069 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
        subst q
        change (2 : ZMod 262139)^4946 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2473 := Nat.prime_eq_prime_of_dvd_pow hq prime_2473 hd
        subst q
        change (2 : ZMod 262139)^106 ≠ 1
        reduce_mod_char
        decide

theorem prime_262147 : Nat.Prime 262147 := by
  apply lucas_primality 262147 (2 : ZMod 262147)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 262147 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((43691 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 262147)^131073 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 262147)^87382 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 43691 := Nat.prime_eq_prime_of_dvd_pow hq prime_43691 hd
        subst q
        change (2 : ZMod 262147)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_262657 : Nat.Prime 262657 := by
  apply lucas_primality 262657 (5 : ZMod 262657)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 262657 - 1 = (2 : ℕ)^9 * ((3 : ℕ)^3 * ((19 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 262657)^131328 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 262657)^87552 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (5 : ZMod 262657)^13824 ≠ 1
        reduce_mod_char
        decide

theorem prime_263737 : Nat.Prime 263737 := by
  apply lucas_primality 263737 (14 : ZMod 263737)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 263737 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^4 * ((11 : ℕ)^1 * ((37 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 263737)^131868 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 263737)^87912 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (14 : ZMod 263737)^23976 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (14 : ZMod 263737)^7128 ≠ 1
          reduce_mod_char
          decide

theorem prime_266221 : Nat.Prime 266221 := by
  apply lucas_primality 266221 (10 : ZMod 266221)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 266221 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((29 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 266221)^133110 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 266221)^88740 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 266221)^53244 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (10 : ZMod 266221)^15660 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (10 : ZMod 266221)^9180 ≠ 1
            reduce_mod_char
            decide

theorem prime_267233 : Nat.Prime 267233 := by
  apply lucas_primality 267233 (3 : ZMod 267233)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 267233 - 1 = (2 : ℕ)^5 * ((7 : ℕ)^1 * ((1193 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 267233)^133616 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 267233)^38176 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1193 := Nat.prime_eq_prime_of_dvd_pow hq prime_1193 hd
        subst q
        change (3 : ZMod 267233)^224 ≠ 1
        reduce_mod_char
        decide

theorem prime_267677 : Nat.Prime 267677 := by
  apply lucas_primality 267677 (2 : ZMod 267677)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 267677 - 1 = (2 : ℕ)^2 * ((66919 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 267677)^133838 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 66919 := Nat.prime_eq_prime_of_dvd_pow hq prime_66919 hd
      subst q
      change (2 : ZMod 267677)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_269473 : Nat.Prime 269473 := by
  apply lucas_primality 269473 (5 : ZMod 269473)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 269473 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((401 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 269473)^134736 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 269473)^89824 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 269473)^38496 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 401 := Nat.prime_eq_prime_of_dvd_pow hq prime_401 hd
          subst q
          change (5 : ZMod 269473)^672 ≠ 1
          reduce_mod_char
          decide

theorem prime_269701 : Nat.Prime 269701 := by
  apply lucas_primality 269701 (7 : ZMod 269701)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 269701 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((29 : ℕ)^1 * ((31 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 269701)^134850 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 269701)^89900 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 269701)^53940 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (7 : ZMod 269701)^9300 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (7 : ZMod 269701)^8700 ≠ 1
            reduce_mod_char
            decide

theorem prime_269887 : Nat.Prime 269887 := by
  apply lucas_primality 269887 (3 : ZMod 269887)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 269887 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((31 : ℕ)^1 * ((1451 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 269887)^134943 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 269887)^89962 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (3 : ZMod 269887)^8706 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1451 := Nat.prime_eq_prime_of_dvd_pow hq prime_1451 hd
          subst q
          change (3 : ZMod 269887)^186 ≠ 1
          reduce_mod_char
          decide

theorem prime_270059 : Nat.Prime 270059 := by
  apply lucas_primality 270059 (2 : ZMod 270059)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 270059 - 1 = (2 : ℕ)^1 * ((135029 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 270059)^135029 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 135029 := Nat.prime_eq_prime_of_dvd_pow hq prime_135029 hd
      subst q
      change (2 : ZMod 270059)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_271861 : Nat.Prime 271861 := by
  apply lucas_primality 271861 (2 : ZMod 271861)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 271861 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((23 : ℕ)^1 * ((197 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 271861)^135930 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 271861)^90620 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 271861)^54372 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (2 : ZMod 271861)^11820 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
            subst q
            change (2 : ZMod 271861)^1380 ≠ 1
            reduce_mod_char
            decide

theorem prime_273283 : Nat.Prime 273283 := by
  apply lucas_primality 273283 (2 : ZMod 273283)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 273283 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((37 : ℕ)^1 * ((1231 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 273283)^136641 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 273283)^91094 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (2 : ZMod 273283)^7386 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1231 := Nat.prime_eq_prime_of_dvd_pow hq prime_1231 hd
          subst q
          change (2 : ZMod 273283)^222 ≠ 1
          reduce_mod_char
          decide

theorem prime_273929 : Nat.Prime 273929 := by
  apply lucas_primality 273929 (3 : ZMod 273929)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 273929 - 1 = (2 : ℕ)^3 * ((97 : ℕ)^1 * ((353 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 273929)^136964 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
        subst q
        change (3 : ZMod 273929)^2824 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 353 := Nat.prime_eq_prime_of_dvd_pow hq prime_353 hd
        subst q
        change (3 : ZMod 273929)^776 ≠ 1
        reduce_mod_char
        decide

theorem prime_274201 : Nat.Prime 274201 := by
  apply lucas_primality 274201 (19 : ZMod 274201)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 274201 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((457 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 274201)^137100 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 274201)^91400 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (19 : ZMod 274201)^54840 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 457 := Nat.prime_eq_prime_of_dvd_pow hq prime_457 hd
          subst q
          change (19 : ZMod 274201)^600 ≠ 1
          reduce_mod_char
          decide

theorem prime_275447 : Nat.Prime 275447 := by
  apply lucas_primality 275447 (5 : ZMod 275447)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 275447 - 1 = (2 : ℕ)^1 * ((137723 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 275447)^137723 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 137723 := Nat.prime_eq_prime_of_dvd_pow hq prime_137723 hd
      subst q
      change (5 : ZMod 275447)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_275593 : Nat.Prime 275593 := by
  apply lucas_primality 275593 (5 : ZMod 275593)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 275593 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((11483 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 275593)^137796 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 275593)^91864 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 11483 := Nat.prime_eq_prime_of_dvd_pow hq prime_11483 hd
        subst q
        change (5 : ZMod 275593)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_275941 : Nat.Prime 275941 := by
  apply lucas_primality 275941 (6 : ZMod 275941)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 275941 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((73 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 275941)^137970 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 275941)^91980 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 275941)^55188 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (6 : ZMod 275941)^39420 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
            subst q
            change (6 : ZMod 275941)^3780 ≠ 1
            reduce_mod_char
            decide

theorem prime_277213 : Nat.Prime 277213 := by
  apply lucas_primality 277213 (2 : ZMod 277213)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 277213 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((1777 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 277213)^138606 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 277213)^92404 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 277213)^21324 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1777 := Nat.prime_eq_prime_of_dvd_pow hq prime_1777 hd
          subst q
          change (2 : ZMod 277213)^156 ≠ 1
          reduce_mod_char
          decide

theorem prime_277889 : Nat.Prime 277889 := by
  apply lucas_primality 277889 (3 : ZMod 277889)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 277889 - 1 = (2 : ℕ)^7 * ((13 : ℕ)^1 * ((167 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 277889)^138944 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 277889)^21376 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
        subst q
        change (3 : ZMod 277889)^1664 ≠ 1
        reduce_mod_char
        decide

theorem prime_278261 : Nat.Prime 278261 := by
  apply lucas_primality 278261 (2 : ZMod 278261)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 278261 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((13913 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 278261)^139130 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 278261)^55652 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13913 := Nat.prime_eq_prime_of_dvd_pow hq prime_13913 hd
        subst q
        change (2 : ZMod 278261)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_278363 : Nat.Prime 278363 := by
  apply lucas_primality 278363 (2 : ZMod 278363)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 278363 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((59 : ℕ)^1 * ((337 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 278363)^139181 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 278363)^39766 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (2 : ZMod 278363)^4718 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 337 := Nat.prime_eq_prime_of_dvd_pow hq prime_337 hd
          subst q
          change (2 : ZMod 278363)^826 ≠ 1
          reduce_mod_char
          decide

theorem prime_279553 : Nat.Prime 279553 := by
  apply lucas_primality 279553 (10 : ZMod 279553)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 279553 - 1 = (2 : ℕ)^10 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 279553)^139776 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 279553)^93184 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (10 : ZMod 279553)^39936 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (10 : ZMod 279553)^21504 ≠ 1
          reduce_mod_char
          decide

theorem prime_279991 : Nat.Prime 279991 := by
  apply lucas_primality 279991 (15 : ZMod 279991)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 279991 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((61 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (15 : ZMod 279991)^139995 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (15 : ZMod 279991)^93330 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (15 : ZMod 279991)^55998 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (15 : ZMod 279991)^16470 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
            subst q
            change (15 : ZMod 279991)^4590 ≠ 1
            reduce_mod_char
            decide

theorem prime_280409 : Nat.Prime 280409 := by
  apply lucas_primality 280409 (3 : ZMod 280409)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 280409 - 1 = (2 : ℕ)^3 * ((35051 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 280409)^140204 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 35051 := Nat.prime_eq_prime_of_dvd_pow hq prime_35051 hd
      subst q
      change (3 : ZMod 280409)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_282481 : Nat.Prime 282481 := by
  apply lucas_primality 282481 (28 : ZMod 282481)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 282481 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((107 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (28 : ZMod 282481)^141240 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (28 : ZMod 282481)^94160 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (28 : ZMod 282481)^56496 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (28 : ZMod 282481)^25680 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
            subst q
            change (28 : ZMod 282481)^2640 ≠ 1
            reduce_mod_char
            decide

theorem prime_283489 : Nat.Prime 283489 := by
  apply lucas_primality 283489 (7 : ZMod 283489)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 283489 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((2953 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 283489)^141744 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 283489)^94496 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2953 := Nat.prime_eq_prime_of_dvd_pow hq prime_2953 hd
        subst q
        change (7 : ZMod 283489)^96 ≠ 1
        reduce_mod_char
        decide

theorem prime_285827 : Nat.Prime 285827 := by
  apply lucas_primality 285827 (2 : ZMod 285827)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 285827 - 1 = (2 : ℕ)^1 * ((241 : ℕ)^1 * ((593 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 285827)^142913 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 241 := Nat.prime_eq_prime_of_dvd_pow hq prime_241 hd
        subst q
        change (2 : ZMod 285827)^1186 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 593 := Nat.prime_eq_prime_of_dvd_pow hq prime_593 hd
        subst q
        change (2 : ZMod 285827)^482 ≠ 1
        reduce_mod_char
        decide

theorem prime_287117 : Nat.Prime 287117 := by
  apply lucas_primality 287117 (2 : ZMod 287117)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 287117 - 1 = (2 : ℕ)^2 * ((179 : ℕ)^1 * ((401 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 287117)^143558 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 179 := Nat.prime_eq_prime_of_dvd_pow hq prime_179 hd
        subst q
        change (2 : ZMod 287117)^1604 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 401 := Nat.prime_eq_prime_of_dvd_pow hq prime_401 hd
        subst q
        change (2 : ZMod 287117)^716 ≠ 1
        reduce_mod_char
        decide

theorem prime_290041 : Nat.Prime 290041 := by
  apply lucas_primality 290041 (35 : ZMod 290041)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 290041 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((2417 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (35 : ZMod 290041)^145020 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (35 : ZMod 290041)^96680 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (35 : ZMod 290041)^58008 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2417 := Nat.prime_eq_prime_of_dvd_pow hq prime_2417 hd
          subst q
          change (35 : ZMod 290041)^120 ≠ 1
          reduce_mod_char
          decide

theorem prime_292141 : Nat.Prime 292141 := by
  apply lucas_primality 292141 (7 : ZMod 292141)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 292141 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((541 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 292141)^146070 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 292141)^97380 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 292141)^58428 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 541 := Nat.prime_eq_prime_of_dvd_pow hq prime_541 hd
          subst q
          change (7 : ZMod 292141)^540 ≠ 1
          reduce_mod_char
          decide

theorem prime_292549 : Nat.Prime 292549 := by
  apply lucas_primality 292549 (2 : ZMod 292549)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 292549 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((24379 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 292549)^146274 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 292549)^97516 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 24379 := Nat.prime_eq_prime_of_dvd_pow hq prime_24379 hd
        subst q
        change (2 : ZMod 292549)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_292777 : Nat.Prime 292777 := by
  apply lucas_primality 292777 (5 : ZMod 292777)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 292777 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((1109 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 292777)^146388 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 292777)^97592 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 292777)^26616 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1109 := Nat.prime_eq_prime_of_dvd_pow hq prime_1109 hd
          subst q
          change (5 : ZMod 292777)^264 ≠ 1
          reduce_mod_char
          decide

theorem prime_297067 : Nat.Prime 297067 := by
  apply lucas_primality 297067 (2 : ZMod 297067)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 297067 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((643 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 297067)^148533 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 297067)^99022 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 297067)^42438 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (2 : ZMod 297067)^27006 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 643 := Nat.prime_eq_prime_of_dvd_pow hq prime_643 hd
            subst q
            change (2 : ZMod 297067)^462 ≠ 1
            reduce_mod_char
            decide

theorem prime_299711 : Nat.Prime 299711 := by
  apply lucas_primality 299711 (11 : ZMod 299711)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 299711 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((41 : ℕ)^1 * ((43 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 299711)^149855 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 299711)^59942 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (11 : ZMod 299711)^17630 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (11 : ZMod 299711)^7310 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (11 : ZMod 299711)^6970 ≠ 1
            reduce_mod_char
            decide

theorem prime_300301 : Nat.Prime 300301 := by
  apply lucas_primality 300301 (2 : ZMod 300301)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 300301 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 300301)^150150 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 300301)^100100 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 300301)^60060 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (2 : ZMod 300301)^42900 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
              subst q
              change (2 : ZMod 300301)^27300 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
              subst q
              change (2 : ZMod 300301)^23100 ≠ 1
              reduce_mod_char
              decide

theorem prime_300733 : Nat.Prime 300733 := by
  apply lucas_primality 300733 (5 : ZMod 300733)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 300733 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((1319 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 300733)^150366 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 300733)^100244 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (5 : ZMod 300733)^15828 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1319 := Nat.prime_eq_prime_of_dvd_pow hq prime_1319 hd
          subst q
          change (5 : ZMod 300733)^228 ≠ 1
          reduce_mod_char
          decide

theorem prime_301181 : Nat.Prime 301181 := by
  apply lucas_primality 301181 (3 : ZMod 301181)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 301181 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((37 : ℕ)^2))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 301181)^150590 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 301181)^60236 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 301181)^27380 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (3 : ZMod 301181)^8140 ≠ 1
          reduce_mod_char
          decide

theorem prime_301997 : Nat.Prime 301997 := by
  apply lucas_primality 301997 (2 : ZMod 301997)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 301997 - 1 = (2 : ℕ)^2 * ((103 : ℕ)^1 * ((733 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 301997)^150998 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
        subst q
        change (2 : ZMod 301997)^2932 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 733 := Nat.prime_eq_prime_of_dvd_pow hq prime_733 hd
        subst q
        change (2 : ZMod 301997)^412 ≠ 1
        reduce_mod_char
        decide

theorem prime_302567 : Nat.Prime 302567 := by
  apply lucas_primality 302567 (5 : ZMod 302567)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 302567 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((809 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 302567)^151283 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 302567)^27506 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (5 : ZMod 302567)^17798 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 809 := Nat.prime_eq_prime_of_dvd_pow hq prime_809 hd
          subst q
          change (5 : ZMod 302567)^374 ≠ 1
          reduce_mod_char
          decide

theorem prime_302579 : Nat.Prime 302579 := by
  apply lucas_primality 302579 (2 : ZMod 302579)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 302579 - 1 = (2 : ℕ)^1 * ((151289 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 302579)^151289 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 151289 := Nat.prime_eq_prime_of_dvd_pow hq prime_151289 hd
      subst q
      change (2 : ZMod 302579)^2 ≠ 1
      reduce_mod_char
      decide

end LegendreK6.Pratt
