import LegendreK6.Pratt.Block003

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LegendreK6.Pratt

theorem prime_9413 : Nat.Prime 9413 := by
  apply lucas_primality 9413 (3 : ZMod 9413)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9413 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((181 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 9413)^4706 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 9413)^724 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 181 := Nat.prime_eq_prime_of_dvd_pow hq prime_181 hd
        subst q
        change (3 : ZMod 9413)^52 ≠ 1
        reduce_mod_char
        decide

theorem prime_9421 : Nat.Prime 9421 := by
  apply lucas_primality 9421 (2 : ZMod 9421)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9421 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((157 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9421)^4710 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 9421)^3140 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 9421)^1884 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
          subst q
          change (2 : ZMod 9421)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_9433 : Nat.Prime 9433 := by
  apply lucas_primality 9433 (5 : ZMod 9433)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9433 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((131 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 9433)^4716 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 9433)^3144 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
        subst q
        change (5 : ZMod 9433)^72 ≠ 1
        reduce_mod_char
        decide

theorem prime_9437 : Nat.Prime 9437 := by
  apply lucas_primality 9437 (2 : ZMod 9437)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9437 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((337 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9437)^4718 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 9437)^1348 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 337 := Nat.prime_eq_prime_of_dvd_pow hq prime_337 hd
        subst q
        change (2 : ZMod 9437)^28 ≠ 1
        reduce_mod_char
        decide

theorem prime_9463 : Nat.Prime 9463 := by
  apply lucas_primality 9463 (3 : ZMod 9463)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9463 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((83 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 9463)^4731 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 9463)^3154 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (3 : ZMod 9463)^498 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
          subst q
          change (3 : ZMod 9463)^114 ≠ 1
          reduce_mod_char
          decide

theorem prime_9479 : Nat.Prime 9479 := by
  apply lucas_primality 9479 (7 : ZMod 9479)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9479 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((677 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 9479)^4739 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 9479)^1354 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 677 := Nat.prime_eq_prime_of_dvd_pow hq prime_677 hd
        subst q
        change (7 : ZMod 9479)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_9497 : Nat.Prime 9497 := by
  apply lucas_primality 9497 (3 : ZMod 9497)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9497 - 1 = (2 : ℕ)^3 * ((1187 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 9497)^4748 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1187 := Nat.prime_eq_prime_of_dvd_pow hq prime_1187 hd
      subst q
      change (3 : ZMod 9497)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_9521 : Nat.Prime 9521 := by
  apply lucas_primality 9521 (3 : ZMod 9521)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9521 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((17 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 9521)^4760 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 9521)^1904 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 9521)^1360 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (3 : ZMod 9521)^560 ≠ 1
          reduce_mod_char
          decide

theorem prime_9539 : Nat.Prime 9539 := by
  apply lucas_primality 9539 (2 : ZMod 9539)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9539 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((251 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9539)^4769 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 9539)^502 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 251 := Nat.prime_eq_prime_of_dvd_pow hq prime_251 hd
        subst q
        change (2 : ZMod 9539)^38 ≠ 1
        reduce_mod_char
        decide

theorem prime_9601 : Nat.Prime 9601 := by
  apply lucas_primality 9601 (13 : ZMod 9601)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9601 - 1 = (2 : ℕ)^7 * ((3 : ℕ)^1 * ((5 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 9601)^4800 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 9601)^3200 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (13 : ZMod 9601)^1920 ≠ 1
        reduce_mod_char
        decide

theorem prime_9613 : Nat.Prime 9613 := by
  apply lucas_primality 9613 (2 : ZMod 9613)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9613 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((89 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9613)^4806 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 9613)^3204 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
        subst q
        change (2 : ZMod 9613)^108 ≠ 1
        reduce_mod_char
        decide

theorem prime_9619 : Nat.Prime 9619 := by
  apply lucas_primality 9619 (2 : ZMod 9619)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9619 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((229 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9619)^4809 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 9619)^3206 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 9619)^1374 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 229 := Nat.prime_eq_prime_of_dvd_pow hq prime_229 hd
          subst q
          change (2 : ZMod 9619)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_9661 : Nat.Prime 9661 := by
  apply lucas_primality 9661 (2 : ZMod 9661)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9661 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((23 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9661)^4830 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 9661)^3220 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 9661)^1932 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (2 : ZMod 9661)^1380 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (2 : ZMod 9661)^420 ≠ 1
            reduce_mod_char
            decide

theorem prime_9679 : Nat.Prime 9679 := by
  apply lucas_primality 9679 (3 : ZMod 9679)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9679 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1613 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 9679)^4839 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 9679)^3226 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1613 := Nat.prime_eq_prime_of_dvd_pow hq prime_1613 hd
        subst q
        change (3 : ZMod 9679)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_9749 : Nat.Prime 9749 := by
  apply lucas_primality 9749 (2 : ZMod 9749)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9749 - 1 = (2 : ℕ)^2 * ((2437 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9749)^4874 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 2437 := Nat.prime_eq_prime_of_dvd_pow hq prime_2437 hd
      subst q
      change (2 : ZMod 9749)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_9767 : Nat.Prime 9767 := by
  apply lucas_primality 9767 (5 : ZMod 9767)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9767 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((257 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 9767)^4883 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (5 : ZMod 9767)^514 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 257 := Nat.prime_eq_prime_of_dvd_pow hq prime_257 hd
        subst q
        change (5 : ZMod 9767)^38 ≠ 1
        reduce_mod_char
        decide

theorem prime_9781 : Nat.Prime 9781 := by
  apply lucas_primality 9781 (6 : ZMod 9781)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9781 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((163 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 9781)^4890 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 9781)^3260 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 9781)^1956 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
          subst q
          change (6 : ZMod 9781)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_9803 : Nat.Prime 9803 := by
  apply lucas_primality 9803 (2 : ZMod 9803)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9803 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^2 * ((29 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9803)^4901 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 9803)^754 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (2 : ZMod 9803)^338 ≠ 1
        reduce_mod_char
        decide

theorem prime_9829 : Nat.Prime 9829 := by
  apply lucas_primality 9829 (10 : ZMod 9829)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9829 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((13 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 9829)^4914 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 9829)^3276 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (10 : ZMod 9829)^1404 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (10 : ZMod 9829)^756 ≠ 1
          reduce_mod_char
          decide

theorem prime_9839 : Nat.Prime 9839 := by
  apply lucas_primality 9839 (7 : ZMod 9839)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9839 - 1 = (2 : ℕ)^1 * ((4919 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 9839)^4919 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 4919 := Nat.prime_eq_prime_of_dvd_pow hq prime_4919 hd
      subst q
      change (7 : ZMod 9839)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_9851 : Nat.Prime 9851 := by
  apply lucas_primality 9851 (2 : ZMod 9851)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9851 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((197 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9851)^4925 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 9851)^1970 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
        subst q
        change (2 : ZMod 9851)^50 ≠ 1
        reduce_mod_char
        decide

theorem prime_9871 : Nat.Prime 9871 := by
  apply lucas_primality 9871 (3 : ZMod 9871)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9871 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((47 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 9871)^4935 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 9871)^3290 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 9871)^1974 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (3 : ZMod 9871)^1410 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
            subst q
            change (3 : ZMod 9871)^210 ≠ 1
            reduce_mod_char
            decide

theorem prime_9901 : Nat.Prime 9901 := by
  apply lucas_primality 9901 (2 : ZMod 9901)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9901 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^2 * ((11 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9901)^4950 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 9901)^3300 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 9901)^1980 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 9901)^900 ≠ 1
          reduce_mod_char
          decide

theorem prime_9907 : Nat.Prime 9907 := by
  apply lucas_primality 9907 (2 : ZMod 9907)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9907 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((127 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9907)^4953 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 9907)^3302 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 9907)^762 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
          subst q
          change (2 : ZMod 9907)^78 ≠ 1
          reduce_mod_char
          decide

theorem prime_9929 : Nat.Prime 9929 := by
  apply lucas_primality 9929 (3 : ZMod 9929)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9929 - 1 = (2 : ℕ)^3 * ((17 : ℕ)^1 * ((73 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 9929)^4964 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (3 : ZMod 9929)^584 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
        subst q
        change (3 : ZMod 9929)^136 ≠ 1
        reduce_mod_char
        decide

theorem prime_9931 : Nat.Prime 9931 := by
  apply lucas_primality 9931 (10 : ZMod 9931)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9931 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((331 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 9931)^4965 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 9931)^3310 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 9931)^1986 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 331 := Nat.prime_eq_prime_of_dvd_pow hq prime_331 hd
          subst q
          change (10 : ZMod 9931)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_9941 : Nat.Prime 9941 := by
  apply lucas_primality 9941 (2 : ZMod 9941)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9941 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((71 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9941)^4970 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 9941)^1988 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 9941)^1420 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
          subst q
          change (2 : ZMod 9941)^140 ≠ 1
          reduce_mod_char
          decide

theorem prime_9949 : Nat.Prime 9949 := by
  apply lucas_primality 9949 (2 : ZMod 9949)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9949 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((829 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9949)^4974 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 9949)^3316 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 829 := Nat.prime_eq_prime_of_dvd_pow hq prime_829 hd
        subst q
        change (2 : ZMod 9949)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_9967 : Nat.Prime 9967 := by
  apply lucas_primality 9967 (3 : ZMod 9967)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9967 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((151 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 9967)^4983 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 9967)^3322 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 9967)^906 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
          subst q
          change (3 : ZMod 9967)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_10009 : Nat.Prime 10009 := by
  apply lucas_primality 10009 (11 : ZMod 10009)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10009 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((139 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 10009)^5004 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 10009)^3336 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
        subst q
        change (11 : ZMod 10009)^72 ≠ 1
        reduce_mod_char
        decide

theorem prime_10061 : Nat.Prime 10061 := by
  apply lucas_primality 10061 (3 : ZMod 10061)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10061 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((503 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 10061)^5030 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 10061)^2012 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 503 := Nat.prime_eq_prime_of_dvd_pow hq prime_503 hd
        subst q
        change (3 : ZMod 10061)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_10069 : Nat.Prime 10069 := by
  apply lucas_primality 10069 (2 : ZMod 10069)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10069 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((839 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 10069)^5034 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 10069)^3356 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 839 := Nat.prime_eq_prime_of_dvd_pow hq prime_839 hd
        subst q
        change (2 : ZMod 10069)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_10079 : Nat.Prime 10079 := by
  apply lucas_primality 10079 (11 : ZMod 10079)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10079 - 1 = (2 : ℕ)^1 * ((5039 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 10079)^5039 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 5039 := Nat.prime_eq_prime_of_dvd_pow hq prime_5039 hd
      subst q
      change (11 : ZMod 10079)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_10091 : Nat.Prime 10091 := by
  apply lucas_primality 10091 (2 : ZMod 10091)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10091 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((1009 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 10091)^5045 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 10091)^2018 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1009 := Nat.prime_eq_prime_of_dvd_pow hq prime_1009 hd
        subst q
        change (2 : ZMod 10091)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_10093 : Nat.Prime 10093 := by
  apply lucas_primality 10093 (2 : ZMod 10093)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10093 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((29 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 10093)^5046 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 10093)^3364 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (2 : ZMod 10093)^348 ≠ 1
        reduce_mod_char
        decide

theorem prime_10111 : Nat.Prime 10111 := by
  apply lucas_primality 10111 (12 : ZMod 10111)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10111 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((337 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (12 : ZMod 10111)^5055 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (12 : ZMod 10111)^3370 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (12 : ZMod 10111)^2022 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 337 := Nat.prime_eq_prime_of_dvd_pow hq prime_337 hd
          subst q
          change (12 : ZMod 10111)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_10133 : Nat.Prime 10133 := by
  apply lucas_primality 10133 (2 : ZMod 10133)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10133 - 1 = (2 : ℕ)^2 * ((17 : ℕ)^1 * ((149 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 10133)^5066 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 10133)^596 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
        subst q
        change (2 : ZMod 10133)^68 ≠ 1
        reduce_mod_char
        decide

theorem prime_10139 : Nat.Prime 10139 := by
  apply lucas_primality 10139 (2 : ZMod 10139)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10139 - 1 = (2 : ℕ)^1 * ((37 : ℕ)^1 * ((137 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 10139)^5069 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (2 : ZMod 10139)^274 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
        subst q
        change (2 : ZMod 10139)^74 ≠ 1
        reduce_mod_char
        decide

theorem prime_10159 : Nat.Prime 10159 := by
  apply lucas_primality 10159 (3 : ZMod 10159)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10159 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1693 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 10159)^5079 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 10159)^3386 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1693 := Nat.prime_eq_prime_of_dvd_pow hq prime_1693 hd
        subst q
        change (3 : ZMod 10159)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_10253 : Nat.Prime 10253 := by
  apply lucas_primality 10253 (2 : ZMod 10253)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10253 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((233 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 10253)^5126 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 10253)^932 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
        subst q
        change (2 : ZMod 10253)^44 ≠ 1
        reduce_mod_char
        decide

theorem prime_10273 : Nat.Prime 10273 := by
  apply lucas_primality 10273 (10 : ZMod 10273)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10273 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((107 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 10273)^5136 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 10273)^3424 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
        subst q
        change (10 : ZMod 10273)^96 ≠ 1
        reduce_mod_char
        decide

theorem prime_10301 : Nat.Prime 10301 := by
  apply lucas_primality 10301 (2 : ZMod 10301)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10301 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((103 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 10301)^5150 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 10301)^2060 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
        subst q
        change (2 : ZMod 10301)^100 ≠ 1
        reduce_mod_char
        decide

theorem prime_10313 : Nat.Prime 10313 := by
  apply lucas_primality 10313 (3 : ZMod 10313)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10313 - 1 = (2 : ℕ)^3 * ((1289 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 10313)^5156 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1289 := Nat.prime_eq_prime_of_dvd_pow hq prime_1289 hd
      subst q
      change (3 : ZMod 10313)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_10331 : Nat.Prime 10331 := by
  apply lucas_primality 10331 (2 : ZMod 10331)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10331 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((1033 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 10331)^5165 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 10331)^2066 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1033 := Nat.prime_eq_prime_of_dvd_pow hq prime_1033 hd
        subst q
        change (2 : ZMod 10331)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_10399 : Nat.Prime 10399 := by
  apply lucas_primality 10399 (6 : ZMod 10399)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10399 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1733 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 10399)^5199 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 10399)^3466 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1733 := Nat.prime_eq_prime_of_dvd_pow hq prime_1733 hd
        subst q
        change (6 : ZMod 10399)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_10433 : Nat.Prime 10433 := by
  apply lucas_primality 10433 (3 : ZMod 10433)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10433 - 1 = (2 : ℕ)^6 * ((163 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 10433)^5216 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
      subst q
      change (3 : ZMod 10433)^64 ≠ 1
      reduce_mod_char
      decide

theorem prime_10453 : Nat.Prime 10453 := by
  apply lucas_primality 10453 (5 : ZMod 10453)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10453 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((67 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 10453)^5226 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 10453)^3484 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (5 : ZMod 10453)^804 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (5 : ZMod 10453)^156 ≠ 1
          reduce_mod_char
          decide

theorem prime_10459 : Nat.Prime 10459 := by
  apply lucas_primality 10459 (2 : ZMod 10459)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10459 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((83 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 10459)^5229 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 10459)^3486 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 10459)^1494 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
          subst q
          change (2 : ZMod 10459)^126 ≠ 1
          reduce_mod_char
          decide

theorem prime_10501 : Nat.Prime 10501 := by
  apply lucas_primality 10501 (2 : ZMod 10501)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10501 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^3 * ((7 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 10501)^5250 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 10501)^3500 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 10501)^2100 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 10501)^1500 ≠ 1
          reduce_mod_char
          decide

theorem prime_10513 : Nat.Prime 10513 := by
  apply lucas_primality 10513 (7 : ZMod 10513)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10513 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((73 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 10513)^5256 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 10513)^3504 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
        subst q
        change (7 : ZMod 10513)^144 ≠ 1
        reduce_mod_char
        decide

theorem prime_10597 : Nat.Prime 10597 := by
  apply lucas_primality 10597 (5 : ZMod 10597)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10597 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((883 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 10597)^5298 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 10597)^3532 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 883 := Nat.prime_eq_prime_of_dvd_pow hq prime_883 hd
        subst q
        change (5 : ZMod 10597)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_10607 : Nat.Prime 10607 := by
  apply lucas_primality 10607 (5 : ZMod 10607)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10607 - 1 = (2 : ℕ)^1 * ((5303 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 10607)^5303 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 5303 := Nat.prime_eq_prime_of_dvd_pow hq prime_5303 hd
      subst q
      change (5 : ZMod 10607)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_10613 : Nat.Prime 10613 := by
  apply lucas_primality 10613 (2 : ZMod 10613)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10613 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((379 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 10613)^5306 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 10613)^1516 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 379 := Nat.prime_eq_prime_of_dvd_pow hq prime_379 hd
        subst q
        change (2 : ZMod 10613)^28 ≠ 1
        reduce_mod_char
        decide

theorem prime_10651 : Nat.Prime 10651 := by
  apply lucas_primality 10651 (7 : ZMod 10651)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10651 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((71 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 10651)^5325 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 10651)^3550 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 10651)^2130 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
          subst q
          change (7 : ZMod 10651)^150 ≠ 1
          reduce_mod_char
          decide

theorem prime_10733 : Nat.Prime 10733 := by
  apply lucas_primality 10733 (2 : ZMod 10733)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10733 - 1 = (2 : ℕ)^2 * ((2683 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 10733)^5366 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 2683 := Nat.prime_eq_prime_of_dvd_pow hq prime_2683 hd
      subst q
      change (2 : ZMod 10733)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_10739 : Nat.Prime 10739 := by
  apply lucas_primality 10739 (6 : ZMod 10739)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10739 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((59 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 10739)^5369 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (6 : ZMod 10739)^1534 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (6 : ZMod 10739)^826 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (6 : ZMod 10739)^182 ≠ 1
          reduce_mod_char
          decide

theorem prime_10781 : Nat.Prime 10781 := by
  apply lucas_primality 10781 (10 : ZMod 10781)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10781 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^2 * ((11 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 10781)^5390 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (10 : ZMod 10781)^2156 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (10 : ZMod 10781)^1540 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (10 : ZMod 10781)^980 ≠ 1
          reduce_mod_char
          decide

theorem prime_10799 : Nat.Prime 10799 := by
  apply lucas_primality 10799 (19 : ZMod 10799)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10799 - 1 = (2 : ℕ)^1 * ((5399 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 10799)^5399 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 5399 := Nat.prime_eq_prime_of_dvd_pow hq prime_5399 hd
      subst q
      change (19 : ZMod 10799)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_10837 : Nat.Prime 10837 := by
  apply lucas_primality 10837 (2 : ZMod 10837)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10837 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((43 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 10837)^5418 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 10837)^3612 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 10837)^1548 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (2 : ZMod 10837)^252 ≠ 1
          reduce_mod_char
          decide

theorem prime_10847 : Nat.Prime 10847 := by
  apply lucas_primality 10847 (5 : ZMod 10847)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10847 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((29 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 10847)^5423 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 10847)^986 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (5 : ZMod 10847)^638 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (5 : ZMod 10847)^374 ≠ 1
          reduce_mod_char
          decide

theorem prime_10867 : Nat.Prime 10867 := by
  apply lucas_primality 10867 (2 : ZMod 10867)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10867 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1811 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 10867)^5433 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 10867)^3622 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1811 := Nat.prime_eq_prime_of_dvd_pow hq prime_1811 hd
        subst q
        change (2 : ZMod 10867)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_10957 : Nat.Prime 10957 := by
  apply lucas_primality 10957 (5 : ZMod 10957)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10957 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((83 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 10957)^5478 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 10957)^3652 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 10957)^996 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
          subst q
          change (5 : ZMod 10957)^132 ≠ 1
          reduce_mod_char
          decide

theorem prime_10973 : Nat.Prime 10973 := by
  apply lucas_primality 10973 (2 : ZMod 10973)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10973 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((211 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 10973)^5486 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 10973)^844 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 211 := Nat.prime_eq_prime_of_dvd_pow hq prime_211 hd
        subst q
        change (2 : ZMod 10973)^52 ≠ 1
        reduce_mod_char
        decide

theorem prime_11057 : Nat.Prime 11057 := by
  apply lucas_primality 11057 (3 : ZMod 11057)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11057 - 1 = (2 : ℕ)^4 * ((691 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 11057)^5528 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 691 := Nat.prime_eq_prime_of_dvd_pow hq prime_691 hd
      subst q
      change (3 : ZMod 11057)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_11059 : Nat.Prime 11059 := by
  apply lucas_primality 11059 (10 : ZMod 11059)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11059 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((97 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 11059)^5529 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 11059)^3686 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (10 : ZMod 11059)^582 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
          subst q
          change (10 : ZMod 11059)^114 ≠ 1
          reduce_mod_char
          decide

theorem prime_11083 : Nat.Prime 11083 := by
  apply lucas_primality 11083 (2 : ZMod 11083)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11083 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1847 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 11083)^5541 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 11083)^3694 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1847 := Nat.prime_eq_prime_of_dvd_pow hq prime_1847 hd
        subst q
        change (2 : ZMod 11083)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_11149 : Nat.Prime 11149 := by
  apply lucas_primality 11149 (10 : ZMod 11149)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11149 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((929 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 11149)^5574 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 11149)^3716 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 929 := Nat.prime_eq_prime_of_dvd_pow hq prime_929 hd
        subst q
        change (10 : ZMod 11149)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_11159 : Nat.Prime 11159 := by
  apply lucas_primality 11159 (7 : ZMod 11159)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11159 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((797 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 11159)^5579 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 11159)^1594 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 797 := Nat.prime_eq_prime_of_dvd_pow hq prime_797 hd
        subst q
        change (7 : ZMod 11159)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_11173 : Nat.Prime 11173 := by
  apply lucas_primality 11173 (5 : ZMod 11173)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11173 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((19 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 11173)^5586 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 11173)^3724 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 11173)^1596 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (5 : ZMod 11173)^588 ≠ 1
          reduce_mod_char
          decide

theorem prime_11213 : Nat.Prime 11213 := by
  apply lucas_primality 11213 (2 : ZMod 11213)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11213 - 1 = (2 : ℕ)^2 * ((2803 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 11213)^5606 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 2803 := Nat.prime_eq_prime_of_dvd_pow hq prime_2803 hd
      subst q
      change (2 : ZMod 11213)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_11243 : Nat.Prime 11243 := by
  apply lucas_primality 11243 (5 : ZMod 11243)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11243 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((73 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 11243)^5621 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 11243)^1606 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 11243)^1022 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
          subst q
          change (5 : ZMod 11243)^154 ≠ 1
          reduce_mod_char
          decide

theorem prime_11299 : Nat.Prime 11299 := by
  apply lucas_primality 11299 (3 : ZMod 11299)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11299 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((269 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 11299)^5649 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 11299)^3766 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 11299)^1614 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
          subst q
          change (3 : ZMod 11299)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_11311 : Nat.Prime 11311 := by
  apply lucas_primality 11311 (3 : ZMod 11311)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11311 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((29 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 11311)^5655 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 11311)^3770 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 11311)^2262 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (3 : ZMod 11311)^870 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (3 : ZMod 11311)^390 ≠ 1
            reduce_mod_char
            decide

theorem prime_11317 : Nat.Prime 11317 := by
  apply lucas_primality 11317 (2 : ZMod 11317)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11317 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((41 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 11317)^5658 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 11317)^3772 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 11317)^492 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (2 : ZMod 11317)^276 ≠ 1
          reduce_mod_char
          decide

theorem prime_11321 : Nat.Prime 11321 := by
  apply lucas_primality 11321 (3 : ZMod 11321)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11321 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((283 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 11321)^5660 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 11321)^2264 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 283 := Nat.prime_eq_prime_of_dvd_pow hq prime_283 hd
        subst q
        change (3 : ZMod 11321)^40 ≠ 1
        reduce_mod_char
        decide

theorem prime_11369 : Nat.Prime 11369 := by
  apply lucas_primality 11369 (3 : ZMod 11369)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11369 - 1 = (2 : ℕ)^3 * ((7 : ℕ)^2 * ((29 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 11369)^5684 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 11369)^1624 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (3 : ZMod 11369)^392 ≠ 1
        reduce_mod_char
        decide

theorem prime_11399 : Nat.Prime 11399 := by
  apply lucas_primality 11399 (11 : ZMod 11399)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11399 - 1 = (2 : ℕ)^1 * ((41 : ℕ)^1 * ((139 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 11399)^5699 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
        subst q
        change (11 : ZMod 11399)^278 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
        subst q
        change (11 : ZMod 11399)^82 ≠ 1
        reduce_mod_char
        decide

theorem prime_11423 : Nat.Prime 11423 := by
  apply lucas_primality 11423 (5 : ZMod 11423)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11423 - 1 = (2 : ℕ)^1 * ((5711 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 11423)^5711 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 5711 := Nat.prime_eq_prime_of_dvd_pow hq prime_5711 hd
      subst q
      change (5 : ZMod 11423)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_11471 : Nat.Prime 11471 := by
  apply lucas_primality 11471 (11 : ZMod 11471)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11471 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((31 : ℕ)^1 * ((37 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 11471)^5735 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 11471)^2294 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (11 : ZMod 11471)^370 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (11 : ZMod 11471)^310 ≠ 1
          reduce_mod_char
          decide

theorem prime_11483 : Nat.Prime 11483 := by
  apply lucas_primality 11483 (2 : ZMod 11483)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11483 - 1 = (2 : ℕ)^1 * ((5741 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 11483)^5741 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 5741 := Nat.prime_eq_prime_of_dvd_pow hq prime_5741 hd
      subst q
      change (2 : ZMod 11483)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_11489 : Nat.Prime 11489 := by
  apply lucas_primality 11489 (3 : ZMod 11489)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11489 - 1 = (2 : ℕ)^5 * ((359 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 11489)^5744 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 359 := Nat.prime_eq_prime_of_dvd_pow hq prime_359 hd
      subst q
      change (3 : ZMod 11489)^32 ≠ 1
      reduce_mod_char
      decide

theorem prime_11519 : Nat.Prime 11519 := by
  apply lucas_primality 11519 (7 : ZMod 11519)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11519 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((443 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 11519)^5759 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (7 : ZMod 11519)^886 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 443 := Nat.prime_eq_prime_of_dvd_pow hq prime_443 hd
        subst q
        change (7 : ZMod 11519)^26 ≠ 1
        reduce_mod_char
        decide

theorem prime_11579 : Nat.Prime 11579 := by
  apply lucas_primality 11579 (2 : ZMod 11579)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11579 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((827 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 11579)^5789 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 11579)^1654 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 827 := Nat.prime_eq_prime_of_dvd_pow hq prime_827 hd
        subst q
        change (2 : ZMod 11579)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_11587 : Nat.Prime 11587 := by
  apply lucas_primality 11587 (2 : ZMod 11587)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11587 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1931 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 11587)^5793 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 11587)^3862 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1931 := Nat.prime_eq_prime_of_dvd_pow hq prime_1931 hd
        subst q
        change (2 : ZMod 11587)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_11593 : Nat.Prime 11593 := by
  apply lucas_primality 11593 (5 : ZMod 11593)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11593 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((23 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 11593)^5796 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 11593)^3864 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 11593)^1656 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (5 : ZMod 11593)^504 ≠ 1
          reduce_mod_char
          decide

theorem prime_11677 : Nat.Prime 11677 := by
  apply lucas_primality 11677 (2 : ZMod 11677)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11677 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((139 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 11677)^5838 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 11677)^3892 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 11677)^1668 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
          subst q
          change (2 : ZMod 11677)^84 ≠ 1
          reduce_mod_char
          decide

theorem prime_11719 : Nat.Prime 11719 := by
  apply lucas_primality 11719 (6 : ZMod 11719)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11719 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((31 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 11719)^5859 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 11719)^3906 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 11719)^1674 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (6 : ZMod 11719)^378 ≠ 1
          reduce_mod_char
          decide

theorem prime_11801 : Nat.Prime 11801 := by
  apply lucas_primality 11801 (3 : ZMod 11801)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11801 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^2 * ((59 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 11801)^5900 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 11801)^2360 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
        subst q
        change (3 : ZMod 11801)^200 ≠ 1
        reduce_mod_char
        decide

theorem prime_11821 : Nat.Prime 11821 := by
  apply lucas_primality 11821 (2 : ZMod 11821)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11821 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((197 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 11821)^5910 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 11821)^3940 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 11821)^2364 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
          subst q
          change (2 : ZMod 11821)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_11839 : Nat.Prime 11839 := by
  apply lucas_primality 11839 (3 : ZMod 11839)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11839 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1973 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 11839)^5919 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 11839)^3946 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1973 := Nat.prime_eq_prime_of_dvd_pow hq prime_1973 hd
        subst q
        change (3 : ZMod 11839)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_11903 : Nat.Prime 11903 := by
  apply lucas_primality 11903 (5 : ZMod 11903)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11903 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((541 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 11903)^5951 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 11903)^1082 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 541 := Nat.prime_eq_prime_of_dvd_pow hq prime_541 hd
        subst q
        change (5 : ZMod 11903)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_11909 : Nat.Prime 11909 := by
  apply lucas_primality 11909 (2 : ZMod 11909)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11909 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((229 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 11909)^5954 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 11909)^916 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 229 := Nat.prime_eq_prime_of_dvd_pow hq prime_229 hd
        subst q
        change (2 : ZMod 11909)^52 ≠ 1
        reduce_mod_char
        decide

theorem prime_11927 : Nat.Prime 11927 := by
  apply lucas_primality 11927 (5 : ZMod 11927)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11927 - 1 = (2 : ℕ)^1 * ((67 : ℕ)^1 * ((89 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 11927)^5963 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
        subst q
        change (5 : ZMod 11927)^178 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
        subst q
        change (5 : ZMod 11927)^134 ≠ 1
        reduce_mod_char
        decide

theorem prime_11941 : Nat.Prime 11941 := by
  apply lucas_primality 11941 (10 : ZMod 11941)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11941 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((199 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 11941)^5970 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 11941)^3980 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 11941)^2388 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 199 := Nat.prime_eq_prime_of_dvd_pow hq prime_199 hd
          subst q
          change (10 : ZMod 11941)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_11981 : Nat.Prime 11981 := by
  apply lucas_primality 11981 (2 : ZMod 11981)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11981 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((599 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 11981)^5990 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 11981)^2396 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 599 := Nat.prime_eq_prime_of_dvd_pow hq prime_599 hd
        subst q
        change (2 : ZMod 11981)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_12007 : Nat.Prime 12007 := by
  apply lucas_primality 12007 (13 : ZMod 12007)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12007 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((23 : ℕ)^1 * ((29 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 12007)^6003 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 12007)^4002 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (13 : ZMod 12007)^522 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (13 : ZMod 12007)^414 ≠ 1
          reduce_mod_char
          decide

theorem prime_12041 : Nat.Prime 12041 := by
  apply lucas_primality 12041 (3 : ZMod 12041)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12041 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((43 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 12041)^6020 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 12041)^2408 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 12041)^1720 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (3 : ZMod 12041)^280 ≠ 1
          reduce_mod_char
          decide

theorem prime_12101 : Nat.Prime 12101 := by
  apply lucas_primality 12101 (3 : ZMod 12101)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12101 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((11 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 12101)^6050 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 12101)^2420 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 12101)^1100 ≠ 1
        reduce_mod_char
        decide

theorem prime_12109 : Nat.Prime 12109 := by
  apply lucas_primality 12109 (6 : ZMod 12109)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12109 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((1009 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 12109)^6054 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 12109)^4036 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1009 := Nat.prime_eq_prime_of_dvd_pow hq prime_1009 hd
        subst q
        change (6 : ZMod 12109)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_12119 : Nat.Prime 12119 := by
  apply lucas_primality 12119 (7 : ZMod 12119)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12119 - 1 = (2 : ℕ)^1 * ((73 : ℕ)^1 * ((83 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 12119)^6059 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
        subst q
        change (7 : ZMod 12119)^166 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
        subst q
        change (7 : ZMod 12119)^146 ≠ 1
        reduce_mod_char
        decide

theorem prime_12157 : Nat.Prime 12157 := by
  apply lucas_primality 12157 (2 : ZMod 12157)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12157 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((1013 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 12157)^6078 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 12157)^4052 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1013 := Nat.prime_eq_prime_of_dvd_pow hq prime_1013 hd
        subst q
        change (2 : ZMod 12157)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_12203 : Nat.Prime 12203 := by
  apply lucas_primality 12203 (2 : ZMod 12203)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12203 - 1 = (2 : ℕ)^1 * ((6101 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 12203)^6101 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 6101 := Nat.prime_eq_prime_of_dvd_pow hq prime_6101 hd
      subst q
      change (2 : ZMod 12203)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_12227 : Nat.Prime 12227 := by
  apply lucas_primality 12227 (2 : ZMod 12227)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12227 - 1 = (2 : ℕ)^1 * ((6113 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 12227)^6113 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 6113 := Nat.prime_eq_prime_of_dvd_pow hq prime_6113 hd
      subst q
      change (2 : ZMod 12227)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_12239 : Nat.Prime 12239 := by
  apply lucas_primality 12239 (13 : ZMod 12239)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12239 - 1 = (2 : ℕ)^1 * ((29 : ℕ)^1 * ((211 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 12239)^6119 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (13 : ZMod 12239)^422 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 211 := Nat.prime_eq_prime_of_dvd_pow hq prime_211 hd
        subst q
        change (13 : ZMod 12239)^58 ≠ 1
        reduce_mod_char
        decide

theorem prime_12251 : Nat.Prime 12251 := by
  apply lucas_primality 12251 (2 : ZMod 12251)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12251 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^3 * ((7 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 12251)^6125 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 12251)^2450 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 12251)^1750 ≠ 1
        reduce_mod_char
        decide

theorem prime_12373 : Nat.Prime 12373 := by
  apply lucas_primality 12373 (2 : ZMod 12373)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12373 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((1031 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 12373)^6186 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 12373)^4124 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1031 := Nat.prime_eq_prime_of_dvd_pow hq prime_1031 hd
        subst q
        change (2 : ZMod 12373)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_12391 : Nat.Prime 12391 := by
  apply lucas_primality 12391 (26 : ZMod 12391)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12391 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((59 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (26 : ZMod 12391)^6195 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (26 : ZMod 12391)^4130 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (26 : ZMod 12391)^2478 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (26 : ZMod 12391)^1770 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
            subst q
            change (26 : ZMod 12391)^210 ≠ 1
            reduce_mod_char
            decide

theorem prime_12479 : Nat.Prime 12479 := by
  apply lucas_primality 12479 (23 : ZMod 12479)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12479 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((367 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (23 : ZMod 12479)^6239 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (23 : ZMod 12479)^734 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 367 := Nat.prime_eq_prime_of_dvd_pow hq prime_367 hd
        subst q
        change (23 : ZMod 12479)^34 ≠ 1
        reduce_mod_char
        decide

theorem prime_12491 : Nat.Prime 12491 := by
  apply lucas_primality 12491 (2 : ZMod 12491)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12491 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((1249 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 12491)^6245 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 12491)^2498 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1249 := Nat.prime_eq_prime_of_dvd_pow hq prime_1249 hd
        subst q
        change (2 : ZMod 12491)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_12527 : Nat.Prime 12527 := by
  apply lucas_primality 12527 (5 : ZMod 12527)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12527 - 1 = (2 : ℕ)^1 * ((6263 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 12527)^6263 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 6263 := Nat.prime_eq_prime_of_dvd_pow hq prime_6263 hd
      subst q
      change (5 : ZMod 12527)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_12539 : Nat.Prime 12539 := by
  apply lucas_primality 12539 (2 : ZMod 12539)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12539 - 1 = (2 : ℕ)^1 * ((6269 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 12539)^6269 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 6269 := Nat.prime_eq_prime_of_dvd_pow hq prime_6269 hd
      subst q
      change (2 : ZMod 12539)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_12577 : Nat.Prime 12577 := by
  apply lucas_primality 12577 (10 : ZMod 12577)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12577 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((131 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 12577)^6288 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 12577)^4192 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
        subst q
        change (10 : ZMod 12577)^96 ≠ 1
        reduce_mod_char
        decide

theorem prime_12589 : Nat.Prime 12589 := by
  apply lucas_primality 12589 (2 : ZMod 12589)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12589 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((1049 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 12589)^6294 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 12589)^4196 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1049 := Nat.prime_eq_prime_of_dvd_pow hq prime_1049 hd
        subst q
        change (2 : ZMod 12589)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_12601 : Nat.Prime 12601 := by
  apply lucas_primality 12601 (11 : ZMod 12601)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12601 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((5 : ℕ)^2 * ((7 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 12601)^6300 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 12601)^4200 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 12601)^2520 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (11 : ZMod 12601)^1800 ≠ 1
          reduce_mod_char
          decide

theorem prime_12619 : Nat.Prime 12619 := by
  apply lucas_primality 12619 (2 : ZMod 12619)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12619 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((701 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 12619)^6309 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 12619)^4206 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 701 := Nat.prime_eq_prime_of_dvd_pow hq prime_701 hd
        subst q
        change (2 : ZMod 12619)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_12659 : Nat.Prime 12659 := by
  apply lucas_primality 12659 (2 : ZMod 12659)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12659 - 1 = (2 : ℕ)^1 * ((6329 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 12659)^6329 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 6329 := Nat.prime_eq_prime_of_dvd_pow hq prime_6329 hd
      subst q
      change (2 : ZMod 12659)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_12689 : Nat.Prime 12689 := by
  apply lucas_primality 12689 (3 : ZMod 12689)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12689 - 1 = (2 : ℕ)^4 * ((13 : ℕ)^1 * ((61 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 12689)^6344 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 12689)^976 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
        subst q
        change (3 : ZMod 12689)^208 ≠ 1
        reduce_mod_char
        decide

theorem prime_12721 : Nat.Prime 12721 := by
  apply lucas_primality 12721 (13 : ZMod 12721)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12721 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((53 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 12721)^6360 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 12721)^4240 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 12721)^2544 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (13 : ZMod 12721)^240 ≠ 1
          reduce_mod_char
          decide

theorem prime_12781 : Nat.Prime 12781 := by
  apply lucas_primality 12781 (2 : ZMod 12781)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12781 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((71 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 12781)^6390 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 12781)^4260 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 12781)^2556 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
          subst q
          change (2 : ZMod 12781)^180 ≠ 1
          reduce_mod_char
          decide

theorem prime_12791 : Nat.Prime 12791 := by
  apply lucas_primality 12791 (7 : ZMod 12791)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12791 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((1279 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 12791)^6395 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 12791)^2558 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1279 := Nat.prime_eq_prime_of_dvd_pow hq prime_1279 hd
        subst q
        change (7 : ZMod 12791)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_12893 : Nat.Prime 12893 := by
  apply lucas_primality 12893 (3 : ZMod 12893)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12893 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((293 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 12893)^6446 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 12893)^1172 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 293 := Nat.prime_eq_prime_of_dvd_pow hq prime_293 hd
        subst q
        change (3 : ZMod 12893)^44 ≠ 1
        reduce_mod_char
        decide

theorem prime_12941 : Nat.Prime 12941 := by
  apply lucas_primality 12941 (2 : ZMod 12941)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12941 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((647 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 12941)^6470 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 12941)^2588 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 647 := Nat.prime_eq_prime_of_dvd_pow hq prime_647 hd
        subst q
        change (2 : ZMod 12941)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_12959 : Nat.Prime 12959 := by
  apply lucas_primality 12959 (7 : ZMod 12959)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12959 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((19 : ℕ)^1 * ((31 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 12959)^6479 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (7 : ZMod 12959)^1178 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (7 : ZMod 12959)^682 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (7 : ZMod 12959)^418 ≠ 1
          reduce_mod_char
          decide

theorem prime_12967 : Nat.Prime 12967 := by
  apply lucas_primality 12967 (3 : ZMod 12967)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12967 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((2161 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 12967)^6483 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 12967)^4322 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2161 := Nat.prime_eq_prime_of_dvd_pow hq prime_2161 hd
        subst q
        change (3 : ZMod 12967)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_12983 : Nat.Prime 12983 := by
  apply lucas_primality 12983 (5 : ZMod 12983)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12983 - 1 = (2 : ℕ)^1 * ((6491 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 12983)^6491 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 6491 := Nat.prime_eq_prime_of_dvd_pow hq prime_6491 hd
      subst q
      change (5 : ZMod 12983)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_13009 : Nat.Prime 13009 := by
  apply lucas_primality 13009 (7 : ZMod 13009)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13009 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((271 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 13009)^6504 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 13009)^4336 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 271 := Nat.prime_eq_prime_of_dvd_pow hq prime_271 hd
        subst q
        change (7 : ZMod 13009)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_13043 : Nat.Prime 13043 := by
  apply lucas_primality 13043 (2 : ZMod 13043)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13043 - 1 = (2 : ℕ)^1 * ((6521 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 13043)^6521 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 6521 := Nat.prime_eq_prime_of_dvd_pow hq prime_6521 hd
      subst q
      change (2 : ZMod 13043)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_13093 : Nat.Prime 13093 := by
  apply lucas_primality 13093 (6 : ZMod 13093)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13093 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((1091 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 13093)^6546 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 13093)^4364 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1091 := Nat.prime_eq_prime_of_dvd_pow hq prime_1091 hd
        subst q
        change (6 : ZMod 13093)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_13109 : Nat.Prime 13109 := by
  apply lucas_primality 13109 (2 : ZMod 13109)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13109 - 1 = (2 : ℕ)^2 * ((29 : ℕ)^1 * ((113 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 13109)^6554 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (2 : ZMod 13109)^452 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
        subst q
        change (2 : ZMod 13109)^116 ≠ 1
        reduce_mod_char
        decide

theorem prime_13121 : Nat.Prime 13121 := by
  apply lucas_primality 13121 (7 : ZMod 13121)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13121 - 1 = (2 : ℕ)^6 * ((5 : ℕ)^1 * ((41 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 13121)^6560 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 13121)^2624 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
        subst q
        change (7 : ZMod 13121)^320 ≠ 1
        reduce_mod_char
        decide

theorem prime_13127 : Nat.Prime 13127 := by
  apply lucas_primality 13127 (5 : ZMod 13127)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13127 - 1 = (2 : ℕ)^1 * ((6563 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 13127)^6563 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 6563 := Nat.prime_eq_prime_of_dvd_pow hq prime_6563 hd
      subst q
      change (5 : ZMod 13127)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_13147 : Nat.Prime 13147 := by
  apply lucas_primality 13147 (2 : ZMod 13147)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13147 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((313 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 13147)^6573 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 13147)^4382 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 13147)^1878 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 313 := Nat.prime_eq_prime_of_dvd_pow hq prime_313 hd
          subst q
          change (2 : ZMod 13147)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_13159 : Nat.Prime 13159 := by
  apply lucas_primality 13159 (3 : ZMod 13159)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13159 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((17 : ℕ)^1 * ((43 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 13159)^6579 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 13159)^4386 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (3 : ZMod 13159)^774 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (3 : ZMod 13159)^306 ≠ 1
          reduce_mod_char
          decide

theorem prime_13219 : Nat.Prime 13219 := by
  apply lucas_primality 13219 (3 : ZMod 13219)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13219 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((2203 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 13219)^6609 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 13219)^4406 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2203 := Nat.prime_eq_prime_of_dvd_pow hq prime_2203 hd
        subst q
        change (3 : ZMod 13219)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_13259 : Nat.Prime 13259 := by
  apply lucas_primality 13259 (6 : ZMod 13259)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13259 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((947 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 13259)^6629 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (6 : ZMod 13259)^1894 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 947 := Nat.prime_eq_prime_of_dvd_pow hq prime_947 hd
        subst q
        change (6 : ZMod 13259)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_13267 : Nat.Prime 13267 := by
  apply lucas_primality 13267 (3 : ZMod 13267)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13267 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((67 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 13267)^6633 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 13267)^4422 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 13267)^1206 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (3 : ZMod 13267)^198 ≠ 1
          reduce_mod_char
          decide

theorem prime_13339 : Nat.Prime 13339 := by
  apply lucas_primality 13339 (2 : ZMod 13339)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13339 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((13 : ℕ)^1 * ((19 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 13339)^6669 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 13339)^4446 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 13339)^1026 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 13339)^702 ≠ 1
          reduce_mod_char
          decide

theorem prime_13523 : Nat.Prime 13523 := by
  apply lucas_primality 13523 (2 : ZMod 13523)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13523 - 1 = (2 : ℕ)^1 * ((6761 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 13523)^6761 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 6761 := Nat.prime_eq_prime_of_dvd_pow hq prime_6761 hd
      subst q
      change (2 : ZMod 13523)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_13537 : Nat.Prime 13537 := by
  apply lucas_primality 13537 (7 : ZMod 13537)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13537 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^2 * ((47 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 13537)^6768 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 13537)^4512 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (7 : ZMod 13537)^288 ≠ 1
        reduce_mod_char
        decide

theorem prime_13553 : Nat.Prime 13553 := by
  apply lucas_primality 13553 (3 : ZMod 13553)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13553 - 1 = (2 : ℕ)^4 * ((7 : ℕ)^1 * ((11 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 13553)^6776 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 13553)^1936 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 13553)^1232 ≠ 1
        reduce_mod_char
        decide

theorem prime_13567 : Nat.Prime 13567 := by
  apply lucas_primality 13567 (3 : ZMod 13567)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13567 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((17 : ℕ)^1 * ((19 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 13567)^6783 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 13567)^4522 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 13567)^1938 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (3 : ZMod 13567)^798 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (3 : ZMod 13567)^714 ≠ 1
            reduce_mod_char
            decide

theorem prime_13577 : Nat.Prime 13577 := by
  apply lucas_primality 13577 (3 : ZMod 13577)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13577 - 1 = (2 : ℕ)^3 * ((1697 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 13577)^6788 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1697 := Nat.prime_eq_prime_of_dvd_pow hq prime_1697 hd
      subst q
      change (3 : ZMod 13577)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_13633 : Nat.Prime 13633 := by
  apply lucas_primality 13633 (5 : ZMod 13633)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13633 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^1 * ((71 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 13633)^6816 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 13633)^4544 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
        subst q
        change (5 : ZMod 13633)^192 ≠ 1
        reduce_mod_char
        decide

theorem prime_13649 : Nat.Prime 13649 := by
  apply lucas_primality 13649 (3 : ZMod 13649)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13649 - 1 = (2 : ℕ)^4 * ((853 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 13649)^6824 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 853 := Nat.prime_eq_prime_of_dvd_pow hq prime_853 hd
      subst q
      change (3 : ZMod 13649)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_13669 : Nat.Prime 13669 := by
  apply lucas_primality 13669 (6 : ZMod 13669)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13669 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((67 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 13669)^6834 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 13669)^4556 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (6 : ZMod 13669)^804 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (6 : ZMod 13669)^204 ≠ 1
          reduce_mod_char
          decide

theorem prime_13681 : Nat.Prime 13681 := by
  apply lucas_primality 13681 (22 : ZMod 13681)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13681 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((19 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (22 : ZMod 13681)^6840 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (22 : ZMod 13681)^4560 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (22 : ZMod 13681)^2736 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (22 : ZMod 13681)^720 ≠ 1
          reduce_mod_char
          decide

theorem prime_13691 : Nat.Prime 13691 := by
  apply lucas_primality 13691 (2 : ZMod 13691)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13691 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((37 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 13691)^6845 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 13691)^2738 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (2 : ZMod 13691)^370 ≠ 1
        reduce_mod_char
        decide

theorem prime_13693 : Nat.Prime 13693 := by
  apply lucas_primality 13693 (6 : ZMod 13693)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13693 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((163 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 13693)^6846 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 13693)^4564 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 13693)^1956 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
          subst q
          change (6 : ZMod 13693)^84 ≠ 1
          reduce_mod_char
          decide

theorem prime_13751 : Nat.Prime 13751 := by
  apply lucas_primality 13751 (11 : ZMod 13751)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13751 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^4 * ((11 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 13751)^6875 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 13751)^2750 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (11 : ZMod 13751)^1250 ≠ 1
        reduce_mod_char
        decide

theorem prime_13841 : Nat.Prime 13841 := by
  apply lucas_primality 13841 (6 : ZMod 13841)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13841 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((173 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 13841)^6920 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 13841)^2768 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
        subst q
        change (6 : ZMod 13841)^80 ≠ 1
        reduce_mod_char
        decide

theorem prime_13873 : Nat.Prime 13873 := by
  apply lucas_primality 13873 (5 : ZMod 13873)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13873 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((17 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 13873)^6936 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 13873)^4624 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (5 : ZMod 13873)^816 ≠ 1
        reduce_mod_char
        decide

theorem prime_13877 : Nat.Prime 13877 := by
  apply lucas_primality 13877 (2 : ZMod 13877)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13877 - 1 = (2 : ℕ)^2 * ((3469 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 13877)^6938 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3469 := Nat.prime_eq_prime_of_dvd_pow hq prime_3469 hd
      subst q
      change (2 : ZMod 13877)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_13913 : Nat.Prime 13913 := by
  apply lucas_primality 13913 (3 : ZMod 13913)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13913 - 1 = (2 : ℕ)^3 * ((37 : ℕ)^1 * ((47 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 13913)^6956 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (3 : ZMod 13913)^376 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (3 : ZMod 13913)^296 ≠ 1
        reduce_mod_char
        decide

theorem prime_13931 : Nat.Prime 13931 := by
  apply lucas_primality 13931 (2 : ZMod 13931)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13931 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((199 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 13931)^6965 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 13931)^2786 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 13931)^1990 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 199 := Nat.prime_eq_prime_of_dvd_pow hq prime_199 hd
          subst q
          change (2 : ZMod 13931)^70 ≠ 1
          reduce_mod_char
          decide

theorem prime_13933 : Nat.Prime 13933 := by
  apply lucas_primality 13933 (2 : ZMod 13933)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13933 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^4 * ((43 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 13933)^6966 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 13933)^4644 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
        subst q
        change (2 : ZMod 13933)^324 ≠ 1
        reduce_mod_char
        decide

theorem prime_13967 : Nat.Prime 13967 := by
  apply lucas_primality 13967 (5 : ZMod 13967)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13967 - 1 = (2 : ℕ)^1 * ((6983 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 13967)^6983 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 6983 := Nat.prime_eq_prime_of_dvd_pow hq prime_6983 hd
      subst q
      change (5 : ZMod 13967)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_14173 : Nat.Prime 14173 := by
  apply lucas_primality 14173 (2 : ZMod 14173)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14173 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((1181 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 14173)^7086 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 14173)^4724 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1181 := Nat.prime_eq_prime_of_dvd_pow hq prime_1181 hd
        subst q
        change (2 : ZMod 14173)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_14249 : Nat.Prime 14249 := by
  apply lucas_primality 14249 (3 : ZMod 14249)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14249 - 1 = (2 : ℕ)^3 * ((13 : ℕ)^1 * ((137 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 14249)^7124 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 14249)^1096 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
        subst q
        change (3 : ZMod 14249)^104 ≠ 1
        reduce_mod_char
        decide

theorem prime_14281 : Nat.Prime 14281 := by
  apply lucas_primality 14281 (19 : ZMod 14281)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14281 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((17 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 14281)^7140 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 14281)^4760 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (19 : ZMod 14281)^2856 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (19 : ZMod 14281)^2040 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (19 : ZMod 14281)^840 ≠ 1
            reduce_mod_char
            decide

theorem prime_14293 : Nat.Prime 14293 := by
  apply lucas_primality 14293 (6 : ZMod 14293)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14293 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((397 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 14293)^7146 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 14293)^4764 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 397 := Nat.prime_eq_prime_of_dvd_pow hq prime_397 hd
        subst q
        change (6 : ZMod 14293)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_14321 : Nat.Prime 14321 := by
  apply lucas_primality 14321 (3 : ZMod 14321)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14321 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((179 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 14321)^7160 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 14321)^2864 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 179 := Nat.prime_eq_prime_of_dvd_pow hq prime_179 hd
        subst q
        change (3 : ZMod 14321)^80 ≠ 1
        reduce_mod_char
        decide

theorem prime_14347 : Nat.Prime 14347 := by
  apply lucas_primality 14347 (3 : ZMod 14347)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14347 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((797 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 14347)^7173 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 14347)^4782 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 797 := Nat.prime_eq_prime_of_dvd_pow hq prime_797 hd
        subst q
        change (3 : ZMod 14347)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_14389 : Nat.Prime 14389 := by
  apply lucas_primality 14389 (2 : ZMod 14389)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14389 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((109 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 14389)^7194 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 14389)^4796 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 14389)^1308 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
          subst q
          change (2 : ZMod 14389)^132 ≠ 1
          reduce_mod_char
          decide

theorem prime_14401 : Nat.Prime 14401 := by
  apply lucas_primality 14401 (11 : ZMod 14401)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14401 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^2 * ((5 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 14401)^7200 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 14401)^4800 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 14401)^2880 ≠ 1
        reduce_mod_char
        decide

theorem prime_14407 : Nat.Prime 14407 := by
  apply lucas_primality 14407 (19 : ZMod 14407)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14407 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^4)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 14407)^7203 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 14407)^4802 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (19 : ZMod 14407)^2058 ≠ 1
        reduce_mod_char
        decide

theorem prime_14447 : Nat.Prime 14447 := by
  apply lucas_primality 14447 (5 : ZMod 14447)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14447 - 1 = (2 : ℕ)^1 * ((31 : ℕ)^1 * ((233 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 14447)^7223 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (5 : ZMod 14447)^466 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
        subst q
        change (5 : ZMod 14447)^62 ≠ 1
        reduce_mod_char
        decide

theorem prime_14449 : Nat.Prime 14449 := by
  apply lucas_primality 14449 (22 : ZMod 14449)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14449 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((43 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (22 : ZMod 14449)^7224 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (22 : ZMod 14449)^4816 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (22 : ZMod 14449)^2064 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (22 : ZMod 14449)^336 ≠ 1
          reduce_mod_char
          decide

theorem prime_14479 : Nat.Prime 14479 := by
  apply lucas_primality 14479 (3 : ZMod 14479)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14479 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((127 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 14479)^7239 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 14479)^4826 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (3 : ZMod 14479)^762 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
          subst q
          change (3 : ZMod 14479)^114 ≠ 1
          reduce_mod_char
          decide

theorem prime_14503 : Nat.Prime 14503 := by
  apply lucas_primality 14503 (3 : ZMod 14503)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14503 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((2417 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 14503)^7251 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 14503)^4834 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2417 := Nat.prime_eq_prime_of_dvd_pow hq prime_2417 hd
        subst q
        change (3 : ZMod 14503)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_14593 : Nat.Prime 14593 := by
  apply lucas_primality 14593 (5 : ZMod 14593)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14593 - 1 = (2 : ℕ)^8 * ((3 : ℕ)^1 * ((19 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 14593)^7296 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 14593)^4864 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (5 : ZMod 14593)^768 ≠ 1
        reduce_mod_char
        decide

theorem prime_14627 : Nat.Prime 14627 := by
  apply lucas_primality 14627 (2 : ZMod 14627)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14627 - 1 = (2 : ℕ)^1 * ((71 : ℕ)^1 * ((103 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 14627)^7313 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
        subst q
        change (2 : ZMod 14627)^206 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
        subst q
        change (2 : ZMod 14627)^142 ≠ 1
        reduce_mod_char
        decide

theorem prime_14653 : Nat.Prime 14653 := by
  apply lucas_primality 14653 (2 : ZMod 14653)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14653 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((37 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 14653)^7326 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 14653)^4884 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 14653)^1332 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (2 : ZMod 14653)^396 ≠ 1
          reduce_mod_char
          decide

theorem prime_14657 : Nat.Prime 14657 := by
  apply lucas_primality 14657 (3 : ZMod 14657)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14657 - 1 = (2 : ℕ)^6 * ((229 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 14657)^7328 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 229 := Nat.prime_eq_prime_of_dvd_pow hq prime_229 hd
      subst q
      change (3 : ZMod 14657)^64 ≠ 1
      reduce_mod_char
      decide

theorem prime_14731 : Nat.Prime 14731 := by
  apply lucas_primality 14731 (10 : ZMod 14731)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14731 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((491 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 14731)^7365 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 14731)^4910 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 14731)^2946 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 491 := Nat.prime_eq_prime_of_dvd_pow hq prime_491 hd
          subst q
          change (10 : ZMod 14731)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_14741 : Nat.Prime 14741 := by
  apply lucas_primality 14741 (2 : ZMod 14741)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14741 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((67 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 14741)^7370 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 14741)^2948 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 14741)^1340 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (2 : ZMod 14741)^220 ≠ 1
          reduce_mod_char
          decide

theorem prime_14821 : Nat.Prime 14821 := by
  apply lucas_primality 14821 (2 : ZMod 14821)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14821 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((19 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 14821)^7410 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 14821)^4940 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 14821)^2964 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (2 : ZMod 14821)^1140 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (2 : ZMod 14821)^780 ≠ 1
            reduce_mod_char
            decide

theorem prime_14851 : Nat.Prime 14851 := by
  apply lucas_primality 14851 (2 : ZMod 14851)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14851 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((5 : ℕ)^2 * ((11 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 14851)^7425 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 14851)^4950 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 14851)^2970 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 14851)^1350 ≠ 1
          reduce_mod_char
          decide

theorem prime_14867 : Nat.Prime 14867 := by
  apply lucas_primality 14867 (2 : ZMod 14867)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14867 - 1 = (2 : ℕ)^1 * ((7433 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 14867)^7433 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 7433 := Nat.prime_eq_prime_of_dvd_pow hq prime_7433 hd
      subst q
      change (2 : ZMod 14867)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_14879 : Nat.Prime 14879 := by
  apply lucas_primality 14879 (7 : ZMod 14879)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14879 - 1 = (2 : ℕ)^1 * ((43 : ℕ)^1 * ((173 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 14879)^7439 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
        subst q
        change (7 : ZMod 14879)^346 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
        subst q
        change (7 : ZMod 14879)^86 ≠ 1
        reduce_mod_char
        decide

theorem prime_14887 : Nat.Prime 14887 := by
  apply lucas_primality 14887 (3 : ZMod 14887)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14887 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((827 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 14887)^7443 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 14887)^4962 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 827 := Nat.prime_eq_prime_of_dvd_pow hq prime_827 hd
        subst q
        change (3 : ZMod 14887)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_14947 : Nat.Prime 14947 := by
  apply lucas_primality 14947 (2 : ZMod 14947)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14947 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((47 : ℕ)^1 * ((53 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 14947)^7473 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 14947)^4982 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (2 : ZMod 14947)^318 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (2 : ZMod 14947)^282 ≠ 1
          reduce_mod_char
          decide

theorem prime_15031 : Nat.Prime 15031 := by
  apply lucas_primality 15031 (3 : ZMod 15031)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15031 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((167 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 15031)^7515 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 15031)^5010 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 15031)^3006 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
          subst q
          change (3 : ZMod 15031)^90 ≠ 1
          reduce_mod_char
          decide

theorem prime_15101 : Nat.Prime 15101 := by
  apply lucas_primality 15101 (2 : ZMod 15101)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15101 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((151 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 15101)^7550 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 15101)^3020 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
        subst q
        change (2 : ZMod 15101)^100 ≠ 1
        reduce_mod_char
        decide

theorem prime_15131 : Nat.Prime 15131 := by
  apply lucas_primality 15131 (2 : ZMod 15131)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15131 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((89 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 15131)^7565 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 15131)^3026 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 15131)^890 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (2 : ZMod 15131)^170 ≠ 1
          reduce_mod_char
          decide

theorem prime_15149 : Nat.Prime 15149 := by
  apply lucas_primality 15149 (2 : ZMod 15149)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15149 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((541 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 15149)^7574 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 15149)^2164 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 541 := Nat.prime_eq_prime_of_dvd_pow hq prime_541 hd
        subst q
        change (2 : ZMod 15149)^28 ≠ 1
        reduce_mod_char
        decide

theorem prime_15161 : Nat.Prime 15161 := by
  apply lucas_primality 15161 (3 : ZMod 15161)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15161 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((379 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 15161)^7580 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 15161)^3032 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 379 := Nat.prime_eq_prime_of_dvd_pow hq prime_379 hd
        subst q
        change (3 : ZMod 15161)^40 ≠ 1
        reduce_mod_char
        decide

theorem prime_15173 : Nat.Prime 15173 := by
  apply lucas_primality 15173 (2 : ZMod 15173)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15173 - 1 = (2 : ℕ)^2 * ((3793 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 15173)^7586 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3793 := Nat.prime_eq_prime_of_dvd_pow hq prime_3793 hd
      subst q
      change (2 : ZMod 15173)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_15187 : Nat.Prime 15187 := by
  apply lucas_primality 15187 (2 : ZMod 15187)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15187 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((2531 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 15187)^7593 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 15187)^5062 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2531 := Nat.prime_eq_prime_of_dvd_pow hq prime_2531 hd
        subst q
        change (2 : ZMod 15187)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_15217 : Nat.Prime 15217 := by
  apply lucas_primality 15217 (10 : ZMod 15217)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15217 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((317 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 15217)^7608 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 15217)^5072 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 317 := Nat.prime_eq_prime_of_dvd_pow hq prime_317 hd
        subst q
        change (10 : ZMod 15217)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_15289 : Nat.Prime 15289 := by
  apply lucas_primality 15289 (11 : ZMod 15289)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15289 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((13 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 15289)^7644 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 15289)^5096 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (11 : ZMod 15289)^2184 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (11 : ZMod 15289)^1176 ≠ 1
          reduce_mod_char
          decide

theorem prime_15313 : Nat.Prime 15313 := by
  apply lucas_primality 15313 (5 : ZMod 15313)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15313 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((29 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 15313)^7656 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 15313)^5104 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 15313)^1392 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (5 : ZMod 15313)^528 ≠ 1
          reduce_mod_char
          decide

theorem prime_15329 : Nat.Prime 15329 := by
  apply lucas_primality 15329 (3 : ZMod 15329)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15329 - 1 = (2 : ℕ)^5 * ((479 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 15329)^7664 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 479 := Nat.prime_eq_prime_of_dvd_pow hq prime_479 hd
      subst q
      change (3 : ZMod 15329)^32 ≠ 1
      reduce_mod_char
      decide

theorem prime_15377 : Nat.Prime 15377 := by
  apply lucas_primality 15377 (3 : ZMod 15377)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15377 - 1 = (2 : ℕ)^4 * ((31 : ℕ)^2) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 15377)^7688 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
      subst q
      change (3 : ZMod 15377)^496 ≠ 1
      reduce_mod_char
      decide

theorem prime_15401 : Nat.Prime 15401 := by
  apply lucas_primality 15401 (6 : ZMod 15401)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15401 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^2 * ((7 : ℕ)^1 * ((11 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 15401)^7700 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 15401)^3080 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 15401)^2200 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (6 : ZMod 15401)^1400 ≠ 1
          reduce_mod_char
          decide

theorem prime_15443 : Nat.Prime 15443 := by
  apply lucas_primality 15443 (2 : ZMod 15443)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15443 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((1103 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 15443)^7721 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 15443)^2206 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1103 := Nat.prime_eq_prime_of_dvd_pow hq prime_1103 hd
        subst q
        change (2 : ZMod 15443)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_15451 : Nat.Prime 15451 := by
  apply lucas_primality 15451 (3 : ZMod 15451)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15451 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((103 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 15451)^7725 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 15451)^5150 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 15451)^3090 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
          subst q
          change (3 : ZMod 15451)^150 ≠ 1
          reduce_mod_char
          decide

theorem prime_15461 : Nat.Prime 15461 := by
  apply lucas_primality 15461 (2 : ZMod 15461)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15461 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((773 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 15461)^7730 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 15461)^3092 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 773 := Nat.prime_eq_prime_of_dvd_pow hq prime_773 hd
        subst q
        change (2 : ZMod 15461)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_15541 : Nat.Prime 15541 := by
  apply lucas_primality 15541 (6 : ZMod 15541)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15541 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((37 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 15541)^7770 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 15541)^5180 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 15541)^3108 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (6 : ZMod 15541)^2220 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
            subst q
            change (6 : ZMod 15541)^420 ≠ 1
            reduce_mod_char
            decide

theorem prime_15569 : Nat.Prime 15569 := by
  apply lucas_primality 15569 (3 : ZMod 15569)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15569 - 1 = (2 : ℕ)^4 * ((7 : ℕ)^1 * ((139 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 15569)^7784 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 15569)^2224 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
        subst q
        change (3 : ZMod 15569)^112 ≠ 1
        reduce_mod_char
        decide

theorem prime_15583 : Nat.Prime 15583 := by
  apply lucas_primality 15583 (5 : ZMod 15583)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15583 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((53 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 15583)^7791 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 15583)^5194 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 15583)^2226 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (5 : ZMod 15583)^294 ≠ 1
          reduce_mod_char
          decide

end LegendreK6.Pratt
