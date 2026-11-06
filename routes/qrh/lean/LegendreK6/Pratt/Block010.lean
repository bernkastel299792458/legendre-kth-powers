import LegendreK6.Pratt.Block009

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LegendreK6.Pratt

theorem prime_302629 : Nat.Prime 302629 := by
  apply lucas_primality 302629 (2 : ZMod 302629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 302629 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((25219 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 302629)^151314 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 302629)^100876 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 25219 := Nat.prime_eq_prime_of_dvd_pow hq prime_25219 hd
        subst q
        change (2 : ZMod 302629)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_304537 : Nat.Prime 304537 := by
  apply lucas_primality 304537 (5 : ZMod 304537)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 304537 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((12689 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 304537)^152268 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 304537)^101512 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 12689 := Nat.prime_eq_prime_of_dvd_pow hq prime_12689 hd
        subst q
        change (5 : ZMod 304537)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_304849 : Nat.Prime 304849 := by
  apply lucas_primality 304849 (7 : ZMod 304849)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 304849 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((29 : ℕ)^1 * ((73 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 304849)^152424 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 304849)^101616 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (7 : ZMod 304849)^10512 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
          subst q
          change (7 : ZMod 304849)^4176 ≠ 1
          reduce_mod_char
          decide

theorem prime_305069 : Nat.Prime 305069 := by
  apply lucas_primality 305069 (2 : ZMod 305069)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 305069 - 1 = (2 : ℕ)^2 * ((53 : ℕ)^1 * ((1439 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 305069)^152534 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
        subst q
        change (2 : ZMod 305069)^5756 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1439 := Nat.prime_eq_prime_of_dvd_pow hq prime_1439 hd
        subst q
        change (2 : ZMod 305069)^212 ≠ 1
        reduce_mod_char
        decide

theorem prime_308681 : Nat.Prime 308681 := by
  apply lucas_primality 308681 (11 : ZMod 308681)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 308681 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((7717 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 308681)^154340 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 308681)^61736 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7717 := Nat.prime_eq_prime_of_dvd_pow hq prime_7717 hd
        subst q
        change (11 : ZMod 308681)^40 ≠ 1
        reduce_mod_char
        decide

theorem prime_308827 : Nat.Prime 308827 := by
  apply lucas_primality 308827 (2 : ZMod 308827)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 308827 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((19 : ℕ)^1 * ((43 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 308827)^154413 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 308827)^102942 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 308827)^44118 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (2 : ZMod 308827)^16254 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (2 : ZMod 308827)^7182 ≠ 1
            reduce_mod_char
            decide

theorem prime_308989 : Nat.Prime 308989 := by
  apply lucas_primality 308989 (2 : ZMod 308989)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 308989 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((2861 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 308989)^154494 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 308989)^102996 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2861 := Nat.prime_eq_prime_of_dvd_pow hq prime_2861 hd
        subst q
        change (2 : ZMod 308989)^108 ≠ 1
        reduce_mod_char
        decide

theorem prime_311791 : Nat.Prime 311791 := by
  apply lucas_primality 311791 (6 : ZMod 311791)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 311791 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((19 : ℕ)^1 * ((547 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 311791)^155895 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 311791)^103930 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 311791)^62358 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (6 : ZMod 311791)^16410 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 547 := Nat.prime_eq_prime_of_dvd_pow hq prime_547 hd
            subst q
            change (6 : ZMod 311791)^570 ≠ 1
            reduce_mod_char
            decide

theorem prime_312331 : Nat.Prime 312331 := by
  apply lucas_primality 312331 (10 : ZMod 312331)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 312331 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((29 : ℕ)^1 * ((359 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 312331)^156165 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 312331)^104110 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 312331)^62466 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (10 : ZMod 312331)^10770 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 359 := Nat.prime_eq_prime_of_dvd_pow hq prime_359 hd
            subst q
            change (10 : ZMod 312331)^870 ≠ 1
            reduce_mod_char
            decide

theorem prime_315193 : Nat.Prime 315193 := by
  apply lucas_primality 315193 (5 : ZMod 315193)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 315193 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((571 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 315193)^157596 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 315193)^105064 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (5 : ZMod 315193)^13704 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 571 := Nat.prime_eq_prime_of_dvd_pow hq prime_571 hd
          subst q
          change (5 : ZMod 315193)^552 ≠ 1
          reduce_mod_char
          decide

theorem prime_318233 : Nat.Prime 318233 := by
  apply lucas_primality 318233 (3 : ZMod 318233)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 318233 - 1 = (2 : ℕ)^3 * ((39779 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 318233)^159116 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 39779 := Nat.prime_eq_prime_of_dvd_pow hq prime_39779 hd
      subst q
      change (3 : ZMod 318233)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_319097 : Nat.Prime 319097 := by
  apply lucas_primality 319097 (3 : ZMod 319097)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 319097 - 1 = (2 : ℕ)^3 * ((39887 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 319097)^159548 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 39887 := Nat.prime_eq_prime_of_dvd_pow hq prime_39887 hd
      subst q
      change (3 : ZMod 319097)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_320923 : Nat.Prime 320923 := by
  apply lucas_primality 320923 (2 : ZMod 320923)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 320923 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((7 : ℕ)^1 * ((283 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 320923)^160461 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 320923)^106974 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 320923)^45846 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 283 := Nat.prime_eq_prime_of_dvd_pow hq prime_283 hd
          subst q
          change (2 : ZMod 320923)^1134 ≠ 1
          reduce_mod_char
          decide

theorem prime_329803 : Nat.Prime 329803 := by
  apply lucas_primality 329803 (2 : ZMod 329803)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 329803 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((19 : ℕ)^1 * ((263 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 329803)^164901 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 329803)^109934 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 329803)^29982 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (2 : ZMod 329803)^17358 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 263 := Nat.prime_eq_prime_of_dvd_pow hq prime_263 hd
            subst q
            change (2 : ZMod 329803)^1254 ≠ 1
            reduce_mod_char
            decide

theorem prime_330679 : Nat.Prime 330679 := by
  apply lucas_primality 330679 (3 : ZMod 330679)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 330679 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((18371 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 330679)^165339 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 330679)^110226 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 18371 := Nat.prime_eq_prime_of_dvd_pow hq prime_18371 hd
        subst q
        change (3 : ZMod 330679)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_331589 : Nat.Prime 331589 := by
  apply lucas_primality 331589 (2 : ZMod 331589)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 331589 - 1 = (2 : ℕ)^2 * ((19 : ℕ)^1 * ((4363 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 331589)^165794 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 331589)^17452 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4363 := Nat.prime_eq_prime_of_dvd_pow hq prime_4363 hd
        subst q
        change (2 : ZMod 331589)^76 ≠ 1
        reduce_mod_char
        decide

theorem prime_332567 : Nat.Prime 332567 := by
  apply lucas_primality 332567 (5 : ZMod 332567)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 332567 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((12791 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 332567)^166283 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (5 : ZMod 332567)^25582 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 12791 := Nat.prime_eq_prime_of_dvd_pow hq prime_12791 hd
        subst q
        change (5 : ZMod 332567)^26 ≠ 1
        reduce_mod_char
        decide

theorem prime_332573 : Nat.Prime 332573 := by
  apply lucas_primality 332573 (2 : ZMod 332573)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 332573 - 1 = (2 : ℕ)^2 * ((29 : ℕ)^1 * ((47 : ℕ)^1 * ((61 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 332573)^166286 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (2 : ZMod 332573)^11468 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (2 : ZMod 332573)^7076 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (2 : ZMod 332573)^5452 ≠ 1
          reduce_mod_char
          decide

theorem prime_333667 : Nat.Prime 333667 := by
  apply lucas_primality 333667 (2 : ZMod 333667)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 333667 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((37 : ℕ)^1 * ((167 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 333667)^166833 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 333667)^111222 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (2 : ZMod 333667)^9018 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
          subst q
          change (2 : ZMod 333667)^1998 ≠ 1
          reduce_mod_char
          decide

theorem prime_337291 : Nat.Prime 337291 := by
  apply lucas_primality 337291 (10 : ZMod 337291)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 337291 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11243 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 337291)^168645 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 337291)^112430 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 337291)^67458 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11243 := Nat.prime_eq_prime_of_dvd_pow hq prime_11243 hd
          subst q
          change (10 : ZMod 337291)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_340849 : Nat.Prime 340849 := by
  apply lucas_primality 340849 (13 : ZMod 340849)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 340849 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^4 * ((263 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 340849)^170424 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 340849)^113616 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 263 := Nat.prime_eq_prime_of_dvd_pow hq prime_263 hd
        subst q
        change (13 : ZMod 340849)^1296 ≠ 1
        reduce_mod_char
        decide

theorem prime_341227 : Nat.Prime 341227 := by
  apply lucas_primality 341227 (2 : ZMod 341227)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 341227 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((71 : ℕ)^1 * ((89 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 341227)^170613 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 341227)^113742 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
          subst q
          change (2 : ZMod 341227)^4806 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (2 : ZMod 341227)^3834 ≠ 1
          reduce_mod_char
          decide

theorem prime_341641 : Nat.Prime 341641 := by
  apply lucas_primality 341641 (7 : ZMod 341641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 341641 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((73 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 341641)^170820 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 341641)^113880 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 341641)^68328 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (7 : ZMod 341641)^26280 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
            subst q
            change (7 : ZMod 341641)^4680 ≠ 1
            reduce_mod_char
            decide

theorem prime_341813 : Nat.Prime 341813 := by
  apply lucas_primality 341813 (2 : ZMod 341813)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 341813 - 1 = (2 : ℕ)^2 * ((85453 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 341813)^170906 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 85453 := Nat.prime_eq_prime_of_dvd_pow hq prime_85453 hd
      subst q
      change (2 : ZMod 341813)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_342889 : Nat.Prime 342889 := by
  apply lucas_primality 342889 (19 : ZMod 342889)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 342889 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((157 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 342889)^171444 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 342889)^114296 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (19 : ZMod 342889)^48984 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (19 : ZMod 342889)^26376 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
            subst q
            change (19 : ZMod 342889)^2184 ≠ 1
            reduce_mod_char
            decide

theorem prime_344053 : Nat.Prime 344053 := by
  apply lucas_primality 344053 (2 : ZMod 344053)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 344053 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((19 : ℕ)^1 * ((503 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 344053)^172026 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 344053)^114684 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 344053)^18108 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 503 := Nat.prime_eq_prime_of_dvd_pow hq prime_503 hd
          subst q
          change (2 : ZMod 344053)^684 ≠ 1
          reduce_mod_char
          decide

theorem prime_345769 : Nat.Prime 345769 := by
  apply lucas_primality 345769 (11 : ZMod 345769)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 345769 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((14407 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 345769)^172884 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 345769)^115256 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 14407 := Nat.prime_eq_prime_of_dvd_pow hq prime_14407 hd
        subst q
        change (11 : ZMod 345769)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_346867 : Nat.Prime 346867 := by
  apply lucas_primality 346867 (5 : ZMod 346867)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 346867 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((4447 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 346867)^173433 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 346867)^115622 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (5 : ZMod 346867)^26682 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4447 := Nat.prime_eq_prime_of_dvd_pow hq prime_4447 hd
          subst q
          change (5 : ZMod 346867)^78 ≠ 1
          reduce_mod_char
          decide

theorem prime_348077 : Nat.Prime 348077 := by
  apply lucas_primality 348077 (2 : ZMod 348077)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 348077 - 1 = (2 : ℕ)^2 * ((173 : ℕ)^1 * ((503 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 348077)^174038 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
        subst q
        change (2 : ZMod 348077)^2012 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 503 := Nat.prime_eq_prime_of_dvd_pow hq prime_503 hd
        subst q
        change (2 : ZMod 348077)^692 ≠ 1
        reduce_mod_char
        decide

theorem prime_350237 : Nat.Prime 350237 := by
  apply lucas_primality 350237 (2 : ZMod 350237)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 350237 - 1 = (2 : ℕ)^2 * ((87559 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 350237)^175118 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 87559 := Nat.prime_eq_prime_of_dvd_pow hq prime_87559 hd
      subst q
      change (2 : ZMod 350237)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_351179 : Nat.Prime 351179 := by
  apply lucas_primality 351179 (2 : ZMod 351179)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 351179 - 1 = (2 : ℕ)^1 * ((53 : ℕ)^1 * ((3313 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 351179)^175589 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
        subst q
        change (2 : ZMod 351179)^6626 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3313 := Nat.prime_eq_prime_of_dvd_pow hq prime_3313 hd
        subst q
        change (2 : ZMod 351179)^106 ≠ 1
        reduce_mod_char
        decide

theorem prime_351863 : Nat.Prime 351863 := by
  apply lucas_primality 351863 (5 : ZMod 351863)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 351863 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((41 : ℕ)^1 * ((613 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 351863)^175931 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 351863)^50266 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (5 : ZMod 351863)^8582 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 613 := Nat.prime_eq_prime_of_dvd_pow hq prime_613 hd
          subst q
          change (5 : ZMod 351863)^574 ≠ 1
          reduce_mod_char
          decide

theorem prime_352123 : Nat.Prime 352123 := by
  apply lucas_primality 352123 (3 : ZMod 352123)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 352123 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((58687 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 352123)^176061 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 352123)^117374 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 58687 := Nat.prime_eq_prime_of_dvd_pow hq prime_58687 hd
        subst q
        change (3 : ZMod 352123)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_353161 : Nat.Prime 353161 := by
  apply lucas_primality 353161 (22 : ZMod 353161)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 353161 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^4 * ((5 : ℕ)^1 * ((109 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (22 : ZMod 353161)^176580 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (22 : ZMod 353161)^117720 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (22 : ZMod 353161)^70632 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
          subst q
          change (22 : ZMod 353161)^3240 ≠ 1
          reduce_mod_char
          decide

theorem prime_353489 : Nat.Prime 353489 := by
  apply lucas_primality 353489 (3 : ZMod 353489)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 353489 - 1 = (2 : ℕ)^4 * ((22093 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 353489)^176744 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 22093 := Nat.prime_eq_prime_of_dvd_pow hq prime_22093 hd
      subst q
      change (3 : ZMod 353489)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_354017 : Nat.Prime 354017 := by
  apply lucas_primality 354017 (3 : ZMod 354017)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 354017 - 1 = (2 : ℕ)^5 * ((13 : ℕ)^1 * ((23 : ℕ)^1 * ((37 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 354017)^177008 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 354017)^27232 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (3 : ZMod 354017)^15392 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (3 : ZMod 354017)^9568 ≠ 1
          reduce_mod_char
          decide

theorem prime_357613 : Nat.Prime 357613 := by
  apply lucas_primality 357613 (2 : ZMod 357613)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 357613 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((1753 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 357613)^178806 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 357613)^119204 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 357613)^21036 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1753 := Nat.prime_eq_prime_of_dvd_pow hq prime_1753 hd
          subst q
          change (2 : ZMod 357613)^204 ≠ 1
          reduce_mod_char
          decide

theorem prime_362381 : Nat.Prime 362381 := by
  apply lucas_primality 362381 (2 : ZMod 362381)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 362381 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((18119 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 362381)^181190 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 362381)^72476 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 18119 := Nat.prime_eq_prime_of_dvd_pow hq prime_18119 hd
        subst q
        change (2 : ZMod 362381)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_363947 : Nat.Prime 363947 := by
  apply lucas_primality 363947 (2 : ZMod 363947)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 363947 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((71 : ℕ)^1 * ((233 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 363947)^181973 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 363947)^33086 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
          subst q
          change (2 : ZMod 363947)^5126 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
          subst q
          change (2 : ZMod 363947)^1562 ≠ 1
          reduce_mod_char
          decide

theorem prime_364213 : Nat.Prime 364213 := by
  apply lucas_primality 364213 (2 : ZMod 364213)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 364213 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((67 : ℕ)^1 * ((151 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 364213)^182106 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 364213)^121404 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (2 : ZMod 364213)^5436 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
          subst q
          change (2 : ZMod 364213)^2412 ≠ 1
          reduce_mod_char
          decide

theorem prime_364379 : Nat.Prime 364379 := by
  apply lucas_primality 364379 (2 : ZMod 364379)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 364379 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((17 : ℕ)^1 * ((1531 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 364379)^182189 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 364379)^52054 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 364379)^21434 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1531 := Nat.prime_eq_prime_of_dvd_pow hq prime_1531 hd
          subst q
          change (2 : ZMod 364379)^238 ≠ 1
          reduce_mod_char
          decide

theorem prime_367519 : Nat.Prime 367519 := by
  apply lucas_primality 367519 (3 : ZMod 367519)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 367519 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((61253 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 367519)^183759 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 367519)^122506 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 61253 := Nat.prime_eq_prime_of_dvd_pow hq prime_61253 hd
        subst q
        change (3 : ZMod 367519)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_368609 : Nat.Prime 368609 := by
  apply lucas_primality 368609 (3 : ZMod 368609)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 368609 - 1 = (2 : ℕ)^5 * ((11519 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 368609)^184304 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 11519 := Nat.prime_eq_prime_of_dvd_pow hq prime_11519 hd
      subst q
      change (3 : ZMod 368609)^32 ≠ 1
      reduce_mod_char
      decide

theorem prime_371561 : Nat.Prime 371561 := by
  apply lucas_primality 371561 (3 : ZMod 371561)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 371561 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((1327 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 371561)^185780 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 371561)^74312 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 371561)^53080 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1327 := Nat.prime_eq_prime_of_dvd_pow hq prime_1327 hd
          subst q
          change (3 : ZMod 371561)^280 ≠ 1
          reduce_mod_char
          decide

theorem prime_372223 : Nat.Prime 372223 := by
  apply lucas_primality 372223 (3 : ZMod 372223)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 372223 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((61 : ℕ)^1 * ((113 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 372223)^186111 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 372223)^124074 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (3 : ZMod 372223)^6102 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
          subst q
          change (3 : ZMod 372223)^3294 ≠ 1
          reduce_mod_char
          decide

theorem prime_378967 : Nat.Prime 378967 := by
  apply lucas_primality 378967 (3 : ZMod 378967)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 378967 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((1289 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 378967)^189483 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 378967)^126322 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 378967)^54138 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1289 := Nat.prime_eq_prime_of_dvd_pow hq prime_1289 hd
          subst q
          change (3 : ZMod 378967)^294 ≠ 1
          reduce_mod_char
          decide

theorem prime_380059 : Nat.Prime 380059 := by
  apply lucas_primality 380059 (2 : ZMod 380059)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 380059 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((9049 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 380059)^190029 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 380059)^126686 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 380059)^54294 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 9049 := Nat.prime_eq_prime_of_dvd_pow hq prime_9049 hd
          subst q
          change (2 : ZMod 380059)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_383837 : Nat.Prime 383837 := by
  apply lucas_primality 383837 (2 : ZMod 383837)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 383837 - 1 = (2 : ℕ)^2 * ((95959 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 383837)^191918 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 95959 := Nat.prime_eq_prime_of_dvd_pow hq prime_95959 hd
      subst q
      change (2 : ZMod 383837)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_384367 : Nat.Prime 384367 := by
  apply lucas_primality 384367 (5 : ZMod 384367)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 384367 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((29 : ℕ)^1 * ((47 : ℕ)^2))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 384367)^192183 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 384367)^128122 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (5 : ZMod 384367)^13254 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (5 : ZMod 384367)^8178 ≠ 1
          reduce_mod_char
          decide

theorem prime_386263 : Nat.Prime 386263 := by
  apply lucas_primality 386263 (5 : ZMod 386263)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 386263 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((23 : ℕ)^1 * ((311 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 386263)^193131 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 386263)^128754 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (5 : ZMod 386263)^16794 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 311 := Nat.prime_eq_prime_of_dvd_pow hq prime_311 hd
          subst q
          change (5 : ZMod 386263)^1242 ≠ 1
          reduce_mod_char
          decide

theorem prime_387071 : Nat.Prime 387071 := by
  apply lucas_primality 387071 (22 : ZMod 387071)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 387071 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((38707 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (22 : ZMod 387071)^193535 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (22 : ZMod 387071)^77414 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 38707 := Nat.prime_eq_prime_of_dvd_pow hq prime_38707 hd
        subst q
        change (22 : ZMod 387071)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_390161 : Nat.Prime 390161 := by
  apply lucas_primality 390161 (3 : ZMod 390161)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 390161 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((4877 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 390161)^195080 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 390161)^78032 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4877 := Nat.prime_eq_prime_of_dvd_pow hq prime_4877 hd
        subst q
        change (3 : ZMod 390161)^80 ≠ 1
        reduce_mod_char
        decide

theorem prime_390307 : Nat.Prime 390307 := by
  apply lucas_primality 390307 (3 : ZMod 390307)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 390307 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((9293 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 390307)^195153 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 390307)^130102 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 390307)^55758 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 9293 := Nat.prime_eq_prime_of_dvd_pow hq prime_9293 hd
          subst q
          change (3 : ZMod 390307)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_390373 : Nat.Prime 390373 := by
  apply lucas_primality 390373 (2 : ZMod 390373)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 390373 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((32531 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 390373)^195186 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 390373)^130124 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 32531 := Nat.prime_eq_prime_of_dvd_pow hq prime_32531 hd
        subst q
        change (2 : ZMod 390373)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_392053 : Nat.Prime 392053 := by
  apply lucas_primality 392053 (2 : ZMod 392053)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 392053 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((37 : ℕ)^1 * ((883 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 392053)^196026 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 392053)^130684 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (2 : ZMod 392053)^10596 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 883 := Nat.prime_eq_prime_of_dvd_pow hq prime_883 hd
          subst q
          change (2 : ZMod 392053)^444 ≠ 1
          reduce_mod_char
          decide

theorem prime_392443 : Nat.Prime 392443 := by
  apply lucas_primality 392443 (5 : ZMod 392443)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 392443 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((65407 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 392443)^196221 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 392443)^130814 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 65407 := Nat.prime_eq_prime_of_dvd_pow hq prime_65407 hd
        subst q
        change (5 : ZMod 392443)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_394363 : Nat.Prime 394363 := by
  apply lucas_primality 394363 (2 : ZMod 394363)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 394363 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((67 : ℕ)^1 * ((109 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 394363)^197181 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 394363)^131454 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (2 : ZMod 394363)^5886 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
          subst q
          change (2 : ZMod 394363)^3618 ≠ 1
          reduce_mod_char
          decide

theorem prime_396667 : Nat.Prime 396667 := by
  apply lucas_primality 396667 (3 : ZMod 396667)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 396667 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((22037 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 396667)^198333 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 396667)^132222 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 22037 := Nat.prime_eq_prime_of_dvd_pow hq prime_22037 hd
        subst q
        change (3 : ZMod 396667)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_398117 : Nat.Prime 398117 := by
  apply lucas_primality 398117 (2 : ZMod 398117)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 398117 - 1 = (2 : ℕ)^2 * ((99529 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 398117)^199058 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 99529 := Nat.prime_eq_prime_of_dvd_pow hq prime_99529 hd
      subst q
      change (2 : ZMod 398117)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_399353 : Nat.Prime 399353 := by
  apply lucas_primality 399353 (3 : ZMod 399353)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 399353 - 1 = (2 : ℕ)^3 * ((49919 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 399353)^199676 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 49919 := Nat.prime_eq_prime_of_dvd_pow hq prime_49919 hd
      subst q
      change (3 : ZMod 399353)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_400199 : Nat.Prime 400199 := by
  apply lucas_primality 400199 (7 : ZMod 400199)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 400199 - 1 = (2 : ℕ)^1 * ((401 : ℕ)^1 * ((499 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 400199)^200099 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 401 := Nat.prime_eq_prime_of_dvd_pow hq prime_401 hd
        subst q
        change (7 : ZMod 400199)^998 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 499 := Nat.prime_eq_prime_of_dvd_pow hq prime_499 hd
        subst q
        change (7 : ZMod 400199)^802 ≠ 1
        reduce_mod_char
        decide

theorem prime_400277 : Nat.Prime 400277 := by
  apply lucas_primality 400277 (2 : ZMod 400277)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 400277 - 1 = (2 : ℕ)^2 * ((100069 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 400277)^200138 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 100069 := Nat.prime_eq_prime_of_dvd_pow hq prime_100069 hd
      subst q
      change (2 : ZMod 400277)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_402023 : Nat.Prime 402023 := by
  apply lucas_primality 402023 (5 : ZMod 402023)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 402023 - 1 = (2 : ℕ)^1 * ((201011 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 402023)^201011 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 201011 := Nat.prime_eq_prime_of_dvd_pow hq prime_201011 hd
      subst q
      change (5 : ZMod 402023)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_403163 : Nat.Prime 403163 := by
  apply lucas_primality 403163 (2 : ZMod 403163)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 403163 - 1 = (2 : ℕ)^1 * ((201581 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 403163)^201581 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 201581 := Nat.prime_eq_prime_of_dvd_pow hq prime_201581 hd
      subst q
      change (2 : ZMod 403163)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_403603 : Nat.Prime 403603 := by
  apply lucas_primality 403603 (2 : ZMod 403603)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 403603 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((137 : ℕ)^1 * ((491 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 403603)^201801 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 403603)^134534 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
          subst q
          change (2 : ZMod 403603)^2946 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 491 := Nat.prime_eq_prime_of_dvd_pow hq prime_491 hd
          subst q
          change (2 : ZMod 403603)^822 ≠ 1
          reduce_mod_char
          decide

theorem prime_404399 : Nat.Prime 404399 := by
  apply lucas_primality 404399 (7 : ZMod 404399)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 404399 - 1 = (2 : ℕ)^1 * ((241 : ℕ)^1 * ((839 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 404399)^202199 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 241 := Nat.prime_eq_prime_of_dvd_pow hq prime_241 hd
        subst q
        change (7 : ZMod 404399)^1678 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 839 := Nat.prime_eq_prime_of_dvd_pow hq prime_839 hd
        subst q
        change (7 : ZMod 404399)^482 ≠ 1
        reduce_mod_char
        decide

theorem prime_405487 : Nat.Prime 405487 := by
  apply lucas_primality 405487 (3 : ZMod 405487)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 405487 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((2503 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 405487)^202743 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 405487)^135162 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2503 := Nat.prime_eq_prime_of_dvd_pow hq prime_2503 hd
        subst q
        change (3 : ZMod 405487)^162 ≠ 1
        reduce_mod_char
        decide

theorem prime_406631 : Nat.Prime 406631 := by
  apply lucas_primality 406631 (7 : ZMod 406631)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 406631 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((37 : ℕ)^1 * ((157 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 406631)^203315 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 406631)^81326 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 406631)^58090 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
            subst q
            change (7 : ZMod 406631)^10990 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
            subst q
            change (7 : ZMod 406631)^2590 ≠ 1
            reduce_mod_char
            decide

theorem prime_407377 : Nat.Prime 407377 := by
  apply lucas_primality 407377 (7 : ZMod 407377)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 407377 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^3 * ((23 : ℕ)^1 * ((41 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 407377)^203688 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 407377)^135792 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (7 : ZMod 407377)^17712 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (7 : ZMod 407377)^9936 ≠ 1
          reduce_mod_char
          decide

theorem prime_409289 : Nat.Prime 409289 := by
  apply lucas_primality 409289 (3 : ZMod 409289)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 409289 - 1 = (2 : ℕ)^3 * ((11 : ℕ)^1 * ((4651 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 409289)^204644 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 409289)^37208 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4651 := Nat.prime_eq_prime_of_dvd_pow hq prime_4651 hd
        subst q
        change (3 : ZMod 409289)^88 ≠ 1
        reduce_mod_char
        decide

theorem prime_409369 : Nat.Prime 409369 := by
  apply lucas_primality 409369 (19 : ZMod 409369)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 409369 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((37 : ℕ)^1 * ((461 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 409369)^204684 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 409369)^136456 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (19 : ZMod 409369)^11064 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 461 := Nat.prime_eq_prime_of_dvd_pow hq prime_461 hd
          subst q
          change (19 : ZMod 409369)^888 ≠ 1
          reduce_mod_char
          decide

theorem prime_423323 : Nat.Prime 423323 := by
  apply lucas_primality 423323 (2 : ZMod 423323)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 423323 - 1 = (2 : ℕ)^1 * ((211661 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 423323)^211661 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 211661 := Nat.prime_eq_prime_of_dvd_pow hq prime_211661 hd
      subst q
      change (2 : ZMod 423323)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_423601 : Nat.Prime 423601 := by
  apply lucas_primality 423601 (7 : ZMod 423601)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 423601 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((353 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 423601)^211800 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 423601)^141200 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 423601)^84720 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 353 := Nat.prime_eq_prime_of_dvd_pow hq prime_353 hd
          subst q
          change (7 : ZMod 423601)^1200 ≠ 1
          reduce_mod_char
          decide

theorem prime_426889 : Nat.Prime 426889 := by
  apply lucas_primality 426889 (13 : ZMod 426889)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 426889 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((7 : ℕ)^2 * ((11 : ℕ)^2))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 426889)^213444 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 426889)^142296 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (13 : ZMod 426889)^60984 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (13 : ZMod 426889)^38808 ≠ 1
          reduce_mod_char
          decide

theorem prime_427789 : Nat.Prime 427789 := by
  apply lucas_primality 427789 (6 : ZMod 427789)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 427789 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((17 : ℕ)^1 * ((233 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 427789)^213894 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 427789)^142596 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (6 : ZMod 427789)^25164 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
          subst q
          change (6 : ZMod 427789)^1836 ≠ 1
          reduce_mod_char
          decide

theorem prime_428003 : Nat.Prime 428003 := by
  apply lucas_primality 428003 (2 : ZMod 428003)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 428003 - 1 = (2 : ℕ)^1 * ((173 : ℕ)^1 * ((1237 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 428003)^214001 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
        subst q
        change (2 : ZMod 428003)^2474 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1237 := Nat.prime_eq_prime_of_dvd_pow hq prime_1237 hd
        subst q
        change (2 : ZMod 428003)^346 ≠ 1
        reduce_mod_char
        decide

theorem prime_432053 : Nat.Prime 432053 := by
  apply lucas_primality 432053 (2 : ZMod 432053)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 432053 - 1 = (2 : ℕ)^2 * ((108013 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 432053)^216026 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 108013 := Nat.prime_eq_prime_of_dvd_pow hq prime_108013 hd
      subst q
      change (2 : ZMod 432053)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_435371 : Nat.Prime 435371 := by
  apply lucas_primality 435371 (6 : ZMod 435371)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 435371 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((17 : ℕ)^1 * ((197 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 435371)^217685 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 435371)^87074 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (6 : ZMod 435371)^33490 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (6 : ZMod 435371)^25610 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
            subst q
            change (6 : ZMod 435371)^2210 ≠ 1
            reduce_mod_char
            decide

theorem prime_435949 : Nat.Prime 435949 := by
  apply lucas_primality 435949 (6 : ZMod 435949)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 435949 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((2137 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 435949)^217974 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 435949)^145316 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (6 : ZMod 435949)^25644 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2137 := Nat.prime_eq_prime_of_dvd_pow hq prime_2137 hd
          subst q
          change (6 : ZMod 435949)^204 ≠ 1
          reduce_mod_char
          decide

theorem prime_436547 : Nat.Prime 436547 := by
  apply lucas_primality 436547 (2 : ZMod 436547)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 436547 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((19843 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 436547)^218273 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 436547)^39686 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 19843 := Nat.prime_eq_prime_of_dvd_pow hq prime_19843 hd
        subst q
        change (2 : ZMod 436547)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_437191 : Nat.Prime 437191 := by
  apply lucas_primality 437191 (6 : ZMod 437191)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 437191 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((19 : ℕ)^1 * ((59 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 437191)^218595 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 437191)^145730 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 437191)^87438 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (6 : ZMod 437191)^33630 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
              subst q
              change (6 : ZMod 437191)^23010 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
              subst q
              change (6 : ZMod 437191)^7410 ≠ 1
              reduce_mod_char
              decide

theorem prime_437809 : Nat.Prime 437809 := by
  apply lucas_primality 437809 (26 : ZMod 437809)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 437809 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((1303 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (26 : ZMod 437809)^218904 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (26 : ZMod 437809)^145936 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (26 : ZMod 437809)^62544 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1303 := Nat.prime_eq_prime_of_dvd_pow hq prime_1303 hd
          subst q
          change (26 : ZMod 437809)^336 ≠ 1
          reduce_mod_char
          decide

theorem prime_437959 : Nat.Prime 437959 := by
  apply lucas_primality 437959 (3 : ZMod 437959)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 437959 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((29 : ℕ)^1 * ((839 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 437959)^218979 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 437959)^145986 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (3 : ZMod 437959)^15102 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 839 := Nat.prime_eq_prime_of_dvd_pow hq prime_839 hd
          subst q
          change (3 : ZMod 437959)^522 ≠ 1
          reduce_mod_char
          decide

theorem prime_438241 : Nat.Prime 438241 := by
  apply lucas_primality 438241 (13 : ZMod 438241)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 438241 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((83 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 438241)^219120 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 438241)^146080 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 438241)^87648 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (13 : ZMod 438241)^39840 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
            subst q
            change (13 : ZMod 438241)^5280 ≠ 1
            reduce_mod_char
            decide

theorem prime_442571 : Nat.Prime 442571 := by
  apply lucas_primality 442571 (2 : ZMod 442571)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 442571 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((44257 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 442571)^221285 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 442571)^88514 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 44257 := Nat.prime_eq_prime_of_dvd_pow hq prime_44257 hd
        subst q
        change (2 : ZMod 442571)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_445433 : Nat.Prime 445433 := by
  apply lucas_primality 445433 (3 : ZMod 445433)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 445433 - 1 = (2 : ℕ)^3 * ((13 : ℕ)^1 * ((4283 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 445433)^222716 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 445433)^34264 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4283 := Nat.prime_eq_prime_of_dvd_pow hq prime_4283 hd
        subst q
        change (3 : ZMod 445433)^104 ≠ 1
        reduce_mod_char
        decide

theorem prime_445853 : Nat.Prime 445853 := by
  apply lucas_primality 445853 (2 : ZMod 445853)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 445853 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((10133 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 445853)^222926 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 445853)^40532 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 10133 := Nat.prime_eq_prime_of_dvd_pow hq prime_10133 hd
        subst q
        change (2 : ZMod 445853)^44 ≠ 1
        reduce_mod_char
        decide

theorem prime_445937 : Nat.Prime 445937 := by
  apply lucas_primality 445937 (3 : ZMod 445937)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 445937 - 1 = (2 : ℕ)^4 * ((47 : ℕ)^1 * ((593 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 445937)^222968 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (3 : ZMod 445937)^9488 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 593 := Nat.prime_eq_prime_of_dvd_pow hq prime_593 hd
        subst q
        change (3 : ZMod 445937)^752 ≠ 1
        reduce_mod_char
        decide

theorem prime_449399 : Nat.Prime 449399 := by
  apply lucas_primality 449399 (11 : ZMod 449399)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 449399 - 1 = (2 : ℕ)^1 * ((224699 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 449399)^224699 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 224699 := Nat.prime_eq_prime_of_dvd_pow hq prime_224699 hd
      subst q
      change (11 : ZMod 449399)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_451637 : Nat.Prime 451637 := by
  apply lucas_primality 451637 (2 : ZMod 451637)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 451637 - 1 = (2 : ℕ)^2 * ((112909 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 451637)^225818 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 112909 := Nat.prime_eq_prime_of_dvd_pow hq prime_112909 hd
      subst q
      change (2 : ZMod 451637)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_453667 : Nat.Prime 453667 := by
  apply lucas_primality 453667 (2 : ZMod 453667)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 453667 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((75611 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 453667)^226833 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 453667)^151222 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 75611 := Nat.prime_eq_prime_of_dvd_pow hq prime_75611 hd
        subst q
        change (2 : ZMod 453667)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_454229 : Nat.Prime 454229 := by
  apply lucas_primality 454229 (2 : ZMod 454229)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 454229 - 1 = (2 : ℕ)^2 * ((113557 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 454229)^227114 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 113557 := Nat.prime_eq_prime_of_dvd_pow hq prime_113557 hd
      subst q
      change (2 : ZMod 454229)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_456047 : Nat.Prime 456047 := by
  apply lucas_primality 456047 (5 : ZMod 456047)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 456047 - 1 = (2 : ℕ)^1 * ((228023 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 456047)^228023 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 228023 := Nat.prime_eq_prime_of_dvd_pow hq prime_228023 hd
      subst q
      change (5 : ZMod 456047)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_456503 : Nat.Prime 456503 := by
  apply lucas_primality 456503 (5 : ZMod 456503)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 456503 - 1 = (2 : ℕ)^1 * ((228251 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 456503)^228251 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 228251 := Nat.prime_eq_prime_of_dvd_pow hq prime_228251 hd
      subst q
      change (5 : ZMod 456503)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_458567 : Nat.Prime 458567 := by
  apply lucas_primality 458567 (5 : ZMod 458567)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 458567 - 1 = (2 : ℕ)^1 * ((229283 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 458567)^229283 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 229283 := Nat.prime_eq_prime_of_dvd_pow hq prime_229283 hd
      subst q
      change (5 : ZMod 458567)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_459181 : Nat.Prime 459181 := by
  apply lucas_primality 459181 (2 : ZMod 459181)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 459181 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((2551 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 459181)^229590 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 459181)^153060 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 459181)^91836 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2551 := Nat.prime_eq_prime_of_dvd_pow hq prime_2551 hd
          subst q
          change (2 : ZMod 459181)^180 ≠ 1
          reduce_mod_char
          decide

theorem prime_459691 : Nat.Prime 459691 := by
  apply lucas_primality 459691 (3 : ZMod 459691)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 459691 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((199 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 459691)^229845 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 459691)^153230 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 459691)^91938 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (3 : ZMod 459691)^65670 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
              subst q
              change (3 : ZMod 459691)^41790 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 199 := Nat.prime_eq_prime_of_dvd_pow hq prime_199 hd
              subst q
              change (3 : ZMod 459691)^2310 ≠ 1
              reduce_mod_char
              decide

theorem prime_463291 : Nat.Prime 463291 := by
  apply lucas_primality 463291 (12 : ZMod 463291)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 463291 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((15443 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (12 : ZMod 463291)^231645 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (12 : ZMod 463291)^154430 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (12 : ZMod 463291)^92658 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 15443 := Nat.prime_eq_prime_of_dvd_pow hq prime_15443 hd
          subst q
          change (12 : ZMod 463291)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_465161 : Nat.Prime 465161 := by
  apply lucas_primality 465161 (3 : ZMod 465161)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 465161 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((29 : ℕ)^1 * ((401 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 465161)^232580 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 465161)^93032 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (3 : ZMod 465161)^16040 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 401 := Nat.prime_eq_prime_of_dvd_pow hq prime_401 hd
          subst q
          change (3 : ZMod 465161)^1160 ≠ 1
          reduce_mod_char
          decide

theorem prime_471301 : Nat.Prime 471301 := by
  apply lucas_primality 471301 (7 : ZMod 471301)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 471301 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((1571 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 471301)^235650 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 471301)^157100 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 471301)^94260 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1571 := Nat.prime_eq_prime_of_dvd_pow hq prime_1571 hd
          subst q
          change (7 : ZMod 471301)^300 ≠ 1
          reduce_mod_char
          decide

theorem prime_473611 : Nat.Prime 473611 := by
  apply lucas_primality 473611 (2 : ZMod 473611)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 473611 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((15787 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 473611)^236805 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 473611)^157870 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 473611)^94722 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 15787 := Nat.prime_eq_prime_of_dvd_pow hq prime_15787 hd
          subst q
          change (2 : ZMod 473611)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_474779 : Nat.Prime 474779 := by
  apply lucas_primality 474779 (2 : ZMod 474779)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 474779 - 1 = (2 : ℕ)^1 * ((277 : ℕ)^1 * ((857 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 474779)^237389 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 277 := Nat.prime_eq_prime_of_dvd_pow hq prime_277 hd
        subst q
        change (2 : ZMod 474779)^1714 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 857 := Nat.prime_eq_prime_of_dvd_pow hq prime_857 hd
        subst q
        change (2 : ZMod 474779)^554 ≠ 1
        reduce_mod_char
        decide

theorem prime_477131 : Nat.Prime 477131 := by
  apply lucas_primality 477131 (2 : ZMod 477131)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 477131 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((47713 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 477131)^238565 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 477131)^95426 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 47713 := Nat.prime_eq_prime_of_dvd_pow hq prime_47713 hd
        subst q
        change (2 : ZMod 477131)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_477727 : Nat.Prime 477727 := by
  apply lucas_primality 477727 (3 : ZMod 477727)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 477727 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((79621 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 477727)^238863 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 477727)^159242 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 79621 := Nat.prime_eq_prime_of_dvd_pow hq prime_79621 hd
        subst q
        change (3 : ZMod 477727)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_478099 : Nat.Prime 478099 := by
  apply lucas_primality 478099 (3 : ZMod 478099)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 478099 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((26561 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 478099)^239049 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 478099)^159366 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 26561 := Nat.prime_eq_prime_of_dvd_pow hq prime_26561 hd
        subst q
        change (3 : ZMod 478099)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_478843 : Nat.Prime 478843 := by
  apply lucas_primality 478843 (2 : ZMod 478843)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 478843 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((877 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 478843)^239421 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 478843)^159614 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 478843)^68406 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (2 : ZMod 478843)^36834 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 877 := Nat.prime_eq_prime_of_dvd_pow hq prime_877 hd
            subst q
            change (2 : ZMod 478843)^546 ≠ 1
            reduce_mod_char
            decide

theorem prime_482773 : Nat.Prime 482773 := by
  apply lucas_primality 482773 (5 : ZMod 482773)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 482773 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((40231 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 482773)^241386 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 482773)^160924 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 40231 := Nat.prime_eq_prime_of_dvd_pow hq prime_40231 hd
        subst q
        change (5 : ZMod 482773)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_484207 : Nat.Prime 484207 := by
  apply lucas_primality 484207 (3 : ZMod 484207)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 484207 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((80701 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 484207)^242103 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 484207)^161402 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 80701 := Nat.prime_eq_prime_of_dvd_pow hq prime_80701 hd
        subst q
        change (3 : ZMod 484207)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_485101 : Nat.Prime 485101 := by
  apply lucas_primality 485101 (6 : ZMod 485101)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 485101 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^2 * ((7 : ℕ)^2 * ((11 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 485101)^242550 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 485101)^161700 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 485101)^97020 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (6 : ZMod 485101)^69300 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (6 : ZMod 485101)^44100 ≠ 1
            reduce_mod_char
            decide

theorem prime_487423 : Nat.Prime 487423 := by
  apply lucas_primality 487423 (3 : ZMod 487423)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 487423 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((13 : ℕ)^1 * ((2083 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 487423)^243711 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 487423)^162474 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 487423)^37494 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2083 := Nat.prime_eq_prime_of_dvd_pow hq prime_2083 hd
          subst q
          change (3 : ZMod 487423)^234 ≠ 1
          reduce_mod_char
          decide

theorem prime_489613 : Nat.Prime 489613 := by
  apply lucas_primality 489613 (5 : ZMod 489613)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 489613 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((40801 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 489613)^244806 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 489613)^163204 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 40801 := Nat.prime_eq_prime_of_dvd_pow hq prime_40801 hd
        subst q
        change (5 : ZMod 489613)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_490921 : Nat.Prime 490921 := by
  apply lucas_primality 490921 (13 : ZMod 490921)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 490921 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((4091 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 490921)^245460 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 490921)^163640 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 490921)^98184 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4091 := Nat.prime_eq_prime_of_dvd_pow hq prime_4091 hd
          subst q
          change (13 : ZMod 490921)^120 ≠ 1
          reduce_mod_char
          decide

theorem prime_491083 : Nat.Prime 491083 := by
  apply lucas_primality 491083 (2 : ZMod 491083)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 491083 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((81847 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 491083)^245541 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 491083)^163694 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 81847 := Nat.prime_eq_prime_of_dvd_pow hq prime_81847 hd
        subst q
        change (2 : ZMod 491083)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_492113 : Nat.Prime 492113 := by
  apply lucas_primality 492113 (3 : ZMod 492113)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 492113 - 1 = (2 : ℕ)^4 * ((30757 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 492113)^246056 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 30757 := Nat.prime_eq_prime_of_dvd_pow hq prime_30757 hd
      subst q
      change (3 : ZMod 492113)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_495563 : Nat.Prime 495563 := by
  apply lucas_primality 495563 (2 : ZMod 495563)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 495563 - 1 = (2 : ℕ)^1 * ((247781 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 495563)^247781 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 247781 := Nat.prime_eq_prime_of_dvd_pow hq prime_247781 hd
      subst q
      change (2 : ZMod 495563)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_495893 : Nat.Prime 495893 := by
  apply lucas_primality 495893 (2 : ZMod 495893)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 495893 - 1 = (2 : ℕ)^2 * ((123973 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 495893)^247946 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 123973 := Nat.prime_eq_prime_of_dvd_pow hq prime_123973 hd
      subst q
      change (2 : ZMod 495893)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_496291 : Nat.Prime 496291 := by
  apply lucas_primality 496291 (12 : ZMod 496291)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 496291 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((71 : ℕ)^1 * ((233 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (12 : ZMod 496291)^248145 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (12 : ZMod 496291)^165430 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (12 : ZMod 496291)^99258 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
            subst q
            change (12 : ZMod 496291)^6990 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
            subst q
            change (12 : ZMod 496291)^2130 ≠ 1
            reduce_mod_char
            decide

theorem prime_496399 : Nat.Prime 496399 := by
  apply lucas_primality 496399 (3 : ZMod 496399)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 496399 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((53 : ℕ)^1 * ((223 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 496399)^248199 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 496399)^165466 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 496399)^70914 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
            subst q
            change (3 : ZMod 496399)^9366 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 223 := Nat.prime_eq_prime_of_dvd_pow hq prime_223 hd
            subst q
            change (3 : ZMod 496399)^2226 ≠ 1
            reduce_mod_char
            decide

theorem prime_497509 : Nat.Prime 497509 := by
  apply lucas_primality 497509 (6 : ZMod 497509)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 497509 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((3769 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 497509)^248754 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 497509)^165836 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (6 : ZMod 497509)^45228 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3769 := Nat.prime_eq_prime_of_dvd_pow hq prime_3769 hd
          subst q
          change (6 : ZMod 497509)^132 ≠ 1
          reduce_mod_char
          decide

theorem prime_500231 : Nat.Prime 500231 := by
  apply lucas_primality 500231 (14 : ZMod 500231)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 500231 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((50023 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 500231)^250115 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (14 : ZMod 500231)^100046 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 50023 := Nat.prime_eq_prime_of_dvd_pow hq prime_50023 hd
        subst q
        change (14 : ZMod 500231)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_500393 : Nat.Prime 500393 := by
  apply lucas_primality 500393 (3 : ZMod 500393)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 500393 - 1 = (2 : ℕ)^3 * ((62549 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 500393)^250196 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 62549 := Nat.prime_eq_prime_of_dvd_pow hq prime_62549 hd
      subst q
      change (3 : ZMod 500393)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_502321 : Nat.Prime 502321 := by
  apply lucas_primality 502321 (17 : ZMod 502321)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 502321 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((23 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 502321)^251160 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 502321)^167440 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (17 : ZMod 502321)^100464 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (17 : ZMod 502321)^71760 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
              subst q
              change (17 : ZMod 502321)^38640 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
              subst q
              change (17 : ZMod 502321)^21840 ≠ 1
              reduce_mod_char
              decide

theorem prime_502421 : Nat.Prime 502421 := by
  apply lucas_primality 502421 (2 : ZMod 502421)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 502421 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((25121 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 502421)^251210 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 502421)^100484 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 25121 := Nat.prime_eq_prime_of_dvd_pow hq prime_25121 hd
        subst q
        change (2 : ZMod 502421)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_504389 : Nat.Prime 504389 := by
  apply lucas_primality 504389 (2 : ZMod 504389)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 504389 - 1 = (2 : ℕ)^2 * ((126097 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 504389)^252194 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 126097 := Nat.prime_eq_prime_of_dvd_pow hq prime_126097 hd
      subst q
      change (2 : ZMod 504389)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_506083 : Nat.Prime 506083 := by
  apply lucas_primality 506083 (2 : ZMod 506083)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 506083 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((84347 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 506083)^253041 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 506083)^168694 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 84347 := Nat.prime_eq_prime_of_dvd_pow hq prime_84347 hd
        subst q
        change (2 : ZMod 506083)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_508943 : Nat.Prime 508943 := by
  apply lucas_primality 508943 (5 : ZMod 508943)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 508943 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((36353 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 508943)^254471 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 508943)^72706 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 36353 := Nat.prime_eq_prime_of_dvd_pow hq prime_36353 hd
        subst q
        change (5 : ZMod 508943)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_510751 : Nat.Prime 510751 := by
  apply lucas_primality 510751 (15 : ZMod 510751)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 510751 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^3 * ((227 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (15 : ZMod 510751)^255375 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (15 : ZMod 510751)^170250 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (15 : ZMod 510751)^102150 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 227 := Nat.prime_eq_prime_of_dvd_pow hq prime_227 hd
          subst q
          change (15 : ZMod 510751)^2250 ≠ 1
          reduce_mod_char
          decide

theorem prime_517511 : Nat.Prime 517511 := by
  apply lucas_primality 517511 (13 : ZMod 517511)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 517511 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((7393 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 517511)^258755 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (13 : ZMod 517511)^103502 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (13 : ZMod 517511)^73930 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7393 := Nat.prime_eq_prime_of_dvd_pow hq prime_7393 hd
          subst q
          change (13 : ZMod 517511)^70 ≠ 1
          reduce_mod_char
          decide

theorem prime_517613 : Nat.Prime 517613 := by
  apply lucas_primality 517613 (2 : ZMod 517613)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 517613 - 1 = (2 : ℕ)^2 * ((129403 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 517613)^258806 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 129403 := Nat.prime_eq_prime_of_dvd_pow hq prime_129403 hd
      subst q
      change (2 : ZMod 517613)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_519737 : Nat.Prime 519737 := by
  apply lucas_primality 519737 (3 : ZMod 519737)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 519737 - 1 = (2 : ℕ)^3 * ((7 : ℕ)^1 * ((9281 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 519737)^259868 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 519737)^74248 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 9281 := Nat.prime_eq_prime_of_dvd_pow hq prime_9281 hd
        subst q
        change (3 : ZMod 519737)^56 ≠ 1
        reduce_mod_char
        decide

theorem prime_520969 : Nat.Prime 520969 := by
  apply lucas_primality 520969 (26 : ZMod 520969)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 520969 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((443 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (26 : ZMod 520969)^260484 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (26 : ZMod 520969)^173656 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (26 : ZMod 520969)^74424 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 443 := Nat.prime_eq_prime_of_dvd_pow hq prime_443 hd
          subst q
          change (26 : ZMod 520969)^1176 ≠ 1
          reduce_mod_char
          decide

theorem prime_521363 : Nat.Prime 521363 := by
  apply lucas_primality 521363 (2 : ZMod 521363)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 521363 - 1 = (2 : ℕ)^1 * ((29 : ℕ)^1 * ((89 : ℕ)^1 * ((101 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 521363)^260681 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (2 : ZMod 521363)^17978 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (2 : ZMod 521363)^5858 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
          subst q
          change (2 : ZMod 521363)^5162 ≠ 1
          reduce_mod_char
          decide

theorem prime_522233 : Nat.Prime 522233 := by
  apply lucas_primality 522233 (3 : ZMod 522233)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 522233 - 1 = (2 : ℕ)^3 * ((29 : ℕ)^1 * ((2251 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 522233)^261116 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (3 : ZMod 522233)^18008 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2251 := Nat.prime_eq_prime_of_dvd_pow hq prime_2251 hd
        subst q
        change (3 : ZMod 522233)^232 ≠ 1
        reduce_mod_char
        decide

theorem prime_523553 : Nat.Prime 523553 := by
  apply lucas_primality 523553 (3 : ZMod 523553)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 523553 - 1 = (2 : ℕ)^5 * ((16361 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 523553)^261776 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 16361 := Nat.prime_eq_prime_of_dvd_pow hq prime_16361 hd
      subst q
      change (3 : ZMod 523553)^32 ≠ 1
      reduce_mod_char
      decide

theorem prime_524063 : Nat.Prime 524063 := by
  apply lucas_primality 524063 (5 : ZMod 524063)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 524063 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((41 : ℕ)^1 * ((83 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 524063)^262031 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 524063)^74866 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 524063)^47642 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (5 : ZMod 524063)^12782 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
            subst q
            change (5 : ZMod 524063)^6314 ≠ 1
            reduce_mod_char
            decide

theorem prime_525373 : Nat.Prime 525373 := by
  apply lucas_primality 525373 (5 : ZMod 525373)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 525373 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((43781 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 525373)^262686 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 525373)^175124 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 43781 := Nat.prime_eq_prime_of_dvd_pow hq prime_43781 hd
        subst q
        change (5 : ZMod 525373)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_527803 : Nat.Prime 527803 := by
  apply lucas_primality 527803 (3 : ZMod 527803)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 527803 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^2 * ((727 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 527803)^263901 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 527803)^175934 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 527803)^47982 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 727 := Nat.prime_eq_prime_of_dvd_pow hq prime_727 hd
          subst q
          change (3 : ZMod 527803)^726 ≠ 1
          reduce_mod_char
          decide

theorem prime_528313 : Nat.Prime 528313 := by
  apply lucas_primality 528313 (13 : ZMod 528313)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 528313 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((22013 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 528313)^264156 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 528313)^176104 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 22013 := Nat.prime_eq_prime_of_dvd_pow hq prime_22013 hd
        subst q
        change (13 : ZMod 528313)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_529049 : Nat.Prime 529049 := by
  apply lucas_primality 529049 (3 : ZMod 529049)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 529049 - 1 = (2 : ℕ)^3 * ((13 : ℕ)^1 * ((5087 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 529049)^264524 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 529049)^40696 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5087 := Nat.prime_eq_prime_of_dvd_pow hq prime_5087 hd
        subst q
        change (3 : ZMod 529049)^104 ≠ 1
        reduce_mod_char
        decide

theorem prime_529471 : Nat.Prime 529471 := by
  apply lucas_primality 529471 (3 : ZMod 529471)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 529471 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((37 : ℕ)^1 * ((53 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 529471)^264735 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 529471)^176490 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 529471)^105894 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
            subst q
            change (3 : ZMod 529471)^14310 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
            subst q
            change (3 : ZMod 529471)^9990 ≠ 1
            reduce_mod_char
            decide

theorem prime_531457 : Nat.Prime 531457 := by
  apply lucas_primality 531457 (5 : ZMod 531457)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 531457 - 1 = (2 : ℕ)^10 * ((3 : ℕ)^1 * ((173 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 531457)^265728 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 531457)^177152 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
        subst q
        change (5 : ZMod 531457)^3072 ≠ 1
        reduce_mod_char
        decide

theorem prime_535937 : Nat.Prime 535937 := by
  apply lucas_primality 535937 (3 : ZMod 535937)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 535937 - 1 = (2 : ℕ)^7 * ((53 : ℕ)^1 * ((79 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 535937)^267968 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
        subst q
        change (3 : ZMod 535937)^10112 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
        subst q
        change (3 : ZMod 535937)^6784 ≠ 1
        reduce_mod_char
        decide

theorem prime_537143 : Nat.Prime 537143 := by
  apply lucas_primality 537143 (5 : ZMod 537143)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 537143 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((11677 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 537143)^268571 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (5 : ZMod 537143)^23354 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 11677 := Nat.prime_eq_prime_of_dvd_pow hq prime_11677 hd
        subst q
        change (5 : ZMod 537143)^46 ≠ 1
        reduce_mod_char
        decide

theorem prime_537269 : Nat.Prime 537269 := by
  apply lucas_primality 537269 (2 : ZMod 537269)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 537269 - 1 = (2 : ℕ)^2 * ((17 : ℕ)^1 * ((7901 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 537269)^268634 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 537269)^31604 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7901 := Nat.prime_eq_prime_of_dvd_pow hq prime_7901 hd
        subst q
        change (2 : ZMod 537269)^68 ≠ 1
        reduce_mod_char
        decide

theorem prime_539003 : Nat.Prime 539003 := by
  apply lucas_primality 539003 (2 : ZMod 539003)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 539003 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((83 : ℕ)^1 * ((191 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 539003)^269501 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 539003)^31706 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
          subst q
          change (2 : ZMod 539003)^6494 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
          subst q
          change (2 : ZMod 539003)^2822 ≠ 1
          reduce_mod_char
          decide

theorem prime_545023 : Nat.Prime 545023 := by
  apply lucas_primality 545023 (3 : ZMod 545023)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 545023 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((10093 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 545023)^272511 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 545023)^181674 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 10093 := Nat.prime_eq_prime_of_dvd_pow hq prime_10093 hd
        subst q
        change (3 : ZMod 545023)^54 ≠ 1
        reduce_mod_char
        decide

theorem prime_546677 : Nat.Prime 546677 := by
  apply lucas_primality 546677 (2 : ZMod 546677)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 546677 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((10513 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 546677)^273338 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 546677)^42052 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 10513 := Nat.prime_eq_prime_of_dvd_pow hq prime_10513 hd
        subst q
        change (2 : ZMod 546677)^52 ≠ 1
        reduce_mod_char
        decide

theorem prime_548909 : Nat.Prime 548909 := by
  apply lucas_primality 548909 (2 : ZMod 548909)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 548909 - 1 = (2 : ℕ)^2 * ((41 : ℕ)^1 * ((3347 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 548909)^274454 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
        subst q
        change (2 : ZMod 548909)^13388 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3347 := Nat.prime_eq_prime_of_dvd_pow hq prime_3347 hd
        subst q
        change (2 : ZMod 548909)^164 ≠ 1
        reduce_mod_char
        decide

theorem prime_549547 : Nat.Prime 549547 := by
  apply lucas_primality 549547 (2 : ZMod 549547)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 549547 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((91591 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 549547)^274773 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 549547)^183182 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 91591 := Nat.prime_eq_prime_of_dvd_pow hq prime_91591 hd
        subst q
        change (2 : ZMod 549547)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_556403 : Nat.Prime 556403 := by
  apply lucas_primality 556403 (2 : ZMod 556403)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 556403 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((3613 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 556403)^278201 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 556403)^79486 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 556403)^50582 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3613 := Nat.prime_eq_prime_of_dvd_pow hq prime_3613 hd
          subst q
          change (2 : ZMod 556403)^154 ≠ 1
          reduce_mod_char
          decide

theorem prime_556727 : Nat.Prime 556727 := by
  apply lucas_primality 556727 (5 : ZMod 556727)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 556727 - 1 = (2 : ℕ)^1 * ((278363 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 556727)^278363 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 278363 := Nat.prime_eq_prime_of_dvd_pow hq prime_278363 hd
      subst q
      change (5 : ZMod 556727)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_558781 : Nat.Prime 558781 := by
  apply lucas_primality 558781 (6 : ZMod 558781)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 558781 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((67 : ℕ)^1 * ((139 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 558781)^279390 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 558781)^186260 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 558781)^111756 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
            subst q
            change (6 : ZMod 558781)^8340 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
            subst q
            change (6 : ZMod 558781)^4020 ≠ 1
            reduce_mod_char
            decide

theorem prime_560237 : Nat.Prime 560237 := by
  apply lucas_primality 560237 (2 : ZMod 560237)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 560237 - 1 = (2 : ℕ)^2 * ((227 : ℕ)^1 * ((617 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 560237)^280118 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 227 := Nat.prime_eq_prime_of_dvd_pow hq prime_227 hd
        subst q
        change (2 : ZMod 560237)^2468 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 617 := Nat.prime_eq_prime_of_dvd_pow hq prime_617 hd
        subst q
        change (2 : ZMod 560237)^908 ≠ 1
        reduce_mod_char
        decide

theorem prime_564881 : Nat.Prime 564881 := by
  apply lucas_primality 564881 (3 : ZMod 564881)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 564881 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((23 : ℕ)^1 * ((307 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 564881)^282440 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 564881)^112976 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (3 : ZMod 564881)^24560 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 307 := Nat.prime_eq_prime_of_dvd_pow hq prime_307 hd
          subst q
          change (3 : ZMod 564881)^1840 ≠ 1
          reduce_mod_char
          decide

theorem prime_572321 : Nat.Prime 572321 := by
  apply lucas_primality 572321 (3 : ZMod 572321)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 572321 - 1 = (2 : ℕ)^5 * ((5 : ℕ)^1 * ((7 : ℕ)^2 * ((73 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 572321)^286160 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 572321)^114464 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 572321)^81760 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
          subst q
          change (3 : ZMod 572321)^7840 ≠ 1
          reduce_mod_char
          decide

theorem prime_572573 : Nat.Prime 572573 := by
  apply lucas_primality 572573 (2 : ZMod 572573)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 572573 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((11 : ℕ)^2 * ((13 : ℕ)^2))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 572573)^286286 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 572573)^81796 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 572573)^52052 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 572573)^44044 ≠ 1
          reduce_mod_char
          decide

theorem prime_576217 : Nat.Prime 576217 := by
  apply lucas_primality 576217 (5 : ZMod 576217)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 576217 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((53 : ℕ)^1 * ((151 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 576217)^288108 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 576217)^192072 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (5 : ZMod 576217)^10872 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
          subst q
          change (5 : ZMod 576217)^3816 ≠ 1
          reduce_mod_char
          decide

theorem prime_576341 : Nat.Prime 576341 := by
  apply lucas_primality 576341 (2 : ZMod 576341)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 576341 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((28817 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 576341)^288170 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 576341)^115268 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 28817 := Nat.prime_eq_prime_of_dvd_pow hq prime_28817 hd
        subst q
        change (2 : ZMod 576341)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_577939 : Nat.Prime 577939 := by
  apply lucas_primality 577939 (2 : ZMod 577939)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 577939 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((96323 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 577939)^288969 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 577939)^192646 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 96323 := Nat.prime_eq_prime_of_dvd_pow hq prime_96323 hd
        subst q
        change (2 : ZMod 577939)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_579883 : Nat.Prime 579883 := by
  apply lucas_primality 579883 (3 : ZMod 579883)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 579883 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((127 : ℕ)^1 * ((761 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 579883)^289941 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 579883)^193294 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
          subst q
          change (3 : ZMod 579883)^4566 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 761 := Nat.prime_eq_prime_of_dvd_pow hq prime_761 hd
          subst q
          change (3 : ZMod 579883)^762 ≠ 1
          reduce_mod_char
          decide

theorem prime_582763 : Nat.Prime 582763 := by
  apply lucas_primality 582763 (5 : ZMod 582763)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 582763 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((97127 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 582763)^291381 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 582763)^194254 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 97127 := Nat.prime_eq_prime_of_dvd_pow hq prime_97127 hd
        subst q
        change (5 : ZMod 582763)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_583697 : Nat.Prime 583697 := by
  apply lucas_primality 583697 (3 : ZMod 583697)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 583697 - 1 = (2 : ℕ)^4 * ((191 : ℕ)^2) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 583697)^291848 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
      subst q
      change (3 : ZMod 583697)^3056 ≠ 1
      reduce_mod_char
      decide

theorem prime_585049 : Nat.Prime 585049 := by
  apply lucas_primality 585049 (7 : ZMod 585049)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 585049 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((1283 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 585049)^292524 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 585049)^195016 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (7 : ZMod 585049)^30792 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1283 := Nat.prime_eq_prime_of_dvd_pow hq prime_1283 hd
          subst q
          change (7 : ZMod 585049)^456 ≠ 1
          reduce_mod_char
          decide

theorem prime_585691 : Nat.Prime 585691 := by
  apply lucas_primality 585691 (3 : ZMod 585691)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 585691 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((2789 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 585691)^292845 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 585691)^195230 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 585691)^117138 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (3 : ZMod 585691)^83670 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2789 := Nat.prime_eq_prime_of_dvd_pow hq prime_2789 hd
            subst q
            change (3 : ZMod 585691)^210 ≠ 1
            reduce_mod_char
            decide

theorem prime_589529 : Nat.Prime 589529 := by
  apply lucas_primality 589529 (3 : ZMod 589529)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 589529 - 1 = (2 : ℕ)^3 * ((59 : ℕ)^1 * ((1249 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 589529)^294764 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
        subst q
        change (3 : ZMod 589529)^9992 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1249 := Nat.prime_eq_prime_of_dvd_pow hq prime_1249 hd
        subst q
        change (3 : ZMod 589529)^472 ≠ 1
        reduce_mod_char
        decide

theorem prime_590641 : Nat.Prime 590641 := by
  apply lucas_primality 590641 (11 : ZMod 590641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 590641 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((23 : ℕ)^1 * ((107 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 590641)^295320 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 590641)^196880 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 590641)^118128 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (11 : ZMod 590641)^25680 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
            subst q
            change (11 : ZMod 590641)^5520 ≠ 1
            reduce_mod_char
            decide

theorem prime_592073 : Nat.Prime 592073 := by
  apply lucas_primality 592073 (3 : ZMod 592073)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 592073 - 1 = (2 : ℕ)^3 * ((13 : ℕ)^1 * ((5693 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 592073)^296036 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 592073)^45544 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5693 := Nat.prime_eq_prime_of_dvd_pow hq prime_5693 hd
        subst q
        change (3 : ZMod 592073)^104 ≠ 1
        reduce_mod_char
        decide

theorem prime_592469 : Nat.Prime 592469 := by
  apply lucas_primality 592469 (2 : ZMod 592469)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 592469 - 1 = (2 : ℕ)^2 * ((73 : ℕ)^1 * ((2029 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 592469)^296234 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
        subst q
        change (2 : ZMod 592469)^8116 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2029 := Nat.prime_eq_prime_of_dvd_pow hq prime_2029 hd
        subst q
        change (2 : ZMod 592469)^292 ≠ 1
        reduce_mod_char
        decide

theorem prime_597407 : Nat.Prime 597407 := by
  apply lucas_primality 597407 (5 : ZMod 597407)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 597407 - 1 = (2 : ℕ)^1 * ((281 : ℕ)^1 * ((1063 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 597407)^298703 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 281 := Nat.prime_eq_prime_of_dvd_pow hq prime_281 hd
        subst q
        change (5 : ZMod 597407)^2126 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1063 := Nat.prime_eq_prime_of_dvd_pow hq prime_1063 hd
        subst q
        change (5 : ZMod 597407)^562 ≠ 1
        reduce_mod_char
        decide

theorem prime_599699 : Nat.Prime 599699 := by
  apply lucas_primality 599699 (2 : ZMod 599699)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 599699 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((27259 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 599699)^299849 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 599699)^54518 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 27259 := Nat.prime_eq_prime_of_dvd_pow hq prime_27259 hd
        subst q
        change (2 : ZMod 599699)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_607249 : Nat.Prime 607249 := by
  apply lucas_primality 607249 (7 : ZMod 607249)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 607249 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((4217 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 607249)^303624 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 607249)^202416 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4217 := Nat.prime_eq_prime_of_dvd_pow hq prime_4217 hd
        subst q
        change (7 : ZMod 607249)^144 ≠ 1
        reduce_mod_char
        decide

theorem prime_608177 : Nat.Prime 608177 := by
  apply lucas_primality 608177 (3 : ZMod 608177)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 608177 - 1 = (2 : ℕ)^4 * ((38011 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 608177)^304088 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 38011 := Nat.prime_eq_prime_of_dvd_pow hq prime_38011 hd
      subst q
      change (3 : ZMod 608177)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_608851 : Nat.Prime 608851 := by
  apply lucas_primality 608851 (11 : ZMod 608851)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 608851 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((5 : ℕ)^2 * ((11 : ℕ)^1 * ((41 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 608851)^304425 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 608851)^202950 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 608851)^121770 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (11 : ZMod 608851)^55350 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (11 : ZMod 608851)^14850 ≠ 1
            reduce_mod_char
            decide

theorem prime_613177 : Nat.Prime 613177 := by
  apply lucas_primality 613177 (13 : ZMod 613177)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 613177 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((29 : ℕ)^1 * ((881 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 613177)^306588 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 613177)^204392 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (13 : ZMod 613177)^21144 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 881 := Nat.prime_eq_prime_of_dvd_pow hq prime_881 hd
          subst q
          change (13 : ZMod 613177)^696 ≠ 1
          reduce_mod_char
          decide

theorem prime_620029 : Nat.Prime 620029 := by
  apply lucas_primality 620029 (2 : ZMod 620029)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 620029 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((5741 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 620029)^310014 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 620029)^206676 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5741 := Nat.prime_eq_prime_of_dvd_pow hq prime_5741 hd
        subst q
        change (2 : ZMod 620029)^108 ≠ 1
        reduce_mod_char
        decide

theorem prime_623723 : Nat.Prime 623723 := by
  apply lucas_primality 623723 (2 : ZMod 623723)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 623723 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((28351 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 623723)^311861 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 623723)^56702 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 28351 := Nat.prime_eq_prime_of_dvd_pow hq prime_28351 hd
        subst q
        change (2 : ZMod 623723)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_628673 : Nat.Prime 628673 := by
  apply lucas_primality 628673 (3 : ZMod 628673)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 628673 - 1 = (2 : ℕ)^6 * ((11 : ℕ)^1 * ((19 : ℕ)^1 * ((47 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 628673)^314336 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 628673)^57152 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (3 : ZMod 628673)^33088 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (3 : ZMod 628673)^13376 ≠ 1
          reduce_mod_char
          decide

theorem prime_629617 : Nat.Prime 629617 := by
  apply lucas_primality 629617 (10 : ZMod 629617)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 629617 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((1009 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 629617)^314808 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 629617)^209872 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (10 : ZMod 629617)^48432 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1009 := Nat.prime_eq_prime_of_dvd_pow hq prime_1009 hd
          subst q
          change (10 : ZMod 629617)^624 ≠ 1
          reduce_mod_char
          decide

theorem prime_632521 : Nat.Prime 632521 := by
  apply lucas_primality 632521 (11 : ZMod 632521)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 632521 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((251 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 632521)^316260 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 632521)^210840 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 632521)^126504 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (11 : ZMod 632521)^90360 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 251 := Nat.prime_eq_prime_of_dvd_pow hq prime_251 hd
            subst q
            change (11 : ZMod 632521)^2520 ≠ 1
            reduce_mod_char
            decide

theorem prime_636781 : Nat.Prime 636781 := by
  apply lucas_primality 636781 (6 : ZMod 636781)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 636781 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((10613 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 636781)^318390 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 636781)^212260 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 636781)^127356 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 10613 := Nat.prime_eq_prime_of_dvd_pow hq prime_10613 hd
          subst q
          change (6 : ZMod 636781)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_638179 : Nat.Prime 638179 := by
  apply lucas_primality 638179 (3 : ZMod 638179)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 638179 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((106363 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 638179)^319089 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 638179)^212726 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 106363 := Nat.prime_eq_prime_of_dvd_pow hq prime_106363 hd
        subst q
        change (3 : ZMod 638179)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_639563 : Nat.Prime 639563 := by
  apply lucas_primality 639563 (2 : ZMod 639563)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 639563 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((4153 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 639563)^319781 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 639563)^91366 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 639563)^58142 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4153 := Nat.prime_eq_prime_of_dvd_pow hq prime_4153 hd
          subst q
          change (2 : ZMod 639563)^154 ≠ 1
          reduce_mod_char
          decide

theorem prime_641891 : Nat.Prime 641891 := by
  apply lucas_primality 641891 (2 : ZMod 641891)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 641891 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((64189 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 641891)^320945 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 641891)^128378 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 64189 := Nat.prime_eq_prime_of_dvd_pow hq prime_64189 hd
        subst q
        change (2 : ZMod 641891)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_642253 : Nat.Prime 642253 := by
  apply lucas_primality 642253 (2 : ZMod 642253)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 642253 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((23 : ℕ)^1 * ((179 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 642253)^321126 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 642253)^214084 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 642253)^49404 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (2 : ZMod 642253)^27924 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 179 := Nat.prime_eq_prime_of_dvd_pow hq prime_179 hd
            subst q
            change (2 : ZMod 642253)^3588 ≠ 1
            reduce_mod_char
            decide

theorem prime_646957 : Nat.Prime 646957 := by
  apply lucas_primality 646957 (5 : ZMod 646957)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 646957 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((17971 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 646957)^323478 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 646957)^215652 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 17971 := Nat.prime_eq_prime_of_dvd_pow hq prime_17971 hd
        subst q
        change (5 : ZMod 646957)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_647641 : Nat.Prime 647641 := by
  apply lucas_primality 647641 (26 : ZMod 647641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 647641 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((257 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (26 : ZMod 647641)^323820 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (26 : ZMod 647641)^215880 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (26 : ZMod 647641)^129528 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (26 : ZMod 647641)^92520 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 257 := Nat.prime_eq_prime_of_dvd_pow hq prime_257 hd
            subst q
            change (26 : ZMod 647641)^2520 ≠ 1
            reduce_mod_char
            decide

theorem prime_651689 : Nat.Prime 651689 := by
  apply lucas_primality 651689 (6 : ZMod 651689)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 651689 - 1 = (2 : ℕ)^3 * ((29 : ℕ)^1 * ((53 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 651689)^325844 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (6 : ZMod 651689)^22472 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
        subst q
        change (6 : ZMod 651689)^12296 ≠ 1
        reduce_mod_char
        decide

theorem prime_651697 : Nat.Prime 651697 := by
  apply lucas_primality 651697 (5 : ZMod 651697)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 651697 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((13577 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 651697)^325848 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 651697)^217232 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13577 := Nat.prime_eq_prime_of_dvd_pow hq prime_13577 hd
        subst q
        change (5 : ZMod 651697)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_653647 : Nat.Prime 653647 := by
  apply lucas_primality 653647 (3 : ZMod 653647)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 653647 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((79 : ℕ)^1 * ((197 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 653647)^326823 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 653647)^217882 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 653647)^93378 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
            subst q
            change (3 : ZMod 653647)^8274 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
            subst q
            change (3 : ZMod 653647)^3318 ≠ 1
            reduce_mod_char
            decide

theorem prime_653899 : Nat.Prime 653899 := by
  apply lucas_primality 653899 (3 : ZMod 653899)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 653899 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((15569 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 653899)^326949 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 653899)^217966 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 653899)^93414 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 15569 := Nat.prime_eq_prime_of_dvd_pow hq prime_15569 hd
          subst q
          change (3 : ZMod 653899)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_654229 : Nat.Prime 654229 := by
  apply lucas_primality 654229 (10 : ZMod 654229)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 654229 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((17 : ℕ)^1 * ((1069 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 654229)^327114 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 654229)^218076 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (10 : ZMod 654229)^38484 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1069 := Nat.prime_eq_prime_of_dvd_pow hq prime_1069 hd
          subst q
          change (10 : ZMod 654229)^612 ≠ 1
          reduce_mod_char
          decide

theorem prime_654421 : Nat.Prime 654421 := by
  apply lucas_primality 654421 (6 : ZMod 654421)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 654421 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((839 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 654421)^327210 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 654421)^218140 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 654421)^130884 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (6 : ZMod 654421)^50340 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 839 := Nat.prime_eq_prime_of_dvd_pow hq prime_839 hd
            subst q
            change (6 : ZMod 654421)^780 ≠ 1
            reduce_mod_char
            decide

theorem prime_655687 : Nat.Prime 655687 := by
  apply lucas_primality 655687 (3 : ZMod 655687)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 655687 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((73 : ℕ)^1 * ((499 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 655687)^327843 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 655687)^218562 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
          subst q
          change (3 : ZMod 655687)^8982 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 499 := Nat.prime_eq_prime_of_dvd_pow hq prime_499 hd
          subst q
          change (3 : ZMod 655687)^1314 ≠ 1
          reduce_mod_char
          decide

theorem prime_660791 : Nat.Prime 660791 := by
  apply lucas_primality 660791 (19 : ZMod 660791)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 660791 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^2 * ((17 : ℕ)^1 * ((23 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 660791)^330395 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (19 : ZMod 660791)^132158 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (19 : ZMod 660791)^50830 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (19 : ZMod 660791)^38870 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (19 : ZMod 660791)^28730 ≠ 1
            reduce_mod_char
            decide

theorem prime_665993 : Nat.Prime 665993 := by
  apply lucas_primality 665993 (3 : ZMod 665993)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 665993 - 1 = (2 : ℕ)^3 * ((17 : ℕ)^1 * ((59 : ℕ)^1 * ((83 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 665993)^332996 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (3 : ZMod 665993)^39176 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (3 : ZMod 665993)^11288 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
          subst q
          change (3 : ZMod 665993)^8024 ≠ 1
          reduce_mod_char
          decide

theorem prime_667129 : Nat.Prime 667129 := by
  apply lucas_primality 667129 (23 : ZMod 667129)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 667129 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((19 : ℕ)^2)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (23 : ZMod 667129)^333564 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (23 : ZMod 667129)^222376 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (23 : ZMod 667129)^95304 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (23 : ZMod 667129)^60648 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (23 : ZMod 667129)^35112 ≠ 1
            reduce_mod_char
            decide

theorem prime_671269 : Nat.Prime 671269 := by
  apply lucas_primality 671269 (6 : ZMod 671269)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 671269 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((13 : ℕ)^2 * ((331 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 671269)^335634 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 671269)^223756 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (6 : ZMod 671269)^51636 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 331 := Nat.prime_eq_prime_of_dvd_pow hq prime_331 hd
          subst q
          change (6 : ZMod 671269)^2028 ≠ 1
          reduce_mod_char
          decide

theorem prime_673961 : Nat.Prime 673961 := by
  apply lucas_primality 673961 (3 : ZMod 673961)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 673961 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((29 : ℕ)^1 * ((83 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 673961)^336980 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 673961)^134792 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 673961)^96280 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (3 : ZMod 673961)^23240 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
            subst q
            change (3 : ZMod 673961)^8120 ≠ 1
            reduce_mod_char
            decide

theorem prime_676043 : Nat.Prime 676043 := by
  apply lucas_primality 676043 (2 : ZMod 676043)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 676043 - 1 = (2 : ℕ)^1 * ((157 : ℕ)^1 * ((2153 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 676043)^338021 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
        subst q
        change (2 : ZMod 676043)^4306 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2153 := Nat.prime_eq_prime_of_dvd_pow hq prime_2153 hd
        subst q
        change (2 : ZMod 676043)^314 ≠ 1
        reduce_mod_char
        decide

theorem prime_689261 : Nat.Prime 689261 := by
  apply lucas_primality 689261 (12 : ZMod 689261)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 689261 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((241 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (12 : ZMod 689261)^344630 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (12 : ZMod 689261)^137852 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (12 : ZMod 689261)^62660 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (12 : ZMod 689261)^53020 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 241 := Nat.prime_eq_prime_of_dvd_pow hq prime_241 hd
            subst q
            change (12 : ZMod 689261)^2860 ≠ 1
            reduce_mod_char
            decide

end LegendreK6.Pratt
