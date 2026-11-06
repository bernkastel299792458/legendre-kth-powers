import LegendreK6.Pratt.Block013

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LegendreK6.Pratt

theorem prime_19839713 : Nat.Prime 19839713 := by
  apply lucas_primality 19839713 (3 : ZMod 19839713)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19839713 - 1 = (2 : ℕ)^5 * ((29 : ℕ)^1 * ((21379 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 19839713)^9919856 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (3 : ZMod 19839713)^684128 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 21379 := Nat.prime_eq_prime_of_dvd_pow hq prime_21379 hd
        subst q
        change (3 : ZMod 19839713)^928 ≠ 1
        reduce_mod_char
        decide

theorem prime_19972111 : Nat.Prime 19972111 := by
  apply lucas_primality 19972111 (3 : ZMod 19972111)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19972111 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((39161 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 19972111)^9986055 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 19972111)^6657370 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 19972111)^3994422 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (3 : ZMod 19972111)^1174830 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 39161 := Nat.prime_eq_prime_of_dvd_pow hq prime_39161 hd
            subst q
            change (3 : ZMod 19972111)^510 ≠ 1
            reduce_mod_char
            decide

theorem prime_20035627 : Nat.Prime 20035627 := by
  apply lucas_primality 20035627 (3 : ZMod 20035627)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20035627 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^2 * ((19759 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 20035627)^10017813 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 20035627)^6678542 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 20035627)^1541202 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 19759 := Nat.prime_eq_prime_of_dvd_pow hq prime_19759 hd
          subst q
          change (3 : ZMod 20035627)^1014 ≠ 1
          reduce_mod_char
          decide

theorem prime_20186351 : Nat.Prime 20186351 := by
  apply lucas_primality 20186351 (11 : ZMod 20186351)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20186351 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((41 : ℕ)^1 * ((43 : ℕ)^1 * ((229 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 20186351)^10093175 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 20186351)^4037270 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (11 : ZMod 20186351)^492350 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (11 : ZMod 20186351)^469450 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 229 := Nat.prime_eq_prime_of_dvd_pow hq prime_229 hd
            subst q
            change (11 : ZMod 20186351)^88150 ≠ 1
            reduce_mod_char
            decide

theorem prime_20204299 : Nat.Prime 20204299 := by
  apply lucas_primality 20204299 (10 : ZMod 20204299)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20204299 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((61 : ℕ)^1 * ((18401 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 20204299)^10102149 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 20204299)^6734766 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (10 : ZMod 20204299)^331218 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 18401 := Nat.prime_eq_prime_of_dvd_pow hq prime_18401 hd
          subst q
          change (10 : ZMod 20204299)^1098 ≠ 1
          reduce_mod_char
          decide

theorem prime_20213233 : Nat.Prime 20213233 := by
  apply lucas_primality 20213233 (10 : ZMod 20213233)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20213233 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((29 : ℕ)^1 * ((1117 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 20213233)^10106616 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 20213233)^6737744 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (10 : ZMod 20213233)^1554864 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (10 : ZMod 20213233)^697008 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1117 := Nat.prime_eq_prime_of_dvd_pow hq prime_1117 hd
            subst q
            change (10 : ZMod 20213233)^18096 ≠ 1
            reduce_mod_char
            decide

theorem prime_20419033 : Nat.Prime 20419033 := by
  apply lucas_primality 20419033 (5 : ZMod 20419033)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20419033 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((71 : ℕ)^1 * ((521 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 20419033)^10209516 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 20419033)^6806344 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (5 : ZMod 20419033)^887784 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
            subst q
            change (5 : ZMod 20419033)^287592 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 521 := Nat.prime_eq_prime_of_dvd_pow hq prime_521 hd
            subst q
            change (5 : ZMod 20419033)^39192 ≠ 1
            reduce_mod_char
            decide

theorem prime_20573341 : Nat.Prime 20573341 := by
  apply lucas_primality 20573341 (11 : ZMod 20573341)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20573341 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((342889 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 20573341)^10286670 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 20573341)^6857780 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 20573341)^4114668 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 342889 := Nat.prime_eq_prime_of_dvd_pow hq prime_342889 hd
          subst q
          change (11 : ZMod 20573341)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_20710867 : Nat.Prime 20710867 := by
  apply lucas_primality 20710867 (3 : ZMod 20710867)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20710867 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((113 : ℕ)^1 * ((2777 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 20710867)^10355433 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 20710867)^6903622 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 20710867)^1882806 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
            subst q
            change (3 : ZMod 20710867)^183282 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2777 := Nat.prime_eq_prime_of_dvd_pow hq prime_2777 hd
            subst q
            change (3 : ZMod 20710867)^7458 ≠ 1
            reduce_mod_char
            decide

theorem prime_21072923 : Nat.Prime 21072923 := by
  apply lucas_primality 21072923 (2 : ZMod 21072923)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21072923 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((23 : ℕ)^1 * ((131 : ℕ)^1 * ((269 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 21072923)^10536461 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 21072923)^1620994 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 21072923)^916214 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
            subst q
            change (2 : ZMod 21072923)^160862 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
            subst q
            change (2 : ZMod 21072923)^78338 ≠ 1
            reduce_mod_char
            decide

theorem prime_21348323 : Nat.Prime 21348323 := by
  apply lucas_primality 21348323 (2 : ZMod 21348323)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21348323 - 1 = (2 : ℕ)^1 * ((199 : ℕ)^1 * ((53639 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 21348323)^10674161 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 199 := Nat.prime_eq_prime_of_dvd_pow hq prime_199 hd
        subst q
        change (2 : ZMod 21348323)^107278 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 53639 := Nat.prime_eq_prime_of_dvd_pow hq prime_53639 hd
        subst q
        change (2 : ZMod 21348323)^398 ≠ 1
        reduce_mod_char
        decide

theorem prime_21380813 : Nat.Prime 21380813 := by
  apply lucas_primality 21380813 (2 : ZMod 21380813)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21380813 - 1 = (2 : ℕ)^2 * ((5345203 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 21380813)^10690406 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 5345203 := Nat.prime_eq_prime_of_dvd_pow hq prime_5345203 hd
      subst q
      change (2 : ZMod 21380813)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_21418087 : Nat.Prime 21418087 := by
  apply lucas_primality 21418087 (5 : ZMod 21418087)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21418087 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((31 : ℕ)^1 * ((115151 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 21418087)^10709043 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 21418087)^7139362 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (5 : ZMod 21418087)^690906 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 115151 := Nat.prime_eq_prime_of_dvd_pow hq prime_115151 hd
          subst q
          change (5 : ZMod 21418087)^186 ≠ 1
          reduce_mod_char
          decide

theorem prime_21523361 : Nat.Prime 21523361 := by
  apply lucas_primality 21523361 (6 : ZMod 21523361)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21523361 - 1 = (2 : ℕ)^5 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((41 : ℕ)^1 * ((193 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 21523361)^10761680 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 21523361)^4304672 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (6 : ZMod 21523361)^1266080 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (6 : ZMod 21523361)^524960 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
            subst q
            change (6 : ZMod 21523361)^111520 ≠ 1
            reduce_mod_char
            decide

theorem prime_21690059 : Nat.Prime 21690059 := by
  apply lucas_primality 21690059 (2 : ZMod 21690059)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21690059 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((19 : ℕ)^1 * ((23 : ℕ)^2 * ((83 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 21690059)^10845029 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 21690059)^1668466 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 21690059)^1141582 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (2 : ZMod 21690059)^943046 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
            subst q
            change (2 : ZMod 21690059)^261326 ≠ 1
            reduce_mod_char
            decide

theorem prime_21859451 : Nat.Prime 21859451 := by
  apply lucas_primality 21859451 (6 : ZMod 21859451)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21859451 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((17 : ℕ)^1 * ((25717 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 21859451)^10929725 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 21859451)^4371890 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (6 : ZMod 21859451)^1285850 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 25717 := Nat.prime_eq_prime_of_dvd_pow hq prime_25717 hd
          subst q
          change (6 : ZMod 21859451)^850 ≠ 1
          reduce_mod_char
          decide

theorem prime_21889297 : Nat.Prime 21889297 := by
  apply lucas_primality 21889297 (5 : ZMod 21889297)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21889297 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((1063 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 21889297)^10944648 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 21889297)^7296432 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 21889297)^1989936 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (5 : ZMod 21889297)^1683792 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1063 := Nat.prime_eq_prime_of_dvd_pow hq prime_1063 hd
            subst q
            change (5 : ZMod 21889297)^20592 ≠ 1
            reduce_mod_char
            decide

theorem prime_22132783 : Nat.Prime 22132783 := by
  apply lucas_primality 22132783 (6 : ZMod 22132783)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22132783 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((269 : ℕ)^1 * ((653 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 22132783)^11066391 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 22132783)^7377594 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 22132783)^3161826 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
            subst q
            change (6 : ZMod 22132783)^82278 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 653 := Nat.prime_eq_prime_of_dvd_pow hq prime_653 hd
            subst q
            change (6 : ZMod 22132783)^33894 ≠ 1
            reduce_mod_char
            decide

theorem prime_22560001 : Nat.Prime 22560001 := by
  apply lucas_primality 22560001 (11 : ZMod 22560001)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22560001 - 1 = (2 : ℕ)^8 * ((3 : ℕ)^1 * ((5 : ℕ)^4 * ((47 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 22560001)^11280000 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 22560001)^7520000 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 22560001)^4512000 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (11 : ZMod 22560001)^480000 ≠ 1
          reduce_mod_char
          decide

theorem prime_23046931 : Nat.Prime 23046931 := by
  apply lucas_primality 23046931 (2 : ZMod 23046931)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23046931 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((5 : ℕ)^1 * ((37 : ℕ)^1 * ((769 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 23046931)^11523465 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 23046931)^7682310 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 23046931)^4609386 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
            subst q
            change (2 : ZMod 23046931)^622890 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 769 := Nat.prime_eq_prime_of_dvd_pow hq prime_769 hd
            subst q
            change (2 : ZMod 23046931)^29970 ≠ 1
            reduce_mod_char
            decide

theorem prime_23352181 : Nat.Prime 23352181 := by
  apply lucas_primality 23352181 (2 : ZMod 23352181)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23352181 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((37 : ℕ)^1 * ((67 : ℕ)^1 * ((157 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 23352181)^11676090 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 23352181)^7784060 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 23352181)^4670436 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
            subst q
            change (2 : ZMod 23352181)^631140 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
              subst q
              change (2 : ZMod 23352181)^348540 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
              subst q
              change (2 : ZMod 23352181)^148740 ≠ 1
              reduce_mod_char
              decide

theorem prime_23427641 : Nat.Prime 23427641 := by
  apply lucas_primality 23427641 (3 : ZMod 23427641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23427641 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((585691 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 23427641)^11713820 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 23427641)^4685528 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 585691 := Nat.prime_eq_prime_of_dvd_pow hq prime_585691 hd
        subst q
        change (3 : ZMod 23427641)^40 ≠ 1
        reduce_mod_char
        decide

theorem prime_23466059 : Nat.Prime 23466059 := by
  apply lucas_primality 23466059 (2 : ZMod 23466059)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23466059 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((152377 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 23466059)^11733029 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 23466059)^3352294 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 23466059)^2133278 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 152377 := Nat.prime_eq_prime_of_dvd_pow hq prime_152377 hd
          subst q
          change (2 : ZMod 23466059)^154 ≠ 1
          reduce_mod_char
          decide

theorem prime_23960107 : Nat.Prime 23960107 := by
  apply lucas_primality 23960107 (2 : ZMod 23960107)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23960107 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((17 : ℕ)^1 * ((78301 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 23960107)^11980053 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 23960107)^7986702 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 23960107)^1409418 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 78301 := Nat.prime_eq_prime_of_dvd_pow hq prime_78301 hd
          subst q
          change (2 : ZMod 23960107)^306 ≠ 1
          reduce_mod_char
          decide

theorem prime_24137573 : Nat.Prime 24137573 := by
  apply lucas_primality 24137573 (2 : ZMod 24137573)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24137573 - 1 = (2 : ℕ)^2 * ((6034393 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 24137573)^12068786 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 6034393 := Nat.prime_eq_prime_of_dvd_pow hq prime_6034393 hd
      subst q
      change (2 : ZMod 24137573)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_24415717 : Nat.Prime 24415717 := by
  apply lucas_primality 24415717 (2 : ZMod 24415717)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24415717 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((156511 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 24415717)^12207858 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 24415717)^8138572 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 24415717)^1878132 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 156511 := Nat.prime_eq_prime_of_dvd_pow hq prime_156511 hd
          subst q
          change (2 : ZMod 24415717)^156 ≠ 1
          reduce_mod_char
          decide

theorem prime_24435811 : Nat.Prime 24435811 := by
  apply lucas_primality 24435811 (2 : ZMod 24435811)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24435811 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((7 : ℕ)^2 * ((1847 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 24435811)^12217905 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 24435811)^8145270 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 24435811)^4887162 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (2 : ZMod 24435811)^3490830 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1847 := Nat.prime_eq_prime_of_dvd_pow hq prime_1847 hd
            subst q
            change (2 : ZMod 24435811)^13230 ≠ 1
            reduce_mod_char
            decide

theorem prime_24443437 : Nat.Prime 24443437 := by
  apply lucas_primality 24443437 (2 : ZMod 24443437)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24443437 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((43 : ℕ)^1 * ((127 : ℕ)^1 * ((373 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 24443437)^12221718 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 24443437)^8147812 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (2 : ZMod 24443437)^568452 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
            subst q
            change (2 : ZMod 24443437)^192468 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 373 := Nat.prime_eq_prime_of_dvd_pow hq prime_373 hd
            subst q
            change (2 : ZMod 24443437)^65532 ≠ 1
            reduce_mod_char
            decide

theorem prime_24685361 : Nat.Prime 24685361 := by
  apply lucas_primality 24685361 (3 : ZMod 24685361)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24685361 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((17 : ℕ)^1 * ((2593 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 24685361)^12342680 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 24685361)^4937072 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 24685361)^3526480 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (3 : ZMod 24685361)^1452080 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2593 := Nat.prime_eq_prime_of_dvd_pow hq prime_2593 hd
            subst q
            change (3 : ZMod 24685361)^9520 ≠ 1
            reduce_mod_char
            decide

theorem prime_24705119 : Nat.Prime 24705119 := by
  apply lucas_primality 24705119 (17 : ZMod 24705119)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24705119 - 1 = (2 : ℕ)^1 * ((12352559 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 24705119)^12352559 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 12352559 := Nat.prime_eq_prime_of_dvd_pow hq prime_12352559 hd
      subst q
      change (17 : ZMod 24705119)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_24802769 : Nat.Prime 24802769 := by
  apply lucas_primality 24802769 (3 : ZMod 24802769)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24802769 - 1 = (2 : ℕ)^4 * ((1550173 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 24802769)^12401384 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1550173 := Nat.prime_eq_prime_of_dvd_pow hq prime_1550173 hd
      subst q
      change (3 : ZMod 24802769)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_25004599 : Nat.Prime 25004599 := by
  apply lucas_primality 25004599 (7 : ZMod 25004599)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 25004599 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((4167433 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 25004599)^12502299 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 25004599)^8334866 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4167433 := Nat.prime_eq_prime_of_dvd_pow hq prime_4167433 hd
        subst q
        change (7 : ZMod 25004599)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_25274453 : Nat.Prime 25274453 := by
  apply lucas_primality 25274453 (2 : ZMod 25274453)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 25274453 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((902659 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 25274453)^12637226 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 25274453)^3610636 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 902659 := Nat.prime_eq_prime_of_dvd_pow hq prime_902659 hd
        subst q
        change (2 : ZMod 25274453)^28 ≠ 1
        reduce_mod_char
        decide

theorem prime_25278719 : Nat.Prime 25278719 := by
  apply lucas_primality 25278719 (7 : ZMod 25278719)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 25278719 - 1 = (2 : ℕ)^1 * ((12639359 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 25278719)^12639359 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 12639359 := Nat.prime_eq_prime_of_dvd_pow hq prime_12639359 hd
      subst q
      change (7 : ZMod 25278719)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_25297021 : Nat.Prime 25297021 := by
  apply lucas_primality 25297021 (2 : ZMod 25297021)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 25297021 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((17 : ℕ)^1 * ((1181 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 25297021)^12648510 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 25297021)^8432340 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 25297021)^5059404 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (2 : ZMod 25297021)^3613860 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
              subst q
              change (2 : ZMod 25297021)^1488060 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1181 := Nat.prime_eq_prime_of_dvd_pow hq prime_1181 hd
              subst q
              change (2 : ZMod 25297021)^21420 ≠ 1
              reduce_mod_char
              decide

theorem prime_25376371 : Nat.Prime 25376371 := by
  apply lucas_primality 25376371 (13 : ZMod 25376371)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 25376371 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((845879 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 25376371)^12688185 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 25376371)^8458790 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 25376371)^5075274 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 845879 := Nat.prime_eq_prime_of_dvd_pow hq prime_845879 hd
          subst q
          change (13 : ZMod 25376371)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_25380479 : Nat.Prime 25380479 := by
  apply lucas_primality 25380479 (11 : ZMod 25380479)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 25380479 - 1 = (2 : ℕ)^1 * ((113 : ℕ)^1 * ((112303 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 25380479)^12690239 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
        subst q
        change (11 : ZMod 25380479)^224606 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 112303 := Nat.prime_eq_prime_of_dvd_pow hq prime_112303 hd
        subst q
        change (11 : ZMod 25380479)^226 ≠ 1
        reduce_mod_char
        decide

theorem prime_25438393 : Nat.Prime 25438393 := by
  apply lucas_primality 25438393 (5 : ZMod 25438393)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 25438393 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((17 : ℕ)^1 * ((2969 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 25438393)^12719196 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 25438393)^8479464 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 25438393)^3634056 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (5 : ZMod 25438393)^1496376 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2969 := Nat.prime_eq_prime_of_dvd_pow hq prime_2969 hd
            subst q
            change (5 : ZMod 25438393)^8568 ≠ 1
            reduce_mod_char
            decide

theorem prime_25674013 : Nat.Prime 25674013 := by
  apply lucas_primality 25674013 (15 : ZMod 25674013)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 25674013 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((17 : ℕ)^1 * ((461 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (15 : ZMod 25674013)^12837006 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (15 : ZMod 25674013)^8558004 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (15 : ZMod 25674013)^3667716 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (15 : ZMod 25674013)^1974924 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
              subst q
              change (15 : ZMod 25674013)^1510236 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 461 := Nat.prime_eq_prime_of_dvd_pow hq prime_461 hd
              subst q
              change (15 : ZMod 25674013)^55692 ≠ 1
              reduce_mod_char
              decide

theorem prime_26005097 : Nat.Prime 26005097 := by
  apply lucas_primality 26005097 (5 : ZMod 26005097)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26005097 - 1 = (2 : ℕ)^3 * ((13 : ℕ)^1 * ((250049 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 26005097)^13002548 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (5 : ZMod 26005097)^2000392 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 250049 := Nat.prime_eq_prime_of_dvd_pow hq prime_250049 hd
        subst q
        change (5 : ZMod 26005097)^104 ≠ 1
        reduce_mod_char
        decide

theorem prime_26062891 : Nat.Prime 26062891 := by
  apply lucas_primality 26062891 (3 : ZMod 26062891)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26062891 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((79 : ℕ)^1 * ((1571 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 26062891)^13031445 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 26062891)^8687630 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 26062891)^5212578 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (3 : ZMod 26062891)^3723270 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
              subst q
              change (3 : ZMod 26062891)^329910 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1571 := Nat.prime_eq_prime_of_dvd_pow hq prime_1571 hd
              subst q
              change (3 : ZMod 26062891)^16590 ≠ 1
              reduce_mod_char
              decide

theorem prime_26101037 : Nat.Prime 26101037 := by
  apply lucas_primality 26101037 (2 : ZMod 26101037)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26101037 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^2 * ((38611 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 26101037)^13050518 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 26101037)^2007772 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 38611 := Nat.prime_eq_prime_of_dvd_pow hq prime_38611 hd
        subst q
        change (2 : ZMod 26101037)^676 ≠ 1
        reduce_mod_char
        decide

theorem prime_26151497 : Nat.Prime 26151497 := by
  apply lucas_primality 26151497 (3 : ZMod 26151497)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26151497 - 1 = (2 : ℕ)^3 * ((7 : ℕ)^2 * ((66713 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 26151497)^13075748 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 26151497)^3735928 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 66713 := Nat.prime_eq_prime_of_dvd_pow hq prime_66713 hd
        subst q
        change (3 : ZMod 26151497)^392 ≠ 1
        reduce_mod_char
        decide

theorem prime_26226913 : Nat.Prime 26226913 := by
  apply lucas_primality 26226913 (7 : ZMod 26226913)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26226913 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((229 : ℕ)^1 * ((1193 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 26226913)^13113456 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 26226913)^8742304 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 229 := Nat.prime_eq_prime_of_dvd_pow hq prime_229 hd
          subst q
          change (7 : ZMod 26226913)^114528 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1193 := Nat.prime_eq_prime_of_dvd_pow hq prime_1193 hd
          subst q
          change (7 : ZMod 26226913)^21984 ≠ 1
          reduce_mod_char
          decide

theorem prime_26267531 : Nat.Prime 26267531 := by
  apply lucas_primality 26267531 (2 : ZMod 26267531)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26267531 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((2626753 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 26267531)^13133765 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 26267531)^5253506 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2626753 := Nat.prime_eq_prime_of_dvd_pow hq prime_2626753 hd
        subst q
        change (2 : ZMod 26267531)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_26297053 : Nat.Prime 26297053 := by
  apply lucas_primality 26297053 (6 : ZMod 26297053)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26297053 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((31 : ℕ)^1 * ((223 : ℕ)^1 * ((317 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 26297053)^13148526 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 26297053)^8765684 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (6 : ZMod 26297053)^848292 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 223 := Nat.prime_eq_prime_of_dvd_pow hq prime_223 hd
            subst q
            change (6 : ZMod 26297053)^117924 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 317 := Nat.prime_eq_prime_of_dvd_pow hq prime_317 hd
            subst q
            change (6 : ZMod 26297053)^82956 ≠ 1
            reduce_mod_char
            decide

theorem prime_26330477 : Nat.Prime 26330477 := by
  apply lucas_primality 26330477 (2 : ZMod 26330477)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26330477 - 1 = (2 : ℕ)^2 * ((109 : ℕ)^1 * ((131 : ℕ)^1 * ((461 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 26330477)^13165238 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
        subst q
        change (2 : ZMod 26330477)^241564 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
          subst q
          change (2 : ZMod 26330477)^200996 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 461 := Nat.prime_eq_prime_of_dvd_pow hq prime_461 hd
          subst q
          change (2 : ZMod 26330477)^57116 ≠ 1
          reduce_mod_char
          decide

theorem prime_26335811 : Nat.Prime 26335811 := by
  apply lucas_primality 26335811 (2 : ZMod 26335811)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26335811 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((2633581 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 26335811)^13167905 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 26335811)^5267162 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2633581 := Nat.prime_eq_prime_of_dvd_pow hq prime_2633581 hd
        subst q
        change (2 : ZMod 26335811)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_26546567 : Nat.Prime 26546567 := by
  apply lucas_primality 26546567 (5 : ZMod 26546567)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26546567 - 1 = (2 : ℕ)^1 * ((43 : ℕ)^1 * ((308681 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 26546567)^13273283 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
        subst q
        change (5 : ZMod 26546567)^617362 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 308681 := Nat.prime_eq_prime_of_dvd_pow hq prime_308681 hd
        subst q
        change (5 : ZMod 26546567)^86 ≠ 1
        reduce_mod_char
        decide

theorem prime_26889299 : Nat.Prime 26889299 := by
  apply lucas_primality 26889299 (2 : ZMod 26889299)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26889299 - 1 = (2 : ℕ)^1 * ((3253 : ℕ)^1 * ((4133 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 26889299)^13444649 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3253 := Nat.prime_eq_prime_of_dvd_pow hq prime_3253 hd
        subst q
        change (2 : ZMod 26889299)^8266 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4133 := Nat.prime_eq_prime_of_dvd_pow hq prime_4133 hd
        subst q
        change (2 : ZMod 26889299)^6506 ≠ 1
        reduce_mod_char
        decide

theorem prime_26925797 : Nat.Prime 26925797 := by
  apply lucas_primality 26925797 (2 : ZMod 26925797)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26925797 - 1 = (2 : ℕ)^2 * ((6731449 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 26925797)^13462898 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 6731449 := Nat.prime_eq_prime_of_dvd_pow hq prime_6731449 hd
      subst q
      change (2 : ZMod 26925797)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_26998009 : Nat.Prime 26998009 := by
  apply lucas_primality 26998009 (7 : ZMod 26998009)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26998009 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((41 : ℕ)^1 * ((27437 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 26998009)^13499004 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 26998009)^8999336 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (7 : ZMod 26998009)^658488 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 27437 := Nat.prime_eq_prime_of_dvd_pow hq prime_27437 hd
          subst q
          change (7 : ZMod 26998009)^984 ≠ 1
          reduce_mod_char
          decide

theorem prime_27011987 : Nat.Prime 27011987 := by
  apply lucas_primality 27011987 (2 : ZMod 27011987)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 27011987 - 1 = (2 : ℕ)^1 * ((13505993 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 27011987)^13505993 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 13505993 := Nat.prime_eq_prime_of_dvd_pow hq prime_13505993 hd
      subst q
      change (2 : ZMod 27011987)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_27282953 : Nat.Prime 27282953 := by
  apply lucas_primality 27282953 (3 : ZMod 27282953)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 27282953 - 1 = (2 : ℕ)^3 * ((3410369 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 27282953)^13641476 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3410369 := Nat.prime_eq_prime_of_dvd_pow hq prime_3410369 hd
      subst q
      change (3 : ZMod 27282953)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_27636481 : Nat.Prime 27636481 := by
  apply lucas_primality 27636481 (13 : ZMod 27636481)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 27636481 - 1 = (2 : ℕ)^8 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((2399 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 27636481)^13818240 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 27636481)^9212160 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 27636481)^5527296 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2399 := Nat.prime_eq_prime_of_dvd_pow hq prime_2399 hd
          subst q
          change (13 : ZMod 27636481)^11520 ≠ 1
          reduce_mod_char
          decide

theorem prime_27794911 : Nat.Prime 27794911 := by
  apply lucas_primality 27794911 (7 : ZMod 27794911)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 27794911 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^2 * ((13 : ℕ)^1 * ((19 : ℕ)^1 * ((31 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 27794911)^13897455 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 27794911)^9264970 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 27794911)^5558982 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (7 : ZMod 27794911)^2526810 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
              subst q
              change (7 : ZMod 27794911)^2138070 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
                subst q
                change (7 : ZMod 27794911)^1462890 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
                subst q
                change (7 : ZMod 27794911)^896610 ≠ 1
                reduce_mod_char
                decide

theorem prime_27905821 : Nat.Prime 27905821 := by
  apply lucas_primality 27905821 (6 : ZMod 27905821)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 27905821 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((59 : ℕ)^1 * ((7883 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 27905821)^13952910 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 27905821)^9301940 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 27905821)^5581164 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
            subst q
            change (6 : ZMod 27905821)^472980 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 7883 := Nat.prime_eq_prime_of_dvd_pow hq prime_7883 hd
            subst q
            change (6 : ZMod 27905821)^3540 ≠ 1
            reduce_mod_char
            decide

theorem prime_28039657 : Nat.Prime 28039657 := by
  apply lucas_primality 28039657 (10 : ZMod 28039657)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 28039657 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((1168319 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 28039657)^14019828 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 28039657)^9346552 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1168319 := Nat.prime_eq_prime_of_dvd_pow hq prime_1168319 hd
        subst q
        change (10 : ZMod 28039657)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_28054993 : Nat.Prime 28054993 := by
  apply lucas_primality 28054993 (11 : ZMod 28054993)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 28054993 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((83497 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 28054993)^14027496 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 28054993)^9351664 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (11 : ZMod 28054993)^4007856 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 83497 := Nat.prime_eq_prime_of_dvd_pow hq prime_83497 hd
          subst q
          change (11 : ZMod 28054993)^336 ≠ 1
          reduce_mod_char
          decide

theorem prime_28932353 : Nat.Prime 28932353 := by
  apply lucas_primality 28932353 (3 : ZMod 28932353)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 28932353 - 1 = (2 : ℕ)^8 * ((113017 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 28932353)^14466176 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 113017 := Nat.prime_eq_prime_of_dvd_pow hq prime_113017 hd
      subst q
      change (3 : ZMod 28932353)^256 ≠ 1
      reduce_mod_char
      decide

theorem prime_28965071 : Nat.Prime 28965071 := by
  apply lucas_primality 28965071 (7 : ZMod 28965071)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 28965071 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((2896507 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 28965071)^14482535 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 28965071)^5793014 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2896507 := Nat.prime_eq_prime_of_dvd_pow hq prime_2896507 hd
        subst q
        change (7 : ZMod 28965071)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_29085439 : Nat.Prime 29085439 := by
  apply lucas_primality 29085439 (11 : ZMod 29085439)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 29085439 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((4847573 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 29085439)^14542719 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 29085439)^9695146 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4847573 := Nat.prime_eq_prime_of_dvd_pow hq prime_4847573 hd
        subst q
        change (11 : ZMod 29085439)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_29178907 : Nat.Prime 29178907 := by
  apply lucas_primality 29178907 (7 : ZMod 29178907)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 29178907 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1847 : ℕ)^1 * ((2633 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 29178907)^14589453 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 29178907)^9726302 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1847 := Nat.prime_eq_prime_of_dvd_pow hq prime_1847 hd
          subst q
          change (7 : ZMod 29178907)^15798 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2633 := Nat.prime_eq_prime_of_dvd_pow hq prime_2633 hd
          subst q
          change (7 : ZMod 29178907)^11082 ≠ 1
          reduce_mod_char
          decide

theorem prime_29667541 : Nat.Prime 29667541 := by
  apply lucas_primality 29667541 (2 : ZMod 29667541)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 29667541 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^2 * ((10091 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 29667541)^14833770 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 29667541)^9889180 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 29667541)^5933508 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (2 : ZMod 29667541)^4238220 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 10091 := Nat.prime_eq_prime_of_dvd_pow hq prime_10091 hd
            subst q
            change (2 : ZMod 29667541)^2940 ≠ 1
            reduce_mod_char
            decide

theorem prime_29724881 : Nat.Prime 29724881 := by
  apply lucas_primality 29724881 (3 : ZMod 29724881)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 29724881 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((371561 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 29724881)^14862440 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 29724881)^5944976 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 371561 := Nat.prime_eq_prime_of_dvd_pow hq prime_371561 hd
        subst q
        change (3 : ZMod 29724881)^80 ≠ 1
        reduce_mod_char
        decide

theorem prime_30041383 : Nat.Prime 30041383 := by
  apply lucas_primality 30041383 (5 : ZMod 30041383)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 30041383 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((269 : ℕ)^1 * ((2659 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 30041383)^15020691 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 30041383)^10013794 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 30041383)^4291626 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
            subst q
            change (5 : ZMod 30041383)^111678 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2659 := Nat.prime_eq_prime_of_dvd_pow hq prime_2659 hd
            subst q
            change (5 : ZMod 30041383)^11298 ≠ 1
            reduce_mod_char
            decide

theorem prime_30115537 : Nat.Prime 30115537 := by
  apply lucas_primality 30115537 (5 : ZMod 30115537)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 30115537 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((57037 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 30115537)^15057768 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 30115537)^10038512 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 30115537)^2737776 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 57037 := Nat.prime_eq_prime_of_dvd_pow hq prime_57037 hd
          subst q
          change (5 : ZMod 30115537)^528 ≠ 1
          reduce_mod_char
          decide

theorem prime_30122161 : Nat.Prime 30122161 := by
  apply lucas_primality 30122161 (41 : ZMod 30122161)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 30122161 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((125509 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (41 : ZMod 30122161)^15061080 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (41 : ZMod 30122161)^10040720 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (41 : ZMod 30122161)^6024432 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 125509 := Nat.prime_eq_prime_of_dvd_pow hq prime_125509 hd
          subst q
          change (41 : ZMod 30122161)^240 ≠ 1
          reduce_mod_char
          decide

theorem prime_30216203 : Nat.Prime 30216203 := by
  apply lucas_primality 30216203 (2 : ZMod 30216203)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 30216203 - 1 = (2 : ℕ)^1 * ((29 : ℕ)^1 * ((520969 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 30216203)^15108101 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (2 : ZMod 30216203)^1041938 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 520969 := Nat.prime_eq_prime_of_dvd_pow hq prime_520969 hd
        subst q
        change (2 : ZMod 30216203)^58 ≠ 1
        reduce_mod_char
        decide

theorem prime_30267593 : Nat.Prime 30267593 := by
  apply lucas_primality 30267593 (3 : ZMod 30267593)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 30267593 - 1 = (2 : ℕ)^3 * ((3783449 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 30267593)^15133796 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3783449 := Nat.prime_eq_prime_of_dvd_pow hq prime_3783449 hd
      subst q
      change (3 : ZMod 30267593)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_30596729 : Nat.Prime 30596729 := by
  apply lucas_primality 30596729 (3 : ZMod 30596729)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 30596729 - 1 = (2 : ℕ)^3 * ((3824591 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 30596729)^15298364 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3824591 := Nat.prime_eq_prime_of_dvd_pow hq prime_3824591 hd
      subst q
      change (3 : ZMod 30596729)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_30671539 : Nat.Prime 30671539 := by
  apply lucas_primality 30671539 (2 : ZMod 30671539)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 30671539 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5111923 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 30671539)^15335769 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 30671539)^10223846 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5111923 := Nat.prime_eq_prime_of_dvd_pow hq prime_5111923 hd
        subst q
        change (2 : ZMod 30671539)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_30786757 : Nat.Prime 30786757 := by
  apply lucas_primality 30786757 (2 : ZMod 30786757)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 30786757 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^2 * ((13 : ℕ)^1 * ((233 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 30786757)^15393378 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 30786757)^10262252 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 30786757)^4398108 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (2 : ZMod 30786757)^2798796 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
              subst q
              change (2 : ZMod 30786757)^2368212 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
              subst q
              change (2 : ZMod 30786757)^132132 ≠ 1
              reduce_mod_char
              decide

theorem prime_30846601 : Nat.Prime 30846601 := by
  apply lucas_primality 30846601 (13 : ZMod 30846601)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 30846601 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((5 : ℕ)^2 * ((17137 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 30846601)^15423300 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 30846601)^10282200 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 30846601)^6169320 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17137 := Nat.prime_eq_prime_of_dvd_pow hq prime_17137 hd
          subst q
          change (13 : ZMod 30846601)^1800 ≠ 1
          reduce_mod_char
          decide

theorem prime_31022521 : Nat.Prime 31022521 := by
  apply lucas_primality 31022521 (7 : ZMod 31022521)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 31022521 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((258521 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 31022521)^15511260 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 31022521)^10340840 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 31022521)^6204504 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 258521 := Nat.prime_eq_prime_of_dvd_pow hq prime_258521 hd
          subst q
          change (7 : ZMod 31022521)^120 ≠ 1
          reduce_mod_char
          decide

theorem prime_31120291 : Nat.Prime 31120291 := by
  apply lucas_primality 31120291 (2 : ZMod 31120291)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 31120291 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((19 : ℕ)^1 * ((18199 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 31120291)^15560145 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 31120291)^10373430 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 31120291)^6224058 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (2 : ZMod 31120291)^1637910 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 18199 := Nat.prime_eq_prime_of_dvd_pow hq prime_18199 hd
            subst q
            change (2 : ZMod 31120291)^1710 ≠ 1
            reduce_mod_char
            decide

theorem prime_31507283 : Nat.Prime 31507283 := by
  apply lucas_primality 31507283 (2 : ZMod 31507283)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 31507283 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((29 : ℕ)^1 * ((28591 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 31507283)^15753641 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 31507283)^1658278 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (2 : ZMod 31507283)^1086458 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 28591 := Nat.prime_eq_prime_of_dvd_pow hq prime_28591 hd
          subst q
          change (2 : ZMod 31507283)^1102 ≠ 1
          reduce_mod_char
          decide

theorem prime_31676119 : Nat.Prime 31676119 := by
  apply lucas_primality 31676119 (6 : ZMod 31676119)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 31676119 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5279353 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 31676119)^15838059 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 31676119)^10558706 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5279353 := Nat.prime_eq_prime_of_dvd_pow hq prime_5279353 hd
        subst q
        change (6 : ZMod 31676119)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_32101453 : Nat.Prime 32101453 := by
  apply lucas_primality 32101453 (2 : ZMod 32101453)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32101453 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((891707 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 32101453)^16050726 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 32101453)^10700484 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 891707 := Nat.prime_eq_prime_of_dvd_pow hq prime_891707 hd
        subst q
        change (2 : ZMod 32101453)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_32107433 : Nat.Prime 32107433 := by
  apply lucas_primality 32107433 (3 : ZMod 32107433)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32107433 - 1 = (2 : ℕ)^3 * ((7 : ℕ)^1 * ((151 : ℕ)^1 * ((3797 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 32107433)^16053716 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 32107433)^4586776 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
          subst q
          change (3 : ZMod 32107433)^212632 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3797 := Nat.prime_eq_prime_of_dvd_pow hq prime_3797 hd
          subst q
          change (3 : ZMod 32107433)^8456 ≠ 1
          reduce_mod_char
          decide

theorem prime_32238361 : Nat.Prime 32238361 := by
  apply lucas_primality 32238361 (29 : ZMod 32238361)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32238361 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((1163 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (29 : ZMod 32238361)^16119180 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (29 : ZMod 32238361)^10746120 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (29 : ZMod 32238361)^6447672 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (29 : ZMod 32238361)^4605480 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
              subst q
              change (29 : ZMod 32238361)^2930760 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1163 := Nat.prime_eq_prime_of_dvd_pow hq prime_1163 hd
              subst q
              change (29 : ZMod 32238361)^27720 ≠ 1
              reduce_mod_char
              decide

theorem prime_32763209 : Nat.Prime 32763209 := by
  apply lucas_primality 32763209 (3 : ZMod 32763209)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32763209 - 1 = (2 : ℕ)^3 * ((4095401 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 32763209)^16381604 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 4095401 := Nat.prime_eq_prime_of_dvd_pow hq prime_4095401 hd
      subst q
      change (3 : ZMod 32763209)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_32921689 : Nat.Prime 32921689 := by
  apply lucas_primality 32921689 (7 : ZMod 32921689)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32921689 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((41 : ℕ)^1 * ((33457 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 32921689)^16460844 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 32921689)^10973896 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (7 : ZMod 32921689)^802968 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 33457 := Nat.prime_eq_prime_of_dvd_pow hq prime_33457 hd
          subst q
          change (7 : ZMod 32921689)^984 ≠ 1
          reduce_mod_char
          decide

theorem prime_33110383 : Nat.Prime 33110383 := by
  apply lucas_primality 33110383 (3 : ZMod 33110383)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 33110383 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5518397 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 33110383)^16555191 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 33110383)^11036794 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5518397 := Nat.prime_eq_prime_of_dvd_pow hq prime_5518397 hd
        subst q
        change (3 : ZMod 33110383)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_34012229 : Nat.Prime 34012229 := by
  apply lucas_primality 34012229 (2 : ZMod 34012229)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34012229 - 1 = (2 : ℕ)^2 * ((8503057 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 34012229)^17006114 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 8503057 := Nat.prime_eq_prime_of_dvd_pow hq prime_8503057 hd
      subst q
      change (2 : ZMod 34012229)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_34082887 : Nat.Prime 34082887 := by
  apply lucas_primality 34082887 (3 : ZMod 34082887)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34082887 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((2297 : ℕ)^1 * ((2473 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 34082887)^17041443 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 34082887)^11360962 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2297 := Nat.prime_eq_prime_of_dvd_pow hq prime_2297 hd
          subst q
          change (3 : ZMod 34082887)^14838 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2473 := Nat.prime_eq_prime_of_dvd_pow hq prime_2473 hd
          subst q
          change (3 : ZMod 34082887)^13782 ≠ 1
          reduce_mod_char
          decide

theorem prime_34169831 : Nat.Prime 34169831 := by
  apply lucas_primality 34169831 (11 : ZMod 34169831)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34169831 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((29 : ℕ)^2 * ((239 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 34169831)^17084915 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 34169831)^6833966 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (11 : ZMod 34169831)^2009990 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (11 : ZMod 34169831)^1178270 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 239 := Nat.prime_eq_prime_of_dvd_pow hq prime_239 hd
            subst q
            change (11 : ZMod 34169831)^142970 ≠ 1
            reduce_mod_char
            decide

theorem prime_34257617 : Nat.Prime 34257617 := by
  apply lucas_primality 34257617 (3 : ZMod 34257617)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34257617 - 1 = (2 : ℕ)^4 * ((751 : ℕ)^1 * ((2851 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 34257617)^17128808 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 751 := Nat.prime_eq_prime_of_dvd_pow hq prime_751 hd
        subst q
        change (3 : ZMod 34257617)^45616 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2851 := Nat.prime_eq_prime_of_dvd_pow hq prime_2851 hd
        subst q
        change (3 : ZMod 34257617)^12016 ≠ 1
        reduce_mod_char
        decide

theorem prime_34395409 : Nat.Prime 34395409 := by
  apply lucas_primality 34395409 (7 : ZMod 34395409)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34395409 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^3 * ((103 : ℕ)^1 * ((773 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 34395409)^17197704 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 34395409)^11465136 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
          subst q
          change (7 : ZMod 34395409)^333936 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 773 := Nat.prime_eq_prime_of_dvd_pow hq prime_773 hd
          subst q
          change (7 : ZMod 34395409)^44496 ≠ 1
          reduce_mod_char
          decide

theorem prime_34894397 : Nat.Prime 34894397 := by
  apply lucas_primality 34894397 (2 : ZMod 34894397)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34894397 - 1 = (2 : ℕ)^2 * ((1493 : ℕ)^1 * ((5843 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 34894397)^17447198 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1493 := Nat.prime_eq_prime_of_dvd_pow hq prime_1493 hd
        subst q
        change (2 : ZMod 34894397)^23372 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5843 := Nat.prime_eq_prime_of_dvd_pow hq prime_5843 hd
        subst q
        change (2 : ZMod 34894397)^5972 ≠ 1
        reduce_mod_char
        decide

theorem prime_34998487 : Nat.Prime 34998487 := by
  apply lucas_primality 34998487 (6 : ZMod 34998487)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34998487 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1217 : ℕ)^1 * ((4793 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 34998487)^17499243 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 34998487)^11666162 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1217 := Nat.prime_eq_prime_of_dvd_pow hq prime_1217 hd
          subst q
          change (6 : ZMod 34998487)^28758 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4793 := Nat.prime_eq_prime_of_dvd_pow hq prime_4793 hd
          subst q
          change (6 : ZMod 34998487)^7302 ≠ 1
          reduce_mod_char
          decide

theorem prime_35024173 : Nat.Prime 35024173 := by
  apply lucas_primality 35024173 (2 : ZMod 35024173)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 35024173 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((31 : ℕ)^1 * ((94151 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 35024173)^17512086 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 35024173)^11674724 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (2 : ZMod 35024173)^1129812 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 94151 := Nat.prime_eq_prime_of_dvd_pow hq prime_94151 hd
          subst q
          change (2 : ZMod 35024173)^372 ≠ 1
          reduce_mod_char
          decide

theorem prime_35456251 : Nat.Prime 35456251 := by
  apply lucas_primality 35456251 (3 : ZMod 35456251)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 35456251 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^5 * ((31 : ℕ)^1 * ((61 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 35456251)^17728125 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 35456251)^11818750 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 35456251)^7091250 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (3 : ZMod 35456251)^1143750 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
            subst q
            change (3 : ZMod 35456251)^581250 ≠ 1
            reduce_mod_char
            decide

theorem prime_36327703 : Nat.Prime 36327703 := by
  apply lucas_primality 36327703 (5 : ZMod 36327703)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 36327703 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((6054617 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 36327703)^18163851 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 36327703)^12109234 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 6054617 := Nat.prime_eq_prime_of_dvd_pow hq prime_6054617 hd
        subst q
        change (5 : ZMod 36327703)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_36822811 : Nat.Prime 36822811 := by
  apply lucas_primality 36822811 (7 : ZMod 36822811)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 36822811 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((53 : ℕ)^1 * ((23159 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 36822811)^18411405 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 36822811)^12274270 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 36822811)^7364562 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
            subst q
            change (7 : ZMod 36822811)^694770 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 23159 := Nat.prime_eq_prime_of_dvd_pow hq prime_23159 hd
            subst q
            change (7 : ZMod 36822811)^1590 ≠ 1
            reduce_mod_char
            decide

theorem prime_37357973 : Nat.Prime 37357973 := by
  apply lucas_primality 37357973 (2 : ZMod 37357973)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 37357973 - 1 = (2 : ℕ)^2 * ((211 : ℕ)^1 * ((44263 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 37357973)^18678986 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 211 := Nat.prime_eq_prime_of_dvd_pow hq prime_211 hd
        subst q
        change (2 : ZMod 37357973)^177052 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 44263 := Nat.prime_eq_prime_of_dvd_pow hq prime_44263 hd
        subst q
        change (2 : ZMod 37357973)^844 ≠ 1
        reduce_mod_char
        decide

theorem prime_37378807 : Nat.Prime 37378807 := by
  apply lucas_primality 37378807 (3 : ZMod 37378807)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 37378807 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((37 : ℕ)^1 * ((137 : ℕ)^1 * ((1229 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 37378807)^18689403 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 37378807)^12459602 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (3 : ZMod 37378807)^1010238 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
            subst q
            change (3 : ZMod 37378807)^272838 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1229 := Nat.prime_eq_prime_of_dvd_pow hq prime_1229 hd
            subst q
            change (3 : ZMod 37378807)^30414 ≠ 1
            reduce_mod_char
            decide

theorem prime_38411641 : Nat.Prime 38411641 := by
  apply lucas_primality 38411641 (29 : ZMod 38411641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 38411641 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((106699 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (29 : ZMod 38411641)^19205820 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (29 : ZMod 38411641)^12803880 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (29 : ZMod 38411641)^7682328 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 106699 := Nat.prime_eq_prime_of_dvd_pow hq prime_106699 hd
          subst q
          change (29 : ZMod 38411641)^360 ≠ 1
          reduce_mod_char
          decide

theorem prime_38830697 : Nat.Prime 38830697 := by
  apply lucas_primality 38830697 (3 : ZMod 38830697)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 38830697 - 1 = (2 : ℕ)^3 * ((4853837 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 38830697)^19415348 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 4853837 := Nat.prime_eq_prime_of_dvd_pow hq prime_4853837 hd
      subst q
      change (3 : ZMod 38830697)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_39019163 : Nat.Prime 39019163 := by
  apply lucas_primality 39019163 (2 : ZMod 39019163)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 39019163 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((214391 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 39019163)^19509581 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 39019163)^5574166 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 39019163)^3001474 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 214391 := Nat.prime_eq_prime_of_dvd_pow hq prime_214391 hd
          subst q
          change (2 : ZMod 39019163)^182 ≠ 1
          reduce_mod_char
          decide

theorem prime_39059821 : Nat.Prime 39059821 := by
  apply lucas_primality 39059821 (2 : ZMod 39059821)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 39059821 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^7 * ((5 : ℕ)^1 * ((19 : ℕ)^1 * ((47 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 39059821)^19529910 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 39059821)^13019940 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 39059821)^7811964 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (2 : ZMod 39059821)^2055780 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
            subst q
            change (2 : ZMod 39059821)^831060 ≠ 1
            reduce_mod_char
            decide

theorem prime_39244991 : Nat.Prime 39244991 := by
  apply lucas_primality 39244991 (11 : ZMod 39244991)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 39244991 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((3924499 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 39244991)^19622495 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 39244991)^7848998 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3924499 := Nat.prime_eq_prime_of_dvd_pow hq prime_3924499 hd
        subst q
        change (11 : ZMod 39244991)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_39454957 : Nat.Prime 39454957 := by
  apply lucas_primality 39454957 (5 : ZMod 39454957)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 39454957 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((41 : ℕ)^1 * ((26731 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 39454957)^19727478 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 39454957)^13151652 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (5 : ZMod 39454957)^962316 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 26731 := Nat.prime_eq_prime_of_dvd_pow hq prime_26731 hd
          subst q
          change (5 : ZMod 39454957)^1476 ≠ 1
          reduce_mod_char
          decide

theorem prime_39662933 : Nat.Prime 39662933 := by
  apply lucas_primality 39662933 (2 : ZMod 39662933)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 39662933 - 1 = (2 : ℕ)^2 * ((61 : ℕ)^1 * ((162553 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 39662933)^19831466 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
        subst q
        change (2 : ZMod 39662933)^650212 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 162553 := Nat.prime_eq_prime_of_dvd_pow hq prime_162553 hd
        subst q
        change (2 : ZMod 39662933)^244 ≠ 1
        reduce_mod_char
        decide

theorem prime_40011583 : Nat.Prime 40011583 := by
  apply lucas_primality 40011583 (3 : ZMod 40011583)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 40011583 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((23 : ℕ)^1 * ((22303 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 40011583)^20005791 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 40011583)^13337194 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 40011583)^3077814 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (3 : ZMod 40011583)^1739634 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 22303 := Nat.prime_eq_prime_of_dvd_pow hq prime_22303 hd
            subst q
            change (3 : ZMod 40011583)^1794 ≠ 1
            reduce_mod_char
            decide

theorem prime_40339441 : Nat.Prime 40339441 := by
  apply lucas_primality 40339441 (22 : ZMod 40339441)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 40339441 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((179 : ℕ)^1 * ((313 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (22 : ZMod 40339441)^20169720 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (22 : ZMod 40339441)^13446480 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (22 : ZMod 40339441)^8067888 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 179 := Nat.prime_eq_prime_of_dvd_pow hq prime_179 hd
            subst q
            change (22 : ZMod 40339441)^225360 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 313 := Nat.prime_eq_prime_of_dvd_pow hq prime_313 hd
            subst q
            change (22 : ZMod 40339441)^128880 ≠ 1
            reduce_mod_char
            decide

theorem prime_40773781 : Nat.Prime 40773781 := by
  apply lucas_primality 40773781 (2 : ZMod 40773781)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 40773781 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^4 * ((5 : ℕ)^1 * ((25169 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 40773781)^20386890 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 40773781)^13591260 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 40773781)^8154756 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 25169 := Nat.prime_eq_prime_of_dvd_pow hq prime_25169 hd
          subst q
          change (2 : ZMod 40773781)^1620 ≠ 1
          reduce_mod_char
          decide

theorem prime_40972903 : Nat.Prime 40972903 := by
  apply lucas_primality 40972903 (3 : ZMod 40972903)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 40972903 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((947 : ℕ)^1 * ((7211 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 40972903)^20486451 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 40972903)^13657634 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 947 := Nat.prime_eq_prime_of_dvd_pow hq prime_947 hd
          subst q
          change (3 : ZMod 40972903)^43266 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7211 := Nat.prime_eq_prime_of_dvd_pow hq prime_7211 hd
          subst q
          change (3 : ZMod 40972903)^5682 ≠ 1
          reduce_mod_char
          decide

theorem prime_41057521 : Nat.Prime 41057521 := by
  apply lucas_primality 41057521 (11 : ZMod 41057521)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 41057521 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((24439 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 41057521)^20528760 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 41057521)^13685840 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 41057521)^8211504 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (11 : ZMod 41057521)^5865360 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 24439 := Nat.prime_eq_prime_of_dvd_pow hq prime_24439 hd
            subst q
            change (11 : ZMod 41057521)^1680 ≠ 1
            reduce_mod_char
            decide

theorem prime_41473141 : Nat.Prime 41473141 := by
  apply lucas_primality 41473141 (13 : ZMod 41473141)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 41473141 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((23 : ℕ)^1 * ((41 : ℕ)^1 * ((733 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 41473141)^20736570 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 41473141)^13824380 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 41473141)^8294628 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (13 : ZMod 41473141)^1803180 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
              subst q
              change (13 : ZMod 41473141)^1011540 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 733 := Nat.prime_eq_prime_of_dvd_pow hq prime_733 hd
              subst q
              change (13 : ZMod 41473141)^56580 ≠ 1
              reduce_mod_char
              decide

theorem prime_41613899 : Nat.Prime 41613899 := by
  apply lucas_primality 41613899 (2 : ZMod 41613899)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 41613899 - 1 = (2 : ℕ)^1 * ((29 : ℕ)^1 * ((433 : ℕ)^1 * ((1657 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 41613899)^20806949 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (2 : ZMod 41613899)^1434962 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 433 := Nat.prime_eq_prime_of_dvd_pow hq prime_433 hd
          subst q
          change (2 : ZMod 41613899)^96106 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1657 := Nat.prime_eq_prime_of_dvd_pow hq prime_1657 hd
          subst q
          change (2 : ZMod 41613899)^25114 ≠ 1
          reduce_mod_char
          decide

theorem prime_41713627 : Nat.Prime 41713627 := by
  apply lucas_primality 41713627 (2 : ZMod 41713627)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 41713627 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((239 : ℕ)^1 * ((1531 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 41713627)^20856813 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 41713627)^13904542 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 41713627)^2195454 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 239 := Nat.prime_eq_prime_of_dvd_pow hq prime_239 hd
            subst q
            change (2 : ZMod 41713627)^174534 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1531 := Nat.prime_eq_prime_of_dvd_pow hq prime_1531 hd
            subst q
            change (2 : ZMod 41713627)^27246 ≠ 1
            reduce_mod_char
            decide

theorem prime_41721941 : Nat.Prime 41721941 := by
  apply lucas_primality 41721941 (3 : ZMod 41721941)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 41721941 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((37 : ℕ)^1 * ((4337 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 41721941)^20860970 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 41721941)^8344388 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 41721941)^3209380 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
            subst q
            change (3 : ZMod 41721941)^1127620 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 4337 := Nat.prime_eq_prime_of_dvd_pow hq prime_4337 hd
            subst q
            change (3 : ZMod 41721941)^9620 ≠ 1
            reduce_mod_char
            decide

theorem prime_41958181 : Nat.Prime 41958181 := by
  apply lucas_primality 41958181 (2 : ZMod 41958181)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 41958181 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((21191 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 41958181)^20979090 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 41958181)^13986060 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 41958181)^8391636 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (2 : ZMod 41958181)^3814380 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 21191 := Nat.prime_eq_prime_of_dvd_pow hq prime_21191 hd
            subst q
            change (2 : ZMod 41958181)^1980 ≠ 1
            reduce_mod_char
            decide

theorem prime_42001171 : Nat.Prime 42001171 := by
  apply lucas_primality 42001171 (10 : ZMod 42001171)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 42001171 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((1400039 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 42001171)^21000585 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 42001171)^14000390 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 42001171)^8400234 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1400039 := Nat.prime_eq_prime_of_dvd_pow hq prime_1400039 hd
          subst q
          change (10 : ZMod 42001171)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_42546211 : Nat.Prime 42546211 := by
  apply lucas_primality 42546211 (19 : ZMod 42546211)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 42546211 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^2 * ((103 : ℕ)^1 * ((281 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 42546211)^21273105 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 42546211)^14182070 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (19 : ZMod 42546211)^8509242 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (19 : ZMod 42546211)^6078030 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
              subst q
              change (19 : ZMod 42546211)^413070 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 281 := Nat.prime_eq_prime_of_dvd_pow hq prime_281 hd
              subst q
              change (19 : ZMod 42546211)^151410 ≠ 1
              reduce_mod_char
              decide

theorem prime_42746689 : Nat.Prime 42746689 := by
  apply lucas_primality 42746689 (7 : ZMod 42746689)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 42746689 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^2 * ((47 : ℕ)^1 * ((1579 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 42746689)^21373344 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 42746689)^14248896 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (7 : ZMod 42746689)^909504 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1579 := Nat.prime_eq_prime_of_dvd_pow hq prime_1579 hd
          subst q
          change (7 : ZMod 42746689)^27072 ≠ 1
          reduce_mod_char
          decide

theorem prime_42761627 : Nat.Prime 42761627 := by
  apply lucas_primality 42761627 (2 : ZMod 42761627)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 42761627 - 1 = (2 : ℕ)^1 * ((21380813 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 42761627)^21380813 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 21380813 := Nat.prime_eq_prime_of_dvd_pow hq prime_21380813 hd
      subst q
      change (2 : ZMod 42761627)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_42762107 : Nat.Prime 42762107 := by
  apply lucas_primality 42762107 (2 : ZMod 42762107)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 42762107 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((23 : ℕ)^1 * ((149 : ℕ)^1 * ((367 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 42762107)^21381053 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 42762107)^2515418 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 42762107)^1859222 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
            subst q
            change (2 : ZMod 42762107)^286994 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 367 := Nat.prime_eq_prime_of_dvd_pow hq prime_367 hd
            subst q
            change (2 : ZMod 42762107)^116518 ≠ 1
            reduce_mod_char
            decide

theorem prime_42794471 : Nat.Prime 42794471 := by
  apply lucas_primality 42794471 (11 : ZMod 42794471)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 42794471 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((59 : ℕ)^1 * ((72533 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 42794471)^21397235 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 42794471)^8558894 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (11 : ZMod 42794471)^725330 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 72533 := Nat.prime_eq_prime_of_dvd_pow hq prime_72533 hd
          subst q
          change (11 : ZMod 42794471)^590 ≠ 1
          reduce_mod_char
          decide

theorem prime_42883073 : Nat.Prime 42883073 := by
  apply lucas_primality 42883073 (3 : ZMod 42883073)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 42883073 - 1 = (2 : ℕ)^11 * ((20939 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 42883073)^21441536 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 20939 := Nat.prime_eq_prime_of_dvd_pow hq prime_20939 hd
      subst q
      change (3 : ZMod 42883073)^2048 ≠ 1
      reduce_mod_char
      decide

theorem prime_43125503 : Nat.Prime 43125503 := by
  apply lucas_primality 43125503 (5 : ZMod 43125503)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 43125503 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((3080393 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 43125503)^21562751 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 43125503)^6160786 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3080393 := Nat.prime_eq_prime_of_dvd_pow hq prime_3080393 hd
        subst q
        change (5 : ZMod 43125503)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_43155143 : Nat.Prime 43155143 := by
  apply lucas_primality 43155143 (5 : ZMod 43155143)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 43155143 - 1 = (2 : ℕ)^1 * ((2953 : ℕ)^1 * ((7307 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 43155143)^21577571 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 2953 := Nat.prime_eq_prime_of_dvd_pow hq prime_2953 hd
        subst q
        change (5 : ZMod 43155143)^14614 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7307 := Nat.prime_eq_prime_of_dvd_pow hq prime_7307 hd
        subst q
        change (5 : ZMod 43155143)^5906 ≠ 1
        reduce_mod_char
        decide

theorem prime_43379773 : Nat.Prime 43379773 := by
  apply lucas_primality 43379773 (2 : ZMod 43379773)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 43379773 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((3614981 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 43379773)^21689886 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 43379773)^14459924 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3614981 := Nat.prime_eq_prime_of_dvd_pow hq prime_3614981 hd
        subst q
        change (2 : ZMod 43379773)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_43380119 : Nat.Prime 43380119 := by
  apply lucas_primality 43380119 (17 : ZMod 43380119)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 43380119 - 1 = (2 : ℕ)^1 * ((21690059 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 43380119)^21690059 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 21690059 := Nat.prime_eq_prime_of_dvd_pow hq prime_21690059 hd
      subst q
      change (17 : ZMod 43380119)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_43469809 : Nat.Prime 43469809 := by
  apply lucas_primality 43469809 (7 : ZMod 43469809)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 43469809 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((905621 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 43469809)^21734904 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 43469809)^14489936 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 905621 := Nat.prime_eq_prime_of_dvd_pow hq prime_905621 hd
        subst q
        change (7 : ZMod 43469809)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_43502161 : Nat.Prime 43502161 := by
  apply lucas_primality 43502161 (7 : ZMod 43502161)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 43502161 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((73 : ℕ)^1 * ((191 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 43502161)^21751080 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 43502161)^14500720 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 43502161)^8700432 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (7 : ZMod 43502161)^3346320 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
              subst q
              change (7 : ZMod 43502161)^595920 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
              subst q
              change (7 : ZMod 43502161)^227760 ≠ 1
              reduce_mod_char
              decide

theorem prime_44350961 : Nat.Prime 44350961 := by
  apply lucas_primality 44350961 (6 : ZMod 44350961)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 44350961 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((32611 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 44350961)^22175480 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 44350961)^8870192 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (6 : ZMod 44350961)^2608880 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 32611 := Nat.prime_eq_prime_of_dvd_pow hq prime_32611 hd
          subst q
          change (6 : ZMod 44350961)^1360 ≠ 1
          reduce_mod_char
          decide

theorem prime_44695661 : Nat.Prime 44695661 := by
  apply lucas_primality 44695661 (7 : ZMod 44695661)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 44695661 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((97 : ℕ)^1 * ((23039 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 44695661)^22347830 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 44695661)^8939132 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
          subst q
          change (7 : ZMod 44695661)^460780 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 23039 := Nat.prime_eq_prime_of_dvd_pow hq prime_23039 hd
          subst q
          change (7 : ZMod 44695661)^1940 ≠ 1
          reduce_mod_char
          decide

theorem prime_45307021 : Nat.Prime 45307021 := by
  apply lucas_primality 45307021 (2 : ZMod 45307021)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 45307021 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((19 : ℕ)^1 * ((3613 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 45307021)^22653510 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 45307021)^15102340 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 45307021)^9061404 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (2 : ZMod 45307021)^4118820 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
              subst q
              change (2 : ZMod 45307021)^2384580 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 3613 := Nat.prime_eq_prime_of_dvd_pow hq prime_3613 hd
              subst q
              change (2 : ZMod 45307021)^12540 ≠ 1
              reduce_mod_char
              decide

theorem prime_45373849 : Nat.Prime 45373849 := by
  apply lucas_primality 45373849 (7 : ZMod 45373849)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 45373849 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((23 : ℕ)^1 * ((6323 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 45373849)^22686924 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 45373849)^15124616 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (7 : ZMod 45373849)^3490296 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (7 : ZMod 45373849)^1972776 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 6323 := Nat.prime_eq_prime_of_dvd_pow hq prime_6323 hd
            subst q
            change (7 : ZMod 45373849)^7176 ≠ 1
            reduce_mod_char
            decide

theorem prime_46631647 : Nat.Prime 46631647 := by
  apply lucas_primality 46631647 (5 : ZMod 46631647)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 46631647 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((17 : ℕ)^1 * ((79 : ℕ)^1 * ((643 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 46631647)^23315823 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 46631647)^15543882 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (5 : ZMod 46631647)^2743038 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
            subst q
            change (5 : ZMod 46631647)^590274 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 643 := Nat.prime_eq_prime_of_dvd_pow hq prime_643 hd
            subst q
            change (5 : ZMod 46631647)^72522 ≠ 1
            reduce_mod_char
            decide

theorem prime_46737917 : Nat.Prime 46737917 := by
  apply lucas_primality 46737917 (2 : ZMod 46737917)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 46737917 - 1 = (2 : ℕ)^2 * ((139 : ℕ)^1 * ((84061 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 46737917)^23368958 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
        subst q
        change (2 : ZMod 46737917)^336244 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 84061 := Nat.prime_eq_prime_of_dvd_pow hq prime_84061 hd
        subst q
        change (2 : ZMod 46737917)^556 ≠ 1
        reduce_mod_char
        decide

theorem prime_47045897 : Nat.Prime 47045897 := by
  apply lucas_primality 47045897 (3 : ZMod 47045897)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 47045897 - 1 = (2 : ℕ)^3 * ((5880737 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 47045897)^23522948 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 5880737 := Nat.prime_eq_prime_of_dvd_pow hq prime_5880737 hd
      subst q
      change (3 : ZMod 47045897)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_47323579 : Nat.Prime 47323579 := by
  apply lucas_primality 47323579 (2 : ZMod 47323579)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 47323579 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7887263 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 47323579)^23661789 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 47323579)^15774526 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7887263 := Nat.prime_eq_prime_of_dvd_pow hq prime_7887263 hd
        subst q
        change (2 : ZMod 47323579)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_48464411 : Nat.Prime 48464411 := by
  apply lucas_primality 48464411 (6 : ZMod 48464411)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 48464411 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((4846441 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 48464411)^24232205 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 48464411)^9692882 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4846441 := Nat.prime_eq_prime_of_dvd_pow hq prime_4846441 hd
        subst q
        change (6 : ZMod 48464411)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_48912491 : Nat.Prime 48912491 := by
  apply lucas_primality 48912491 (10 : ZMod 48912491)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 48912491 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((23 : ℕ)^1 * ((19333 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 48912491)^24456245 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (10 : ZMod 48912491)^9782498 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (10 : ZMod 48912491)^4446590 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (10 : ZMod 48912491)^2126630 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 19333 := Nat.prime_eq_prime_of_dvd_pow hq prime_19333 hd
            subst q
            change (10 : ZMod 48912491)^2530 ≠ 1
            reduce_mod_char
            decide

theorem prime_49273681 : Nat.Prime 49273681 := by
  apply lucas_primality 49273681 (19 : ZMod 49273681)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 49273681 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((205307 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 49273681)^24636840 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 49273681)^16424560 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (19 : ZMod 49273681)^9854736 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 205307 := Nat.prime_eq_prime_of_dvd_pow hq prime_205307 hd
          subst q
          change (19 : ZMod 49273681)^240 ≠ 1
          reduce_mod_char
          decide

theorem prime_49961341 : Nat.Prime 49961341 := by
  apply lucas_primality 49961341 (2 : ZMod 49961341)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 49961341 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((647 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 49961341)^24980670 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 49961341)^16653780 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 49961341)^9992268 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (2 : ZMod 49961341)^4541940 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
              subst q
              change (2 : ZMod 49961341)^3843180 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 647 := Nat.prime_eq_prime_of_dvd_pow hq prime_647 hd
              subst q
              change (2 : ZMod 49961341)^77220 ≠ 1
              reduce_mod_char
              decide

theorem prime_50028859 : Nat.Prime 50028859 := by
  apply lucas_primality 50028859 (3 : ZMod 50028859)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 50028859 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((89 : ℕ)^1 * ((167 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 50028859)^25014429 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 50028859)^16676286 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 50028859)^4548078 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (3 : ZMod 50028859)^2942874 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
              subst q
              change (3 : ZMod 50028859)^562122 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
              subst q
              change (3 : ZMod 50028859)^299574 ≠ 1
              reduce_mod_char
              decide

theorem prime_50175137 : Nat.Prime 50175137 := by
  apply lucas_primality 50175137 (3 : ZMod 50175137)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 50175137 - 1 = (2 : ℕ)^5 * ((11 : ℕ)^1 * ((142543 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 50175137)^25087568 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 50175137)^4561376 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 142543 := Nat.prime_eq_prime_of_dvd_pow hq prime_142543 hd
        subst q
        change (3 : ZMod 50175137)^352 ≠ 1
        reduce_mod_char
        decide

theorem prime_50185939 : Nat.Prime 50185939 := by
  apply lucas_primality 50185939 (2 : ZMod 50185939)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 50185939 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((44729 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 50185939)^25092969 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 50185939)^16728646 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 50185939)^4562358 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (2 : ZMod 50185939)^2952114 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 44729 := Nat.prime_eq_prime_of_dvd_pow hq prime_44729 hd
            subst q
            change (2 : ZMod 50185939)^1122 ≠ 1
            reduce_mod_char
            decide

theorem prime_50273359 : Nat.Prime 50273359 := by
  apply lucas_primality 50273359 (3 : ZMod 50273359)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 50273359 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((8378893 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 50273359)^25136679 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 50273359)^16757786 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 8378893 := Nat.prime_eq_prime_of_dvd_pow hq prime_8378893 hd
        subst q
        change (3 : ZMod 50273359)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_50548907 : Nat.Prime 50548907 := by
  apply lucas_primality 50548907 (2 : ZMod 50548907)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 50548907 - 1 = (2 : ℕ)^1 * ((25274453 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 50548907)^25274453 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 25274453 := Nat.prime_eq_prime_of_dvd_pow hq prime_25274453 hd
      subst q
      change (2 : ZMod 50548907)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_50760959 : Nat.Prime 50760959 := by
  apply lucas_primality 50760959 (7 : ZMod 50760959)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 50760959 - 1 = (2 : ℕ)^1 * ((25380479 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 50760959)^25380479 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 25380479 := Nat.prime_eq_prime_of_dvd_pow hq prime_25380479 hd
      subst q
      change (7 : ZMod 50760959)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_52716893 : Nat.Prime 52716893 := by
  apply lucas_primality 52716893 (2 : ZMod 52716893)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 52716893 - 1 = (2 : ℕ)^2 * ((47 : ℕ)^1 * ((280409 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 52716893)^26358446 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (2 : ZMod 52716893)^1121636 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 280409 := Nat.prime_eq_prime_of_dvd_pow hq prime_280409 hd
        subst q
        change (2 : ZMod 52716893)^188 ≠ 1
        reduce_mod_char
        decide

theorem prime_53422541 : Nat.Prime 53422541 := by
  apply lucas_primality 53422541 (10 : ZMod 53422541)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 53422541 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((1193 : ℕ)^1 * ((2239 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 53422541)^26711270 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (10 : ZMod 53422541)^10684508 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1193 := Nat.prime_eq_prime_of_dvd_pow hq prime_1193 hd
          subst q
          change (10 : ZMod 53422541)^44780 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2239 := Nat.prime_eq_prime_of_dvd_pow hq prime_2239 hd
          subst q
          change (10 : ZMod 53422541)^23860 ≠ 1
          reduce_mod_char
          decide

theorem prime_53539961 : Nat.Prime 53539961 := by
  apply lucas_primality 53539961 (3 : ZMod 53539961)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 53539961 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((1338499 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 53539961)^26769980 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 53539961)^10707992 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1338499 := Nat.prime_eq_prime_of_dvd_pow hq prime_1338499 hd
        subst q
        change (3 : ZMod 53539961)^40 ≠ 1
        reduce_mod_char
        decide

theorem prime_54270247 : Nat.Prime 54270247 := by
  apply lucas_primality 54270247 (5 : ZMod 54270247)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 54270247 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((2333 : ℕ)^1 * ((3877 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 54270247)^27135123 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 54270247)^18090082 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2333 := Nat.prime_eq_prime_of_dvd_pow hq prime_2333 hd
          subst q
          change (5 : ZMod 54270247)^23262 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3877 := Nat.prime_eq_prime_of_dvd_pow hq prime_3877 hd
          subst q
          change (5 : ZMod 54270247)^13998 ≠ 1
          reduce_mod_char
          decide

theorem prime_54690529 : Nat.Prime 54690529 := by
  apply lucas_primality 54690529 (7 : ZMod 54690529)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 54690529 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((103 : ℕ)^1 * ((5531 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 54690529)^27345264 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 54690529)^18230176 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
          subst q
          change (7 : ZMod 54690529)^530976 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 5531 := Nat.prime_eq_prime_of_dvd_pow hq prime_5531 hd
          subst q
          change (7 : ZMod 54690529)^9888 ≠ 1
          reduce_mod_char
          decide

theorem prime_54892427 : Nat.Prime 54892427 := by
  apply lucas_primality 54892427 (2 : ZMod 54892427)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 54892427 - 1 = (2 : ℕ)^1 * ((151 : ℕ)^1 * ((181763 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 54892427)^27446213 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
        subst q
        change (2 : ZMod 54892427)^363526 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 181763 := Nat.prime_eq_prime_of_dvd_pow hq prime_181763 hd
        subst q
        change (2 : ZMod 54892427)^302 ≠ 1
        reduce_mod_char
        decide

theorem prime_55805201 : Nat.Prime 55805201 := by
  apply lucas_primality 55805201 (6 : ZMod 55805201)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 55805201 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^2 * ((11 : ℕ)^2 * ((1153 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 55805201)^27902600 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 55805201)^11161040 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (6 : ZMod 55805201)^5073200 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1153 := Nat.prime_eq_prime_of_dvd_pow hq prime_1153 hd
          subst q
          change (6 : ZMod 55805201)^48400 ≠ 1
          reduce_mod_char
          decide

theorem prime_56973481 : Nat.Prime 56973481 := by
  apply lucas_primality 56973481 (7 : ZMod 56973481)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 56973481 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((474779 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 56973481)^28486740 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 56973481)^18991160 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 56973481)^11394696 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 474779 := Nat.prime_eq_prime_of_dvd_pow hq prime_474779 hd
          subst q
          change (7 : ZMod 56973481)^120 ≠ 1
          reduce_mod_char
          decide

theorem prime_57280903 : Nat.Prime 57280903 := by
  apply lucas_primality 57280903 (3 : ZMod 57280903)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 57280903 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((23 : ℕ)^1 * ((43 : ℕ)^1 * ((197 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 57280903)^28640451 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 57280903)^19093634 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 57280903)^8182986 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (3 : ZMod 57280903)^2490474 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
              subst q
              change (3 : ZMod 57280903)^1332114 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
              subst q
              change (3 : ZMod 57280903)^290766 ≠ 1
              reduce_mod_char
              decide

theorem prime_57332047 : Nat.Prime 57332047 := by
  apply lucas_primality 57332047 (5 : ZMod 57332047)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 57332047 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1049 : ℕ)^1 * ((9109 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 57332047)^28666023 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 57332047)^19110682 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1049 := Nat.prime_eq_prime_of_dvd_pow hq prime_1049 hd
          subst q
          change (5 : ZMod 57332047)^54654 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 9109 := Nat.prime_eq_prime_of_dvd_pow hq prime_9109 hd
          subst q
          change (5 : ZMod 57332047)^6294 ≠ 1
          reduce_mod_char
          decide

theorem prime_57912509 : Nat.Prime 57912509 := by
  apply lucas_primality 57912509 (2 : ZMod 57912509)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 57912509 - 1 = (2 : ℕ)^2 * ((127 : ℕ)^1 * ((114001 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 57912509)^28956254 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
        subst q
        change (2 : ZMod 57912509)^456004 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 114001 := Nat.prime_eq_prime_of_dvd_pow hq prime_114001 hd
        subst q
        change (2 : ZMod 57912509)^508 ≠ 1
        reduce_mod_char
        decide

theorem prime_58509727 : Nat.Prime 58509727 := by
  apply lucas_primality 58509727 (5 : ZMod 58509727)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 58509727 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((886511 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 58509727)^29254863 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 58509727)^19503242 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 58509727)^5319066 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 886511 := Nat.prime_eq_prime_of_dvd_pow hq prime_886511 hd
          subst q
          change (5 : ZMod 58509727)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_58812763 : Nat.Prime 58812763 := by
  apply lucas_primality 58812763 (3 : ZMod 58812763)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 58812763 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((719 : ℕ)^1 * ((13633 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 58812763)^29406381 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 58812763)^19604254 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 719 := Nat.prime_eq_prime_of_dvd_pow hq prime_719 hd
          subst q
          change (3 : ZMod 58812763)^81798 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13633 := Nat.prime_eq_prime_of_dvd_pow hq prime_13633 hd
          subst q
          change (3 : ZMod 58812763)^4314 ≠ 1
          reduce_mod_char
          decide

theorem prime_59449763 : Nat.Prime 59449763 := by
  apply lucas_primality 59449763 (2 : ZMod 59449763)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 59449763 - 1 = (2 : ℕ)^1 * ((29724881 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 59449763)^29724881 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 29724881 := Nat.prime_eq_prime_of_dvd_pow hq prime_29724881 hd
      subst q
      change (2 : ZMod 59449763)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_59662051 : Nat.Prime 59662051 := by
  apply lucas_primality 59662051 (2 : ZMod 59662051)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 59662051 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((7 : ℕ)^1 * ((56821 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 59662051)^29831025 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 59662051)^19887350 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 59662051)^11932410 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (2 : ZMod 59662051)^8523150 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 56821 := Nat.prime_eq_prime_of_dvd_pow hq prime_56821 hd
            subst q
            change (2 : ZMod 59662051)^1050 ≠ 1
            reduce_mod_char
            decide

theorem prime_60037799 : Nat.Prime 60037799 := by
  apply lucas_primality 60037799 (23 : ZMod 60037799)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 60037799 - 1 = (2 : ℕ)^1 * ((89 : ℕ)^1 * ((337291 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (23 : ZMod 60037799)^30018899 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
        subst q
        change (23 : ZMod 60037799)^674582 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 337291 := Nat.prime_eq_prime_of_dvd_pow hq prime_337291 hd
        subst q
        change (23 : ZMod 60037799)^178 ≠ 1
        reduce_mod_char
        decide

theorem prime_60050971 : Nat.Prime 60050971 := by
  apply lucas_primality 60050971 (10 : ZMod 60050971)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 60050971 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((5 : ℕ)^1 * ((7 : ℕ)^2 * ((17 : ℕ)^1 * ((89 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 60050971)^30025485 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 60050971)^20016990 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 60050971)^12010194 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (10 : ZMod 60050971)^8578710 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
              subst q
              change (10 : ZMod 60050971)^3532410 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
              subst q
              change (10 : ZMod 60050971)^674730 ≠ 1
              reduce_mod_char
              decide

theorem prime_60162937 : Nat.Prime 60162937 := by
  apply lucas_primality 60162937 (10 : ZMod 60162937)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 60162937 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((29 : ℕ)^1 * ((86441 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 60162937)^30081468 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 60162937)^20054312 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (10 : ZMod 60162937)^2074584 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 86441 := Nat.prime_eq_prime_of_dvd_pow hq prime_86441 hd
          subst q
          change (10 : ZMod 60162937)^696 ≠ 1
          reduce_mod_char
          decide

theorem prime_60198487 : Nat.Prime 60198487 := by
  apply lucas_primality 60198487 (21 : ZMod 60198487)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 60198487 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((71 : ℕ)^1 * ((141311 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (21 : ZMod 60198487)^30099243 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (21 : ZMod 60198487)^20066162 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
          subst q
          change (21 : ZMod 60198487)^847866 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 141311 := Nat.prime_eq_prime_of_dvd_pow hq prime_141311 hd
          subst q
          change (21 : ZMod 60198487)^426 ≠ 1
          reduce_mod_char
          decide

theorem prime_60587959 : Nat.Prime 60587959 := by
  apply lucas_primality 60587959 (3 : ZMod 60587959)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 60587959 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((433 : ℕ)^1 * ((23321 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 60587959)^30293979 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 60587959)^20195986 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 433 := Nat.prime_eq_prime_of_dvd_pow hq prime_433 hd
          subst q
          change (3 : ZMod 60587959)^139926 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 23321 := Nat.prime_eq_prime_of_dvd_pow hq prime_23321 hd
          subst q
          change (3 : ZMod 60587959)^2598 ≠ 1
          reduce_mod_char
          decide

theorem prime_60757343 : Nat.Prime 60757343 := by
  apply lucas_primality 60757343 (5 : ZMod 60757343)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 60757343 - 1 = (2 : ℕ)^1 * ((61 : ℕ)^1 * ((67 : ℕ)^1 * ((7433 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 60757343)^30378671 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
        subst q
        change (5 : ZMod 60757343)^996022 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (5 : ZMod 60757343)^906826 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7433 := Nat.prime_eq_prime_of_dvd_pow hq prime_7433 hd
          subst q
          change (5 : ZMod 60757343)^8174 ≠ 1
          reduce_mod_char
          decide

theorem prime_61004131 : Nat.Prime 61004131 := by
  apply lucas_primality 61004131 (3 : ZMod 61004131)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 61004131 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((401 : ℕ)^1 * ((461 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 61004131)^30502065 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 61004131)^20334710 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 61004131)^12200826 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (3 : ZMod 61004131)^5545830 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 401 := Nat.prime_eq_prime_of_dvd_pow hq prime_401 hd
              subst q
              change (3 : ZMod 61004131)^152130 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 461 := Nat.prime_eq_prime_of_dvd_pow hq prime_461 hd
              subst q
              change (3 : ZMod 61004131)^132330 ≠ 1
              reduce_mod_char
              decide

theorem prime_62047043 : Nat.Prime 62047043 := by
  apply lucas_primality 62047043 (2 : ZMod 62047043)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 62047043 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((71 : ℕ)^1 * ((25703 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 62047043)^31023521 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 62047043)^3649826 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
          subst q
          change (2 : ZMod 62047043)^873902 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 25703 := Nat.prime_eq_prime_of_dvd_pow hq prime_25703 hd
          subst q
          change (2 : ZMod 62047043)^2414 ≠ 1
          reduce_mod_char
          decide

theorem prime_62187637 : Nat.Prime 62187637 := by
  apply lucas_primality 62187637 (5 : ZMod 62187637)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 62187637 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((740329 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 62187637)^31093818 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 62187637)^20729212 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 62187637)^8883948 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 740329 := Nat.prime_eq_prime_of_dvd_pow hq prime_740329 hd
          subst q
          change (5 : ZMod 62187637)^84 ≠ 1
          reduce_mod_char
          decide

theorem prime_62406073 : Nat.Prime 62406073 := by
  apply lucas_primality 62406073 (10 : ZMod 62406073)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 62406073 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((43 : ℕ)^1 * ((6719 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 62406073)^31203036 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 62406073)^20802024 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (10 : ZMod 62406073)^1451304 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 6719 := Nat.prime_eq_prime_of_dvd_pow hq prime_6719 hd
          subst q
          change (10 : ZMod 62406073)^9288 ≠ 1
          reduce_mod_char
          decide

theorem prime_63414217 : Nat.Prime 63414217 := by
  apply lucas_primality 63414217 (5 : ZMod 63414217)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 63414217 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((17 : ℕ)^1 * ((103 : ℕ)^1 * ((503 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 63414217)^31707108 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 63414217)^21138072 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (5 : ZMod 63414217)^3730248 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
            subst q
            change (5 : ZMod 63414217)^615672 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 503 := Nat.prime_eq_prime_of_dvd_pow hq prime_503 hd
            subst q
            change (5 : ZMod 63414217)^126072 ≠ 1
            reduce_mod_char
            decide

theorem prime_63665089 : Nat.Prime 63665089 := by
  apply lucas_primality 63665089 (7 : ZMod 63665089)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 63665089 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^1 * ((331589 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 63665089)^31832544 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 63665089)^21221696 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 331589 := Nat.prime_eq_prime_of_dvd_pow hq prime_331589 hd
        subst q
        change (7 : ZMod 63665089)^192 ≠ 1
        reduce_mod_char
        decide

theorem prime_63787949 : Nat.Prime 63787949 := by
  apply lucas_primality 63787949 (2 : ZMod 63787949)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 63787949 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((2278141 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 63787949)^31893974 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 63787949)^9112564 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2278141 := Nat.prime_eq_prime_of_dvd_pow hq prime_2278141 hd
        subst q
        change (2 : ZMod 63787949)^28 ≠ 1
        reduce_mod_char
        decide

theorem prime_63919469 : Nat.Prime 63919469 := by
  apply lucas_primality 63919469 (2 : ZMod 63919469)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 63919469 - 1 = (2 : ℕ)^2 * ((179 : ℕ)^1 * ((89273 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 63919469)^31959734 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 179 := Nat.prime_eq_prime_of_dvd_pow hq prime_179 hd
        subst q
        change (2 : ZMod 63919469)^357092 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 89273 := Nat.prime_eq_prime_of_dvd_pow hq prime_89273 hd
        subst q
        change (2 : ZMod 63919469)^716 ≠ 1
        reduce_mod_char
        decide

theorem prime_64000031 : Nat.Prime 64000031 := by
  apply lucas_primality 64000031 (7 : ZMod 64000031)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 64000031 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((23 : ℕ)^1 * ((278261 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 64000031)^32000015 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 64000031)^12800006 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (7 : ZMod 64000031)^2782610 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 278261 := Nat.prime_eq_prime_of_dvd_pow hq prime_278261 hd
          subst q
          change (7 : ZMod 64000031)^230 ≠ 1
          reduce_mod_char
          decide

theorem prime_67171591 : Nat.Prime 67171591 := by
  apply lucas_primality 67171591 (3 : ZMod 67171591)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 67171591 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((43 : ℕ)^1 * ((1021 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 67171591)^33585795 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 67171591)^22390530 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 67171591)^13434318 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (3 : ZMod 67171591)^3951270 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
              subst q
              change (3 : ZMod 67171591)^1562130 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1021 := Nat.prime_eq_prime_of_dvd_pow hq prime_1021 hd
              subst q
              change (3 : ZMod 67171591)^65790 ≠ 1
              reduce_mod_char
              decide

theorem prime_68281403 : Nat.Prime 68281403 := by
  apply lucas_primality 68281403 (2 : ZMod 68281403)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 68281403 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^2 * ((19 : ℕ)^1 * ((36671 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 68281403)^34140701 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 68281403)^9754486 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 68281403)^3593758 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 36671 := Nat.prime_eq_prime_of_dvd_pow hq prime_36671 hd
          subst q
          change (2 : ZMod 68281403)^1862 ≠ 1
          reduce_mod_char
          decide

theorem prime_68461451 : Nat.Prime 68461451 := by
  apply lucas_primality 68461451 (6 : ZMod 68461451)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 68461451 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((1369229 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 68461451)^34230725 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 68461451)^13692290 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1369229 := Nat.prime_eq_prime_of_dvd_pow hq prime_1369229 hd
        subst q
        change (6 : ZMod 68461451)^50 ≠ 1
        reduce_mod_char
        decide

theorem prime_68926811 : Nat.Prime 68926811 := by
  apply lucas_primality 68926811 (2 : ZMod 68926811)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 68926811 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((463 : ℕ)^1 * ((14887 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 68926811)^34463405 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 68926811)^13785362 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 463 := Nat.prime_eq_prime_of_dvd_pow hq prime_463 hd
          subst q
          change (2 : ZMod 68926811)^148870 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 14887 := Nat.prime_eq_prime_of_dvd_pow hq prime_14887 hd
          subst q
          change (2 : ZMod 68926811)^4630 ≠ 1
          reduce_mod_char
          decide

theorem prime_69056797 : Nat.Prime 69056797 := by
  apply lucas_primality 69056797 (2 : ZMod 69056797)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 69056797 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((43 : ℕ)^1 * ((133831 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 69056797)^34528398 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 69056797)^23018932 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (2 : ZMod 69056797)^1605972 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 133831 := Nat.prime_eq_prime_of_dvd_pow hq prime_133831 hd
          subst q
          change (2 : ZMod 69056797)^516 ≠ 1
          reduce_mod_char
          decide

theorem prime_69849079 : Nat.Prime 69849079 := by
  apply lucas_primality 69849079 (3 : ZMod 69849079)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 69849079 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((269 : ℕ)^1 * ((3329 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 69849079)^34924539 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 69849079)^23283026 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 69849079)^5373006 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
            subst q
            change (3 : ZMod 69849079)^259662 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3329 := Nat.prime_eq_prime_of_dvd_pow hq prime_3329 hd
            subst q
            change (3 : ZMod 69849079)^20982 ≠ 1
            reduce_mod_char
            decide

theorem prime_71159629 : Nat.Prime 71159629 := by
  apply lucas_primality 71159629 (2 : ZMod 71159629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 71159629 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((67 : ℕ)^2 * ((1321 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 71159629)^35579814 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 71159629)^23719876 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (2 : ZMod 71159629)^1062084 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1321 := Nat.prime_eq_prime_of_dvd_pow hq prime_1321 hd
          subst q
          change (2 : ZMod 71159629)^53868 ≠ 1
          reduce_mod_char
          decide

theorem prime_71298497 : Nat.Prime 71298497 := by
  apply lucas_primality 71298497 (3 : ZMod 71298497)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 71298497 - 1 = (2 : ℕ)^6 * ((1114039 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 71298497)^35649248 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1114039 := Nat.prime_eq_prime_of_dvd_pow hq prime_1114039 hd
      subst q
      change (3 : ZMod 71298497)^64 ≠ 1
      reduce_mod_char
      decide

theorem prime_71738473 : Nat.Prime 71738473 := by
  apply lucas_primality 71738473 (15 : ZMod 71738473)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 71738473 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((13 : ℕ)^2 * ((23 : ℕ)^1 * ((769 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (15 : ZMod 71738473)^35869236 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (15 : ZMod 71738473)^23912824 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (15 : ZMod 71738473)^5518344 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (15 : ZMod 71738473)^3119064 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 769 := Nat.prime_eq_prime_of_dvd_pow hq prime_769 hd
            subst q
            change (15 : ZMod 71738473)^93288 ≠ 1
            reduce_mod_char
            decide

theorem prime_71914109 : Nat.Prime 71914109 := by
  apply lucas_primality 71914109 (2 : ZMod 71914109)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 71914109 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((2568361 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 71914109)^35957054 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 71914109)^10273444 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2568361 := Nat.prime_eq_prime_of_dvd_pow hq prime_2568361 hd
        subst q
        change (2 : ZMod 71914109)^28 ≠ 1
        reduce_mod_char
        decide

theorem prime_72147043 : Nat.Prime 72147043 := by
  apply lucas_primality 72147043 (2 : ZMod 72147043)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 72147043 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((364379 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 72147043)^36073521 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 72147043)^24049014 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 72147043)^6558822 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 364379 := Nat.prime_eq_prime_of_dvd_pow hq prime_364379 hd
          subst q
          change (2 : ZMod 72147043)^198 ≠ 1
          reduce_mod_char
          decide

theorem prime_73029529 : Nat.Prime 73029529 := by
  apply lucas_primality 73029529 (14 : ZMod 73029529)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 73029529 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((41 : ℕ)^1 * ((173 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 73029529)^36514764 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 73029529)^24343176 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (14 : ZMod 73029529)^6639048 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (14 : ZMod 73029529)^5617656 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
              subst q
              change (14 : ZMod 73029529)^1781208 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
              subst q
              change (14 : ZMod 73029529)^422136 ≠ 1
              reduce_mod_char
              decide

theorem prime_74160467 : Nat.Prime 74160467 := by
  apply lucas_primality 74160467 (2 : ZMod 74160467)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 74160467 - 1 = (2 : ℕ)^1 * ((43 : ℕ)^1 * ((862331 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 74160467)^37080233 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
        subst q
        change (2 : ZMod 74160467)^1724662 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 862331 := Nat.prime_eq_prime_of_dvd_pow hq prime_862331 hd
        subst q
        change (2 : ZMod 74160467)^86 ≠ 1
        reduce_mod_char
        decide

theorem prime_74704891 : Nat.Prime 74704891 := by
  apply lucas_primality 74704891 (3 : ZMod 74704891)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 74704891 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((191551 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 74704891)^37352445 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 74704891)^24901630 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 74704891)^14940978 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (3 : ZMod 74704891)^5746530 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 191551 := Nat.prime_eq_prime_of_dvd_pow hq prime_191551 hd
            subst q
            change (3 : ZMod 74704891)^390 ≠ 1
            reduce_mod_char
            decide

theorem prime_74989597 : Nat.Prime 74989597 := by
  apply lucas_primality 74989597 (2 : ZMod 74989597)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 74989597 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((239 : ℕ)^1 * ((2377 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 74989597)^37494798 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 74989597)^24996532 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 74989597)^6817236 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 239 := Nat.prime_eq_prime_of_dvd_pow hq prime_239 hd
            subst q
            change (2 : ZMod 74989597)^313764 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2377 := Nat.prime_eq_prime_of_dvd_pow hq prime_2377 hd
            subst q
            change (2 : ZMod 74989597)^31548 ≠ 1
            reduce_mod_char
            decide

theorem prime_75284383 : Nat.Prime 75284383 := by
  apply lucas_primality 75284383 (3 : ZMod 75284383)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 75284383 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((307 : ℕ)^1 * ((1777 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 75284383)^37642191 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 75284383)^25094794 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (3 : ZMod 75284383)^3273234 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 307 := Nat.prime_eq_prime_of_dvd_pow hq prime_307 hd
            subst q
            change (3 : ZMod 75284383)^245226 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1777 := Nat.prime_eq_prime_of_dvd_pow hq prime_1777 hd
            subst q
            change (3 : ZMod 75284383)^42366 ≠ 1
            reduce_mod_char
            decide

theorem prime_76199869 : Nat.Prime 76199869 := by
  apply lucas_primality 76199869 (2 : ZMod 76199869)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 76199869 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((2116663 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 76199869)^38099934 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 76199869)^25399956 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2116663 := Nat.prime_eq_prime_of_dvd_pow hq prime_2116663 hd
        subst q
        change (2 : ZMod 76199869)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_76844681 : Nat.Prime 76844681 := by
  apply lucas_primality 76844681 (6 : ZMod 76844681)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 76844681 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((11 : ℕ)^2 * ((15877 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 76844681)^38422340 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 76844681)^15368936 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (6 : ZMod 76844681)^6985880 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 15877 := Nat.prime_eq_prime_of_dvd_pow hq prime_15877 hd
          subst q
          change (6 : ZMod 76844681)^4840 ≠ 1
          reduce_mod_char
          decide

theorem prime_77295223 : Nat.Prime 77295223 := by
  apply lucas_primality 77295223 (3 : ZMod 77295223)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 77295223 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((477131 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 77295223)^38647611 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 77295223)^25765074 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 477131 := Nat.prime_eq_prime_of_dvd_pow hq prime_477131 hd
        subst q
        change (3 : ZMod 77295223)^162 ≠ 1
        reduce_mod_char
        decide

theorem prime_79353317 : Nat.Prime 79353317 := by
  apply lucas_primality 79353317 (2 : ZMod 79353317)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 79353317 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((2834047 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 79353317)^39676658 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 79353317)^11336188 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2834047 := Nat.prime_eq_prime_of_dvd_pow hq prime_2834047 hd
        subst q
        change (2 : ZMod 79353317)^28 ≠ 1
        reduce_mod_char
        decide

theorem prime_79481917 : Nat.Prime 79481917 := by
  apply lucas_primality 79481917 (13 : ZMod 79481917)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 79481917 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((2207831 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 79481917)^39740958 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 79481917)^26493972 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2207831 := Nat.prime_eq_prime_of_dvd_pow hq prime_2207831 hd
        subst q
        change (13 : ZMod 79481917)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_80111113 : Nat.Prime 80111113 := by
  apply lucas_primality 80111113 (5 : ZMod 80111113)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 80111113 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((311 : ℕ)^1 * ((10733 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 80111113)^40055556 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 80111113)^26703704 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 311 := Nat.prime_eq_prime_of_dvd_pow hq prime_311 hd
          subst q
          change (5 : ZMod 80111113)^257592 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 10733 := Nat.prime_eq_prime_of_dvd_pow hq prime_10733 hd
          subst q
          change (5 : ZMod 80111113)^7464 ≠ 1
          reduce_mod_char
          decide

theorem prime_80315051 : Nat.Prime 80315051 := by
  apply lucas_primality 80315051 (6 : ZMod 80315051)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 80315051 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((439 : ℕ)^1 * ((3659 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 80315051)^40157525 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 80315051)^16063010 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 439 := Nat.prime_eq_prime_of_dvd_pow hq prime_439 hd
          subst q
          change (6 : ZMod 80315051)^182950 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3659 := Nat.prime_eq_prime_of_dvd_pow hq prime_3659 hd
          subst q
          change (6 : ZMod 80315051)^21950 ≠ 1
          reduce_mod_char
          decide

theorem prime_83918299 : Nat.Prime 83918299 := by
  apply lucas_primality 83918299 (3 : ZMod 83918299)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 83918299 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((127 : ℕ)^1 * ((110129 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 83918299)^41959149 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 83918299)^27972766 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
          subst q
          change (3 : ZMod 83918299)^660774 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 110129 := Nat.prime_eq_prime_of_dvd_pow hq prime_110129 hd
          subst q
          change (3 : ZMod 83918299)^762 ≠ 1
          reduce_mod_char
          decide

theorem prime_84336433 : Nat.Prime 84336433 := by
  apply lucas_primality 84336433 (7 : ZMod 84336433)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 84336433 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((191 : ℕ)^1 * ((9199 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 84336433)^42168216 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 84336433)^28112144 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
          subst q
          change (7 : ZMod 84336433)^441552 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 9199 := Nat.prime_eq_prime_of_dvd_pow hq prime_9199 hd
          subst q
          change (7 : ZMod 84336433)^9168 ≠ 1
          reduce_mod_char
          decide

end LegendreK6.Pratt
