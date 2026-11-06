import LegendreK6.Pratt.Block007

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LegendreK6.Pratt

theorem prime_83497 : Nat.Prime 83497 := by
  apply lucas_primality 83497 (10 : ZMod 83497)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 83497 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((71 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 83497)^41748 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 83497)^27832 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (10 : ZMod 83497)^11928 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
          subst q
          change (10 : ZMod 83497)^1176 ≠ 1
          reduce_mod_char
          decide

theorem prime_84017 : Nat.Prime 84017 := by
  apply lucas_primality 84017 (3 : ZMod 84017)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 84017 - 1 = (2 : ℕ)^4 * ((59 : ℕ)^1 * ((89 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 84017)^42008 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
        subst q
        change (3 : ZMod 84017)^1424 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
        subst q
        change (3 : ZMod 84017)^944 ≠ 1
        reduce_mod_char
        decide

theorem prime_84061 : Nat.Prime 84061 := by
  apply lucas_primality 84061 (7 : ZMod 84061)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 84061 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((467 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 84061)^42030 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 84061)^28020 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 84061)^16812 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 467 := Nat.prime_eq_prime_of_dvd_pow hq prime_467 hd
          subst q
          change (7 : ZMod 84061)^180 ≠ 1
          reduce_mod_char
          decide

theorem prime_84347 : Nat.Prime 84347 := by
  apply lucas_primality 84347 (2 : ZMod 84347)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 84347 - 1 = (2 : ℕ)^1 * ((181 : ℕ)^1 * ((233 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 84347)^42173 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 181 := Nat.prime_eq_prime_of_dvd_pow hq prime_181 hd
        subst q
        change (2 : ZMod 84347)^466 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
        subst q
        change (2 : ZMod 84347)^362 ≠ 1
        reduce_mod_char
        decide

theorem prime_85147 : Nat.Prime 85147 := by
  apply lucas_primality 85147 (2 : ZMod 85147)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 85147 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((617 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 85147)^42573 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 85147)^28382 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 85147)^3702 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 617 := Nat.prime_eq_prime_of_dvd_pow hq prime_617 hd
          subst q
          change (2 : ZMod 85147)^138 ≠ 1
          reduce_mod_char
          decide

theorem prime_85453 : Nat.Prime 85453 := by
  apply lucas_primality 85453 (2 : ZMod 85453)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 85453 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7121 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 85453)^42726 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 85453)^28484 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7121 := Nat.prime_eq_prime_of_dvd_pow hq prime_7121 hd
        subst q
        change (2 : ZMod 85453)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_85717 : Nat.Prime 85717 := by
  apply lucas_primality 85717 (2 : ZMod 85717)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 85717 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((2381 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 85717)^42858 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 85717)^28572 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2381 := Nat.prime_eq_prime_of_dvd_pow hq prime_2381 hd
        subst q
        change (2 : ZMod 85717)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_85733 : Nat.Prime 85733 := by
  apply lucas_primality 85733 (2 : ZMod 85733)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 85733 - 1 = (2 : ℕ)^2 * ((21433 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 85733)^42866 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 21433 := Nat.prime_eq_prime_of_dvd_pow hq prime_21433 hd
      subst q
      change (2 : ZMod 85733)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_86017 : Nat.Prime 86017 := by
  apply lucas_primality 86017 (5 : ZMod 86017)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 86017 - 1 = (2 : ℕ)^12 * ((3 : ℕ)^1 * ((7 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 86017)^43008 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 86017)^28672 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 86017)^12288 ≠ 1
        reduce_mod_char
        decide

theorem prime_86171 : Nat.Prime 86171 := by
  apply lucas_primality 86171 (7 : ZMod 86171)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 86171 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((1231 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 86171)^43085 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 86171)^17234 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 86171)^12310 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1231 := Nat.prime_eq_prime_of_dvd_pow hq prime_1231 hd
          subst q
          change (7 : ZMod 86171)^70 ≠ 1
          reduce_mod_char
          decide

theorem prime_86311 : Nat.Prime 86311 := by
  apply lucas_primality 86311 (3 : ZMod 86311)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 86311 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((137 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 86311)^43155 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 86311)^28770 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 86311)^17262 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (3 : ZMod 86311)^12330 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
            subst q
            change (3 : ZMod 86311)^630 ≠ 1
            reduce_mod_char
            decide

theorem prime_86441 : Nat.Prime 86441 := by
  apply lucas_primality 86441 (3 : ZMod 86441)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 86441 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((2161 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 86441)^43220 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 86441)^17288 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2161 := Nat.prime_eq_prime_of_dvd_pow hq prime_2161 hd
        subst q
        change (3 : ZMod 86441)^40 ≠ 1
        reduce_mod_char
        decide

theorem prime_86599 : Nat.Prime 86599 := by
  apply lucas_primality 86599 (3 : ZMod 86599)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 86599 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((17 : ℕ)^1 * ((283 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 86599)^43299 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 86599)^28866 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (3 : ZMod 86599)^5094 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 283 := Nat.prime_eq_prime_of_dvd_pow hq prime_283 hd
          subst q
          change (3 : ZMod 86599)^306 ≠ 1
          reduce_mod_char
          decide

theorem prime_86689 : Nat.Prime 86689 := by
  apply lucas_primality 86689 (13 : ZMod 86689)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 86689 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((43 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 86689)^43344 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 86689)^28896 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (13 : ZMod 86689)^12384 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (13 : ZMod 86689)^2016 ≠ 1
          reduce_mod_char
          decide

theorem prime_87103 : Nat.Prime 87103 := by
  apply lucas_primality 87103 (3 : ZMod 87103)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 87103 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((1613 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 87103)^43551 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 87103)^29034 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1613 := Nat.prime_eq_prime_of_dvd_pow hq prime_1613 hd
        subst q
        change (3 : ZMod 87103)^54 ≠ 1
        reduce_mod_char
        decide

theorem prime_87421 : Nat.Prime 87421 := by
  apply lucas_primality 87421 (6 : ZMod 87421)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 87421 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((31 : ℕ)^1 * ((47 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 87421)^43710 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 87421)^29140 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 87421)^17484 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (6 : ZMod 87421)^2820 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
            subst q
            change (6 : ZMod 87421)^1860 ≠ 1
            reduce_mod_char
            decide

theorem prime_87433 : Nat.Prime 87433 := by
  apply lucas_primality 87433 (5 : ZMod 87433)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 87433 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((3643 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 87433)^43716 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 87433)^29144 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3643 := Nat.prime_eq_prime_of_dvd_pow hq prime_3643 hd
        subst q
        change (5 : ZMod 87433)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_87559 : Nat.Prime 87559 := by
  apply lucas_primality 87559 (3 : ZMod 87559)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 87559 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((14593 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 87559)^43779 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 87559)^29186 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 14593 := Nat.prime_eq_prime_of_dvd_pow hq prime_14593 hd
        subst q
        change (3 : ZMod 87559)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_88223 : Nat.Prime 88223 := by
  apply lucas_primality 88223 (5 : ZMod 88223)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 88223 - 1 = (2 : ℕ)^1 * ((44111 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 88223)^44111 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 44111 := Nat.prime_eq_prime_of_dvd_pow hq prime_44111 hd
      subst q
      change (5 : ZMod 88223)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_88651 : Nat.Prime 88651 := by
  apply lucas_primality 88651 (3 : ZMod 88651)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 88651 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^2 * ((197 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 88651)^44325 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 88651)^29550 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 88651)^17730 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
          subst q
          change (3 : ZMod 88651)^450 ≠ 1
          reduce_mod_char
          decide

theorem prime_88817 : Nat.Prime 88817 := by
  apply lucas_primality 88817 (3 : ZMod 88817)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 88817 - 1 = (2 : ℕ)^4 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((61 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 88817)^44408 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 88817)^12688 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 88817)^6832 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (3 : ZMod 88817)^1456 ≠ 1
          reduce_mod_char
          decide

theorem prime_89071 : Nat.Prime 89071 := by
  apply lucas_primality 89071 (6 : ZMod 89071)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 89071 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((2969 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 89071)^44535 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 89071)^29690 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 89071)^17814 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2969 := Nat.prime_eq_prime_of_dvd_pow hq prime_2969 hd
          subst q
          change (6 : ZMod 89071)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_89107 : Nat.Prime 89107 := by
  apply lucas_primality 89107 (2 : ZMod 89107)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 89107 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((14851 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 89107)^44553 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 89107)^29702 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 14851 := Nat.prime_eq_prime_of_dvd_pow hq prime_14851 hd
        subst q
        change (2 : ZMod 89107)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_89269 : Nat.Prime 89269 := by
  apply lucas_primality 89269 (2 : ZMod 89269)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 89269 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((43 : ℕ)^1 * ((173 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 89269)^44634 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 89269)^29756 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (2 : ZMod 89269)^2076 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
          subst q
          change (2 : ZMod 89269)^516 ≠ 1
          reduce_mod_char
          decide

theorem prime_89273 : Nat.Prime 89273 := by
  apply lucas_primality 89273 (3 : ZMod 89273)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 89273 - 1 = (2 : ℕ)^3 * ((11159 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 89273)^44636 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 11159 := Nat.prime_eq_prime_of_dvd_pow hq prime_11159 hd
      subst q
      change (3 : ZMod 89273)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_89891 : Nat.Prime 89891 := by
  apply lucas_primality 89891 (7 : ZMod 89891)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 89891 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((89 : ℕ)^1 * ((101 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 89891)^44945 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 89891)^17978 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (7 : ZMod 89891)^1010 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
          subst q
          change (7 : ZMod 89891)^890 ≠ 1
          reduce_mod_char
          decide

theorem prime_89909 : Nat.Prime 89909 := by
  apply lucas_primality 89909 (2 : ZMod 89909)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 89909 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((13 : ℕ)^2 * ((19 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 89909)^44954 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 89909)^12844 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 89909)^6916 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 89909)^4732 ≠ 1
          reduce_mod_char
          decide

theorem prime_89923 : Nat.Prime 89923 := by
  apply lucas_primality 89923 (3 : ZMod 89923)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 89923 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((2141 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 89923)^44961 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 89923)^29974 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 89923)^12846 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2141 := Nat.prime_eq_prime_of_dvd_pow hq prime_2141 hd
          subst q
          change (3 : ZMod 89923)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_90197 : Nat.Prime 90197 := by
  apply lucas_primality 90197 (2 : ZMod 90197)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 90197 - 1 = (2 : ℕ)^2 * ((22549 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 90197)^45098 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 22549 := Nat.prime_eq_prime_of_dvd_pow hq prime_22549 hd
      subst q
      change (2 : ZMod 90197)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_91141 : Nat.Prime 91141 := by
  apply lucas_primality 91141 (6 : ZMod 91141)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 91141 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^2 * ((31 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 91141)^45570 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 91141)^30380 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 91141)^18228 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (6 : ZMod 91141)^13020 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (6 : ZMod 91141)^2940 ≠ 1
            reduce_mod_char
            decide

theorem prime_91163 : Nat.Prime 91163 := by
  apply lucas_primality 91163 (2 : ZMod 91163)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 91163 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((2399 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 91163)^45581 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 91163)^4798 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2399 := Nat.prime_eq_prime_of_dvd_pow hq prime_2399 hd
        subst q
        change (2 : ZMod 91163)^38 ≠ 1
        reduce_mod_char
        decide

theorem prime_91193 : Nat.Prime 91193 := by
  apply lucas_primality 91193 (3 : ZMod 91193)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 91193 - 1 = (2 : ℕ)^3 * ((11399 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 91193)^45596 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 11399 := Nat.prime_eq_prime_of_dvd_pow hq prime_11399 hd
      subst q
      change (3 : ZMod 91193)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_91591 : Nat.Prime 91591 := by
  apply lucas_primality 91591 (3 : ZMod 91591)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 91591 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((43 : ℕ)^1 * ((71 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 91591)^45795 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 91591)^30530 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 91591)^18318 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (3 : ZMod 91591)^2130 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
            subst q
            change (3 : ZMod 91591)^1290 ≠ 1
            reduce_mod_char
            decide

theorem prime_91813 : Nat.Prime 91813 := by
  apply lucas_primality 91813 (2 : ZMod 91813)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 91813 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((1093 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 91813)^45906 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 91813)^30604 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 91813)^13116 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1093 := Nat.prime_eq_prime_of_dvd_pow hq prime_1093 hd
          subst q
          change (2 : ZMod 91813)^84 ≠ 1
          reduce_mod_char
          decide

theorem prime_91909 : Nat.Prime 91909 := by
  apply lucas_primality 91909 (2 : ZMod 91909)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 91909 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((23 : ℕ)^1 * ((37 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 91909)^45954 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 91909)^30636 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 91909)^3996 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (2 : ZMod 91909)^2484 ≠ 1
          reduce_mod_char
          decide

theorem prime_91943 : Nat.Prime 91943 := by
  apply lucas_primality 91943 (5 : ZMod 91943)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 91943 - 1 = (2 : ℕ)^1 * ((45971 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 91943)^45971 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 45971 := Nat.prime_eq_prime_of_dvd_pow hq prime_45971 hd
      subst q
      change (5 : ZMod 91943)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_92791 : Nat.Prime 92791 := by
  apply lucas_primality 92791 (6 : ZMod 92791)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 92791 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((1031 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 92791)^46395 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 92791)^30930 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 92791)^18558 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1031 := Nat.prime_eq_prime_of_dvd_pow hq prime_1031 hd
          subst q
          change (6 : ZMod 92791)^90 ≠ 1
          reduce_mod_char
          decide

theorem prime_93083 : Nat.Prime 93083 := by
  apply lucas_primality 93083 (2 : ZMod 93083)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 93083 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((4231 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 93083)^46541 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 93083)^8462 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4231 := Nat.prime_eq_prime_of_dvd_pow hq prime_4231 hd
        subst q
        change (2 : ZMod 93083)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_94049 : Nat.Prime 94049 := by
  apply lucas_primality 94049 (3 : ZMod 94049)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 94049 - 1 = (2 : ℕ)^5 * ((2939 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 94049)^47024 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 2939 := Nat.prime_eq_prime_of_dvd_pow hq prime_2939 hd
      subst q
      change (3 : ZMod 94049)^32 ≠ 1
      reduce_mod_char
      decide

theorem prime_94099 : Nat.Prime 94099 := by
  apply lucas_primality 94099 (2 : ZMod 94099)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 94099 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((15683 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 94099)^47049 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 94099)^31366 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 15683 := Nat.prime_eq_prime_of_dvd_pow hq prime_15683 hd
        subst q
        change (2 : ZMod 94099)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_94151 : Nat.Prime 94151 := by
  apply lucas_primality 94151 (7 : ZMod 94151)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 94151 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((7 : ℕ)^1 * ((269 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 94151)^47075 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 94151)^18830 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 94151)^13450 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
          subst q
          change (7 : ZMod 94151)^350 ≠ 1
          reduce_mod_char
          decide

theorem prime_94873 : Nat.Prime 94873 := by
  apply lucas_primality 94873 (5 : ZMod 94873)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 94873 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((59 : ℕ)^1 * ((67 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 94873)^47436 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 94873)^31624 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (5 : ZMod 94873)^1608 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (5 : ZMod 94873)^1416 ≠ 1
          reduce_mod_char
          decide

theorem prime_95027 : Nat.Prime 95027 := by
  apply lucas_primality 95027 (2 : ZMod 95027)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 95027 - 1 = (2 : ℕ)^1 * ((47513 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 95027)^47513 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 47513 := Nat.prime_eq_prime_of_dvd_pow hq prime_47513 hd
      subst q
      change (2 : ZMod 95027)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_95891 : Nat.Prime 95891 := by
  apply lucas_primality 95891 (2 : ZMod 95891)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 95891 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((43 : ℕ)^1 * ((223 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 95891)^47945 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 95891)^19178 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (2 : ZMod 95891)^2230 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 223 := Nat.prime_eq_prime_of_dvd_pow hq prime_223 hd
          subst q
          change (2 : ZMod 95891)^430 ≠ 1
          reduce_mod_char
          decide

theorem prime_95959 : Nat.Prime 95959 := by
  apply lucas_primality 95959 (3 : ZMod 95959)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 95959 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((1777 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 95959)^47979 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 95959)^31986 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1777 := Nat.prime_eq_prime_of_dvd_pow hq prime_1777 hd
        subst q
        change (3 : ZMod 95959)^54 ≠ 1
        reduce_mod_char
        decide

theorem prime_96179 : Nat.Prime 96179 := by
  apply lucas_primality 96179 (2 : ZMod 96179)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 96179 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((2531 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 96179)^48089 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 96179)^5062 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2531 := Nat.prime_eq_prime_of_dvd_pow hq prime_2531 hd
        subst q
        change (2 : ZMod 96179)^38 ≠ 1
        reduce_mod_char
        decide

theorem prime_96323 : Nat.Prime 96323 := by
  apply lucas_primality 96323 (2 : ZMod 96323)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 96323 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((2833 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 96323)^48161 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 96323)^5666 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2833 := Nat.prime_eq_prime_of_dvd_pow hq prime_2833 hd
        subst q
        change (2 : ZMod 96323)^34 ≠ 1
        reduce_mod_char
        decide

theorem prime_96661 : Nat.Prime 96661 := by
  apply lucas_primality 96661 (7 : ZMod 96661)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 96661 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((179 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 96661)^48330 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 96661)^32220 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 96661)^19332 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 179 := Nat.prime_eq_prime_of_dvd_pow hq prime_179 hd
          subst q
          change (7 : ZMod 96661)^540 ≠ 1
          reduce_mod_char
          decide

theorem prime_96851 : Nat.Prime 96851 := by
  apply lucas_primality 96851 (2 : ZMod 96851)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 96851 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((13 : ℕ)^1 * ((149 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 96851)^48425 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 96851)^19370 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 96851)^7450 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
          subst q
          change (2 : ZMod 96851)^650 ≠ 1
          reduce_mod_char
          decide

theorem prime_96907 : Nat.Prime 96907 := by
  apply lucas_primality 96907 (2 : ZMod 96907)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 96907 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((31 : ℕ)^1 * ((521 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 96907)^48453 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 96907)^32302 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (2 : ZMod 96907)^3126 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 521 := Nat.prime_eq_prime_of_dvd_pow hq prime_521 hd
          subst q
          change (2 : ZMod 96907)^186 ≠ 1
          reduce_mod_char
          decide

theorem prime_97127 : Nat.Prime 97127 := by
  apply lucas_primality 97127 (5 : ZMod 97127)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 97127 - 1 = (2 : ℕ)^1 * ((48563 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 97127)^48563 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 48563 := Nat.prime_eq_prime_of_dvd_pow hq prime_48563 hd
      subst q
      change (5 : ZMod 97127)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_98009 : Nat.Prime 98009 := by
  apply lucas_primality 98009 (3 : ZMod 98009)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 98009 - 1 = (2 : ℕ)^3 * ((12251 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 98009)^49004 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 12251 := Nat.prime_eq_prime_of_dvd_pow hq prime_12251 hd
      subst q
      change (3 : ZMod 98009)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_98429 : Nat.Prime 98429 := by
  apply lucas_primality 98429 (2 : ZMod 98429)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 98429 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((2237 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 98429)^49214 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 98429)^8948 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2237 := Nat.prime_eq_prime_of_dvd_pow hq prime_2237 hd
        subst q
        change (2 : ZMod 98429)^44 ≠ 1
        reduce_mod_char
        decide

theorem prime_98519 : Nat.Prime 98519 := by
  apply lucas_primality 98519 (7 : ZMod 98519)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 98519 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((31 : ℕ)^1 * ((227 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 98519)^49259 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 98519)^14074 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (7 : ZMod 98519)^3178 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 227 := Nat.prime_eq_prime_of_dvd_pow hq prime_227 hd
          subst q
          change (7 : ZMod 98519)^434 ≠ 1
          reduce_mod_char
          decide

theorem prime_98717 : Nat.Prime 98717 := by
  apply lucas_primality 98717 (2 : ZMod 98717)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 98717 - 1 = (2 : ℕ)^2 * ((23 : ℕ)^1 * ((29 : ℕ)^1 * ((37 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 98717)^49358 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (2 : ZMod 98717)^4292 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (2 : ZMod 98717)^3404 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (2 : ZMod 98717)^2668 ≠ 1
          reduce_mod_char
          decide

theorem prime_98929 : Nat.Prime 98929 := by
  apply lucas_primality 98929 (11 : ZMod 98929)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 98929 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^3 * ((229 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 98929)^49464 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 98929)^32976 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 229 := Nat.prime_eq_prime_of_dvd_pow hq prime_229 hd
        subst q
        change (11 : ZMod 98929)^432 ≠ 1
        reduce_mod_char
        decide

theorem prime_99529 : Nat.Prime 99529 := by
  apply lucas_primality 99529 (7 : ZMod 99529)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 99529 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((29 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 99529)^49764 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 99529)^33176 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (7 : ZMod 99529)^9048 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (7 : ZMod 99529)^7656 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (7 : ZMod 99529)^3432 ≠ 1
            reduce_mod_char
            decide

theorem prime_100057 : Nat.Prime 100057 := by
  apply lucas_primality 100057 (10 : ZMod 100057)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 100057 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((379 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 100057)^50028 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 100057)^33352 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (10 : ZMod 100057)^9096 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 379 := Nat.prime_eq_prime_of_dvd_pow hq prime_379 hd
          subst q
          change (10 : ZMod 100057)^264 ≠ 1
          reduce_mod_char
          decide

theorem prime_100069 : Nat.Prime 100069 := by
  apply lucas_primality 100069 (10 : ZMod 100069)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 100069 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((31 : ℕ)^1 * ((269 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 100069)^50034 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 100069)^33356 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (10 : ZMod 100069)^3228 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
          subst q
          change (10 : ZMod 100069)^372 ≠ 1
          reduce_mod_char
          decide

theorem prime_100271 : Nat.Prime 100271 := by
  apply lucas_primality 100271 (13 : ZMod 100271)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 100271 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((37 : ℕ)^1 * ((271 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 100271)^50135 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (13 : ZMod 100271)^20054 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (13 : ZMod 100271)^2710 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 271 := Nat.prime_eq_prime_of_dvd_pow hq prime_271 hd
          subst q
          change (13 : ZMod 100271)^370 ≠ 1
          reduce_mod_char
          decide

theorem prime_100609 : Nat.Prime 100609 := by
  apply lucas_primality 100609 (7 : ZMod 100609)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 100609 - 1 = (2 : ℕ)^8 * ((3 : ℕ)^1 * ((131 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 100609)^50304 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 100609)^33536 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
        subst q
        change (7 : ZMod 100609)^768 ≠ 1
        reduce_mod_char
        decide

theorem prime_100669 : Nat.Prime 100669 := by
  apply lucas_primality 100669 (6 : ZMod 100669)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 100669 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((8389 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 100669)^50334 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 100669)^33556 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 8389 := Nat.prime_eq_prime_of_dvd_pow hq prime_8389 hd
        subst q
        change (6 : ZMod 100669)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_100907 : Nat.Prime 100907 := by
  apply lucas_primality 100907 (2 : ZMod 100907)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 100907 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((3881 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 100907)^50453 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 100907)^7762 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3881 := Nat.prime_eq_prime_of_dvd_pow hq prime_3881 hd
        subst q
        change (2 : ZMod 100907)^26 ≠ 1
        reduce_mod_char
        decide

theorem prime_100957 : Nat.Prime 100957 := by
  apply lucas_primality 100957 (2 : ZMod 100957)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 100957 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((47 : ℕ)^1 * ((179 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 100957)^50478 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 100957)^33652 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (2 : ZMod 100957)^2148 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 179 := Nat.prime_eq_prime_of_dvd_pow hq prime_179 hd
          subst q
          change (2 : ZMod 100957)^564 ≠ 1
          reduce_mod_char
          decide

theorem prime_101113 : Nat.Prime 101113 := by
  apply lucas_primality 101113 (5 : ZMod 101113)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 101113 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((383 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 101113)^50556 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 101113)^33704 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 101113)^9192 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 383 := Nat.prime_eq_prime_of_dvd_pow hq prime_383 hd
          subst q
          change (5 : ZMod 101113)^264 ≠ 1
          reduce_mod_char
          decide

theorem prime_101527 : Nat.Prime 101527 := by
  apply lucas_primality 101527 (5 : ZMod 101527)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 101527 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((16921 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 101527)^50763 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 101527)^33842 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 16921 := Nat.prime_eq_prime_of_dvd_pow hq prime_16921 hd
        subst q
        change (5 : ZMod 101527)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_101641 : Nat.Prime 101641 := by
  apply lucas_primality 101641 (13 : ZMod 101641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 101641 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^2)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 101641)^50820 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 101641)^33880 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 101641)^20328 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (13 : ZMod 101641)^14520 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (13 : ZMod 101641)^9240 ≠ 1
            reduce_mod_char
            decide

theorem prime_101681 : Nat.Prime 101681 := by
  apply lucas_primality 101681 (6 : ZMod 101681)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 101681 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((31 : ℕ)^1 * ((41 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 101681)^50840 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 101681)^20336 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (6 : ZMod 101681)^3280 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (6 : ZMod 101681)^2480 ≠ 1
          reduce_mod_char
          decide

theorem prime_101929 : Nat.Prime 101929 := by
  apply lucas_primality 101929 (17 : ZMod 101929)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 101929 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((31 : ℕ)^1 * ((137 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 101929)^50964 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 101929)^33976 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (17 : ZMod 101929)^3288 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
          subst q
          change (17 : ZMod 101929)^744 ≠ 1
          reduce_mod_char
          decide

theorem prime_102013 : Nat.Prime 102013 := by
  apply lucas_primality 102013 (5 : ZMod 102013)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 102013 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((8501 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 102013)^51006 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 102013)^34004 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 8501 := Nat.prime_eq_prime_of_dvd_pow hq prime_8501 hd
        subst q
        change (5 : ZMod 102013)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_102121 : Nat.Prime 102121 := by
  apply lucas_primality 102121 (7 : ZMod 102121)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 102121 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((23 : ℕ)^1 * ((37 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 102121)^51060 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 102121)^34040 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 102121)^20424 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (7 : ZMod 102121)^4440 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
            subst q
            change (7 : ZMod 102121)^2760 ≠ 1
            reduce_mod_char
            decide

theorem prime_102251 : Nat.Prime 102251 := by
  apply lucas_primality 102251 (2 : ZMod 102251)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 102251 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^3 * ((409 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 102251)^51125 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 102251)^20450 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 409 := Nat.prime_eq_prime_of_dvd_pow hq prime_409 hd
        subst q
        change (2 : ZMod 102251)^250 ≠ 1
        reduce_mod_char
        decide

theorem prime_102607 : Nat.Prime 102607 := by
  apply lucas_primality 102607 (5 : ZMod 102607)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 102607 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((349 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 102607)^51303 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 102607)^34202 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 102607)^14658 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 349 := Nat.prime_eq_prime_of_dvd_pow hq prime_349 hd
          subst q
          change (5 : ZMod 102607)^294 ≠ 1
          reduce_mod_char
          decide

theorem prime_102643 : Nat.Prime 102643 := by
  apply lucas_primality 102643 (7 : ZMod 102643)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 102643 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17107 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 102643)^51321 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 102643)^34214 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 17107 := Nat.prime_eq_prime_of_dvd_pow hq prime_17107 hd
        subst q
        change (7 : ZMod 102643)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_102653 : Nat.Prime 102653 := by
  apply lucas_primality 102653 (2 : ZMod 102653)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 102653 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((2333 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 102653)^51326 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 102653)^9332 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2333 := Nat.prime_eq_prime_of_dvd_pow hq prime_2333 hd
        subst q
        change (2 : ZMod 102653)^44 ≠ 1
        reduce_mod_char
        decide

theorem prime_103619 : Nat.Prime 103619 := by
  apply lucas_primality 103619 (2 : ZMod 103619)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 103619 - 1 = (2 : ℕ)^1 * ((103 : ℕ)^1 * ((503 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 103619)^51809 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
        subst q
        change (2 : ZMod 103619)^1006 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 503 := Nat.prime_eq_prime_of_dvd_pow hq prime_503 hd
        subst q
        change (2 : ZMod 103619)^206 ≠ 1
        reduce_mod_char
        decide

theorem prime_104089 : Nat.Prime 104089 := by
  apply lucas_primality 104089 (7 : ZMod 104089)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 104089 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((4337 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 104089)^52044 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 104089)^34696 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4337 := Nat.prime_eq_prime_of_dvd_pow hq prime_4337 hd
        subst q
        change (7 : ZMod 104089)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_104107 : Nat.Prime 104107 := by
  apply lucas_primality 104107 (5 : ZMod 104107)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 104107 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17351 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 104107)^52053 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 104107)^34702 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 17351 := Nat.prime_eq_prime_of_dvd_pow hq prime_17351 hd
        subst q
        change (5 : ZMod 104107)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_104231 : Nat.Prime 104231 := by
  apply lucas_primality 104231 (7 : ZMod 104231)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 104231 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((1489 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 104231)^52115 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 104231)^20846 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 104231)^14890 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1489 := Nat.prime_eq_prime_of_dvd_pow hq prime_1489 hd
          subst q
          change (7 : ZMod 104231)^70 ≠ 1
          reduce_mod_char
          decide

theorem prime_104347 : Nat.Prime 104347 := by
  apply lucas_primality 104347 (11 : ZMod 104347)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 104347 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((31 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 104347)^52173 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 104347)^34782 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (11 : ZMod 104347)^9486 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (11 : ZMod 104347)^6138 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (11 : ZMod 104347)^3366 ≠ 1
            reduce_mod_char
            decide

theorem prime_104659 : Nat.Prime 104659 := by
  apply lucas_primality 104659 (2 : ZMod 104659)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 104659 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17443 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 104659)^52329 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 104659)^34886 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 17443 := Nat.prime_eq_prime_of_dvd_pow hq prime_17443 hd
        subst q
        change (2 : ZMod 104659)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_104723 : Nat.Prime 104723 := by
  apply lucas_primality 104723 (2 : ZMod 104723)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 104723 - 1 = (2 : ℕ)^1 * ((52361 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 104723)^52361 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 52361 := Nat.prime_eq_prime_of_dvd_pow hq prime_52361 hd
      subst q
      change (2 : ZMod 104723)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_104743 : Nat.Prime 104743 := by
  apply lucas_primality 104743 (3 : ZMod 104743)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 104743 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((23 : ℕ)^2))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 104743)^52371 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 104743)^34914 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 104743)^9522 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (3 : ZMod 104743)^4554 ≠ 1
          reduce_mod_char
          decide

theorem prime_104851 : Nat.Prime 104851 := by
  apply lucas_primality 104851 (13 : ZMod 104851)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 104851 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^2 * ((233 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 104851)^52425 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 104851)^34950 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 104851)^20970 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
          subst q
          change (13 : ZMod 104851)^450 ≠ 1
          reduce_mod_char
          decide

theorem prime_105733 : Nat.Prime 105733 := by
  apply lucas_primality 105733 (6 : ZMod 105733)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 105733 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((11 : ℕ)^1 * ((89 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 105733)^52866 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 105733)^35244 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (6 : ZMod 105733)^9612 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (6 : ZMod 105733)^1188 ≠ 1
          reduce_mod_char
          decide

theorem prime_106123 : Nat.Prime 106123 := by
  apply lucas_primality 106123 (2 : ZMod 106123)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 106123 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((769 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 106123)^53061 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 106123)^35374 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 106123)^4614 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 769 := Nat.prime_eq_prime_of_dvd_pow hq prime_769 hd
          subst q
          change (2 : ZMod 106123)^138 ≠ 1
          reduce_mod_char
          decide

theorem prime_106363 : Nat.Prime 106363 := by
  apply lucas_primality 106363 (2 : ZMod 106363)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 106363 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((19 : ℕ)^1 * ((311 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 106363)^53181 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 106363)^35454 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 106363)^5598 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 311 := Nat.prime_eq_prime_of_dvd_pow hq prime_311 hd
          subst q
          change (2 : ZMod 106363)^342 ≠ 1
          reduce_mod_char
          decide

theorem prime_106699 : Nat.Prime 106699 := by
  apply lucas_primality 106699 (3 : ZMod 106699)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 106699 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17783 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 106699)^53349 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 106699)^35566 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 17783 := Nat.prime_eq_prime_of_dvd_pow hq prime_17783 hd
        subst q
        change (3 : ZMod 106699)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_106753 : Nat.Prime 106753 := by
  apply lucas_primality 106753 (5 : ZMod 106753)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 106753 - 1 = (2 : ℕ)^8 * ((3 : ℕ)^1 * ((139 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 106753)^53376 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 106753)^35584 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
        subst q
        change (5 : ZMod 106753)^768 ≠ 1
        reduce_mod_char
        decide

theorem prime_106907 : Nat.Prime 106907 := by
  apply lucas_primality 106907 (2 : ZMod 106907)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 106907 - 1 = (2 : ℕ)^1 * ((53453 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 106907)^53453 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 53453 := Nat.prime_eq_prime_of_dvd_pow hq prime_53453 hd
      subst q
      change (2 : ZMod 106907)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_107273 : Nat.Prime 107273 := by
  apply lucas_primality 107273 (3 : ZMod 107273)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 107273 - 1 = (2 : ℕ)^3 * ((11 : ℕ)^1 * ((23 : ℕ)^1 * ((53 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 107273)^53636 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 107273)^9752 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (3 : ZMod 107273)^4664 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (3 : ZMod 107273)^2024 ≠ 1
          reduce_mod_char
          decide

theorem prime_107377 : Nat.Prime 107377 := by
  apply lucas_primality 107377 (10 : ZMod 107377)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 107377 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((2237 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 107377)^53688 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 107377)^35792 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2237 := Nat.prime_eq_prime_of_dvd_pow hq prime_2237 hd
        subst q
        change (10 : ZMod 107377)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_107441 : Nat.Prime 107441 := by
  apply lucas_primality 107441 (3 : ZMod 107441)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 107441 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((79 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 107441)^53720 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 107441)^21488 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (3 : ZMod 107441)^6320 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (3 : ZMod 107441)^1360 ≠ 1
          reduce_mod_char
          decide

theorem prime_108013 : Nat.Prime 108013 := by
  apply lucas_primality 108013 (6 : ZMod 108013)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 108013 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((9001 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 108013)^54006 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 108013)^36004 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 9001 := Nat.prime_eq_prime_of_dvd_pow hq prime_9001 hd
        subst q
        change (6 : ZMod 108013)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_109171 : Nat.Prime 109171 := by
  apply lucas_primality 109171 (2 : ZMod 109171)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 109171 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((1213 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 109171)^54585 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 109171)^36390 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 109171)^21834 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1213 := Nat.prime_eq_prime_of_dvd_pow hq prime_1213 hd
          subst q
          change (2 : ZMod 109171)^90 ≠ 1
          reduce_mod_char
          decide

theorem prime_109451 : Nat.Prime 109451 := by
  apply lucas_primality 109451 (2 : ZMod 109451)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 109451 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((11 : ℕ)^1 * ((199 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 109451)^54725 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 109451)^21890 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 109451)^9950 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 199 := Nat.prime_eq_prime_of_dvd_pow hq prime_199 hd
          subst q
          change (2 : ZMod 109451)^550 ≠ 1
          reduce_mod_char
          decide

theorem prime_109519 : Nat.Prime 109519 := by
  apply lucas_primality 109519 (3 : ZMod 109519)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 109519 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((18253 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 109519)^54759 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 109519)^36506 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 18253 := Nat.prime_eq_prime_of_dvd_pow hq prime_18253 hd
        subst q
        change (3 : ZMod 109519)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_110129 : Nat.Prime 110129 := by
  apply lucas_primality 110129 (3 : ZMod 110129)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 110129 - 1 = (2 : ℕ)^4 * ((6883 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 110129)^55064 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 6883 := Nat.prime_eq_prime_of_dvd_pow hq prime_6883 hd
      subst q
      change (3 : ZMod 110129)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_110501 : Nat.Prime 110501 := by
  apply lucas_primality 110501 (2 : ZMod 110501)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 110501 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^3 * ((13 : ℕ)^1 * ((17 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 110501)^55250 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 110501)^22100 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 110501)^8500 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 110501)^6500 ≠ 1
          reduce_mod_char
          decide

theorem prime_110729 : Nat.Prime 110729 := by
  apply lucas_primality 110729 (3 : ZMod 110729)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 110729 - 1 = (2 : ℕ)^3 * ((13841 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 110729)^55364 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 13841 := Nat.prime_eq_prime_of_dvd_pow hq prime_13841 hd
      subst q
      change (3 : ZMod 110729)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_110989 : Nat.Prime 110989 := by
  apply lucas_primality 110989 (2 : ZMod 110989)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 110989 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((3083 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 110989)^55494 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 110989)^36996 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3083 := Nat.prime_eq_prime_of_dvd_pow hq prime_3083 hd
        subst q
        change (2 : ZMod 110989)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_111103 : Nat.Prime 111103 := by
  apply lucas_primality 111103 (6 : ZMod 111103)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 111103 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((18517 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 111103)^55551 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 111103)^37034 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 18517 := Nat.prime_eq_prime_of_dvd_pow hq prime_18517 hd
        subst q
        change (6 : ZMod 111103)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_111443 : Nat.Prime 111443 := by
  apply lucas_primality 111443 (2 : ZMod 111443)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 111443 - 1 = (2 : ℕ)^1 * ((55721 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 111443)^55721 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 55721 := Nat.prime_eq_prime_of_dvd_pow hq prime_55721 hd
      subst q
      change (2 : ZMod 111443)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_111919 : Nat.Prime 111919 := by
  apply lucas_primality 111919 (3 : ZMod 111919)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 111919 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((811 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 111919)^55959 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 111919)^37306 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (3 : ZMod 111919)^4866 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 811 := Nat.prime_eq_prime_of_dvd_pow hq prime_811 hd
          subst q
          change (3 : ZMod 111919)^138 ≠ 1
          reduce_mod_char
          decide

theorem prime_112061 : Nat.Prime 112061 := by
  apply lucas_primality 112061 (3 : ZMod 112061)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 112061 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((431 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 112061)^56030 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 112061)^22412 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 112061)^8620 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 431 := Nat.prime_eq_prime_of_dvd_pow hq prime_431 hd
          subst q
          change (3 : ZMod 112061)^260 ≠ 1
          reduce_mod_char
          decide

theorem prime_112249 : Nat.Prime 112249 := by
  apply lucas_primality 112249 (26 : ZMod 112249)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 112249 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((1559 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (26 : ZMod 112249)^56124 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (26 : ZMod 112249)^37416 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1559 := Nat.prime_eq_prime_of_dvd_pow hq prime_1559 hd
        subst q
        change (26 : ZMod 112249)^72 ≠ 1
        reduce_mod_char
        decide

theorem prime_112303 : Nat.Prime 112303 := by
  apply lucas_primality 112303 (3 : ZMod 112303)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 112303 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((17 : ℕ)^1 * ((367 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 112303)^56151 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 112303)^37434 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (3 : ZMod 112303)^6606 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 367 := Nat.prime_eq_prime_of_dvd_pow hq prime_367 hd
          subst q
          change (3 : ZMod 112303)^306 ≠ 1
          reduce_mod_char
          decide

theorem prime_112349 : Nat.Prime 112349 := by
  apply lucas_primality 112349 (2 : ZMod 112349)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 112349 - 1 = (2 : ℕ)^2 * ((28087 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 112349)^56174 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 28087 := Nat.prime_eq_prime_of_dvd_pow hq prime_28087 hd
      subst q
      change (2 : ZMod 112349)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_112501 : Nat.Prime 112501 := by
  apply lucas_primality 112501 (10 : ZMod 112501)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 112501 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^5)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 112501)^56250 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 112501)^37500 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (10 : ZMod 112501)^22500 ≠ 1
        reduce_mod_char
        decide

theorem prime_112663 : Nat.Prime 112663 := by
  apply lucas_primality 112663 (10 : ZMod 112663)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 112663 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((569 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 112663)^56331 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 112663)^37554 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (10 : ZMod 112663)^10242 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 569 := Nat.prime_eq_prime_of_dvd_pow hq prime_569 hd
          subst q
          change (10 : ZMod 112663)^198 ≠ 1
          reduce_mod_char
          decide

theorem prime_112909 : Nat.Prime 112909 := by
  apply lucas_primality 112909 (2 : ZMod 112909)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 112909 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((97 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 112909)^56454 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 112909)^37636 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
        subst q
        change (2 : ZMod 112909)^1164 ≠ 1
        reduce_mod_char
        decide

theorem prime_113017 : Nat.Prime 113017 := by
  apply lucas_primality 113017 (10 : ZMod 113017)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 113017 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((277 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 113017)^56508 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 113017)^37672 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (10 : ZMod 113017)^6648 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 277 := Nat.prime_eq_prime_of_dvd_pow hq prime_277 hd
          subst q
          change (10 : ZMod 113017)^408 ≠ 1
          reduce_mod_char
          decide

theorem prime_113539 : Nat.Prime 113539 := by
  apply lucas_primality 113539 (2 : ZMod 113539)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 113539 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((127 : ℕ)^1 * ((149 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 113539)^56769 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 113539)^37846 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
          subst q
          change (2 : ZMod 113539)^894 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
          subst q
          change (2 : ZMod 113539)^762 ≠ 1
          reduce_mod_char
          decide

theorem prime_113557 : Nat.Prime 113557 := by
  apply lucas_primality 113557 (5 : ZMod 113557)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 113557 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((9463 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 113557)^56778 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 113557)^37852 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 9463 := Nat.prime_eq_prime_of_dvd_pow hq prime_9463 hd
        subst q
        change (5 : ZMod 113557)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_113759 : Nat.Prime 113759 := by
  apply lucas_primality 113759 (7 : ZMod 113759)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 113759 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((2473 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 113759)^56879 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (7 : ZMod 113759)^4946 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2473 := Nat.prime_eq_prime_of_dvd_pow hq prime_2473 hd
        subst q
        change (7 : ZMod 113759)^46 ≠ 1
        reduce_mod_char
        decide

theorem prime_114001 : Nat.Prime 114001 := by
  apply lucas_primality 114001 (7 : ZMod 114001)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 114001 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((5 : ℕ)^3 * ((19 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 114001)^57000 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 114001)^38000 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 114001)^22800 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (7 : ZMod 114001)^6000 ≠ 1
          reduce_mod_char
          decide

theorem prime_114641 : Nat.Prime 114641 := by
  apply lucas_primality 114641 (3 : ZMod 114641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 114641 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((1433 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 114641)^57320 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 114641)^22928 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1433 := Nat.prime_eq_prime_of_dvd_pow hq prime_1433 hd
        subst q
        change (3 : ZMod 114641)^80 ≠ 1
        reduce_mod_char
        decide

theorem prime_115019 : Nat.Prime 115019 := by
  apply lucas_primality 115019 (2 : ZMod 115019)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 115019 - 1 = (2 : ℕ)^1 * ((131 : ℕ)^1 * ((439 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 115019)^57509 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
        subst q
        change (2 : ZMod 115019)^878 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 439 := Nat.prime_eq_prime_of_dvd_pow hq prime_439 hd
        subst q
        change (2 : ZMod 115019)^262 ≠ 1
        reduce_mod_char
        decide

theorem prime_115151 : Nat.Prime 115151 := by
  apply lucas_primality 115151 (11 : ZMod 115151)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 115151 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((7 : ℕ)^2 * ((47 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 115151)^57575 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 115151)^23030 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (11 : ZMod 115151)^16450 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (11 : ZMod 115151)^2450 ≠ 1
          reduce_mod_char
          decide

theorem prime_116471 : Nat.Prime 116471 := by
  apply lucas_primality 116471 (11 : ZMod 116471)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 116471 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((19 : ℕ)^1 * ((613 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 116471)^58235 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 116471)^23294 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (11 : ZMod 116471)^6130 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 613 := Nat.prime_eq_prime_of_dvd_pow hq prime_613 hd
          subst q
          change (11 : ZMod 116471)^190 ≠ 1
          reduce_mod_char
          decide

theorem prime_116953 : Nat.Prime 116953 := by
  apply lucas_primality 116953 (5 : ZMod 116953)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 116953 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((443 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 116953)^58476 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 116953)^38984 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 116953)^10632 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 443 := Nat.prime_eq_prime_of_dvd_pow hq prime_443 hd
          subst q
          change (5 : ZMod 116953)^264 ≠ 1
          reduce_mod_char
          decide

theorem prime_116989 : Nat.Prime 116989 := by
  apply lucas_primality 116989 (10 : ZMod 116989)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 116989 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((9749 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 116989)^58494 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 116989)^38996 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 9749 := Nat.prime_eq_prime_of_dvd_pow hq prime_9749 hd
        subst q
        change (10 : ZMod 116989)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_117503 : Nat.Prime 117503 := by
  apply lucas_primality 117503 (5 : ZMod 117503)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 117503 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^2 * ((11 : ℕ)^1 * ((109 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 117503)^58751 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 117503)^16786 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 117503)^10682 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
          subst q
          change (5 : ZMod 117503)^1078 ≠ 1
          reduce_mod_char
          decide

theorem prime_117659 : Nat.Prime 117659 := by
  apply lucas_primality 117659 (2 : ZMod 117659)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 117659 - 1 = (2 : ℕ)^1 * ((89 : ℕ)^1 * ((661 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 117659)^58829 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
        subst q
        change (2 : ZMod 117659)^1322 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 661 := Nat.prime_eq_prime_of_dvd_pow hq prime_661 hd
        subst q
        change (2 : ZMod 117659)^178 ≠ 1
        reduce_mod_char
        decide

theorem prime_117881 : Nat.Prime 117881 := by
  apply lucas_primality 117881 (3 : ZMod 117881)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 117881 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((421 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 117881)^58940 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 117881)^23576 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 117881)^16840 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 421 := Nat.prime_eq_prime_of_dvd_pow hq prime_421 hd
          subst q
          change (3 : ZMod 117881)^280 ≠ 1
          reduce_mod_char
          decide

theorem prime_118399 : Nat.Prime 118399 := by
  apply lucas_primality 118399 (17 : ZMod 118399)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 118399 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((2819 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 118399)^59199 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 118399)^39466 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (17 : ZMod 118399)^16914 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2819 := Nat.prime_eq_prime_of_dvd_pow hq prime_2819 hd
          subst q
          change (17 : ZMod 118399)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_118471 : Nat.Prime 118471 := by
  apply lucas_primality 118471 (3 : ZMod 118471)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 118471 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((359 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 118471)^59235 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 118471)^39490 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 118471)^23694 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (3 : ZMod 118471)^10770 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 359 := Nat.prime_eq_prime_of_dvd_pow hq prime_359 hd
            subst q
            change (3 : ZMod 118471)^330 ≠ 1
            reduce_mod_char
            decide

theorem prime_119179 : Nat.Prime 119179 := by
  apply lucas_primality 119179 (3 : ZMod 119179)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 119179 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((2207 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 119179)^59589 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 119179)^39726 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2207 := Nat.prime_eq_prime_of_dvd_pow hq prime_2207 hd
        subst q
        change (3 : ZMod 119179)^54 ≠ 1
        reduce_mod_char
        decide

theorem prime_119297 : Nat.Prime 119297 := by
  apply lucas_primality 119297 (3 : ZMod 119297)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 119297 - 1 = (2 : ℕ)^9 * ((233 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 119297)^59648 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
      subst q
      change (3 : ZMod 119297)^512 ≠ 1
      reduce_mod_char
      decide

theorem prime_119363 : Nat.Prime 119363 := by
  apply lucas_primality 119363 (2 : ZMod 119363)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 119363 - 1 = (2 : ℕ)^1 * ((37 : ℕ)^1 * ((1613 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 119363)^59681 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (2 : ZMod 119363)^3226 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1613 := Nat.prime_eq_prime_of_dvd_pow hq prime_1613 hd
        subst q
        change (2 : ZMod 119363)^74 ≠ 1
        reduce_mod_char
        decide

theorem prime_120049 : Nat.Prime 120049 := by
  apply lucas_primality 120049 (7 : ZMod 120049)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 120049 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((41 : ℕ)^1 * ((61 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 120049)^60024 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 120049)^40016 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (7 : ZMod 120049)^2928 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (7 : ZMod 120049)^1968 ≠ 1
          reduce_mod_char
          decide

theorem prime_120091 : Nat.Prime 120091 := by
  apply lucas_primality 120091 (3 : ZMod 120091)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 120091 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((4003 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 120091)^60045 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 120091)^40030 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 120091)^24018 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4003 := Nat.prime_eq_prime_of_dvd_pow hq prime_4003 hd
          subst q
          change (3 : ZMod 120091)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_120247 : Nat.Prime 120247 := by
  apply lucas_primality 120247 (3 : ZMod 120247)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 120247 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((409 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 120247)^60123 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 120247)^40082 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 120247)^17178 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 409 := Nat.prime_eq_prime_of_dvd_pow hq prime_409 hd
          subst q
          change (3 : ZMod 120247)^294 ≠ 1
          reduce_mod_char
          decide

theorem prime_120833 : Nat.Prime 120833 := by
  apply lucas_primality 120833 (3 : ZMod 120833)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 120833 - 1 = (2 : ℕ)^11 * ((59 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 120833)^60416 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
      subst q
      change (3 : ZMod 120833)^2048 ≠ 1
      reduce_mod_char
      decide

theorem prime_120997 : Nat.Prime 120997 := by
  apply lucas_primality 120997 (2 : ZMod 120997)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 120997 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((3361 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 120997)^60498 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 120997)^40332 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3361 := Nat.prime_eq_prime_of_dvd_pow hq prime_3361 hd
        subst q
        change (2 : ZMod 120997)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_121591 : Nat.Prime 121591 := by
  apply lucas_primality 121591 (3 : ZMod 121591)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 121591 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((193 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 121591)^60795 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 121591)^40530 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 121591)^24318 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (3 : ZMod 121591)^17370 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
            subst q
            change (3 : ZMod 121591)^630 ≠ 1
            reduce_mod_char
            decide

theorem prime_123083 : Nat.Prime 123083 := by
  apply lucas_primality 123083 (2 : ZMod 123083)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 123083 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((41 : ℕ)^1 * ((79 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 123083)^61541 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 123083)^6478 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (2 : ZMod 123083)^3002 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (2 : ZMod 123083)^1558 ≠ 1
          reduce_mod_char
          decide

theorem prime_123973 : Nat.Prime 123973 := by
  apply lucas_primality 123973 (2 : ZMod 123973)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 123973 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((10331 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 123973)^61986 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 123973)^41324 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 10331 := Nat.prime_eq_prime_of_dvd_pow hq prime_10331 hd
        subst q
        change (2 : ZMod 123973)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_124721 : Nat.Prime 124721 := by
  apply lucas_primality 124721 (3 : ZMod 124721)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 124721 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((1559 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 124721)^62360 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 124721)^24944 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1559 := Nat.prime_eq_prime_of_dvd_pow hq prime_1559 hd
        subst q
        change (3 : ZMod 124721)^80 ≠ 1
        reduce_mod_char
        decide

theorem prime_124951 : Nat.Prime 124951 := by
  apply lucas_primality 124951 (3 : ZMod 124951)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 124951 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((7 : ℕ)^2 * ((17 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 124951)^62475 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 124951)^41650 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 124951)^24990 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (3 : ZMod 124951)^17850 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (3 : ZMod 124951)^7350 ≠ 1
            reduce_mod_char
            decide

theorem prime_125429 : Nat.Prime 125429 := by
  apply lucas_primality 125429 (2 : ZMod 125429)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 125429 - 1 = (2 : ℕ)^2 * ((31357 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 125429)^62714 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 31357 := Nat.prime_eq_prime_of_dvd_pow hq prime_31357 hd
      subst q
      change (2 : ZMod 125429)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_125509 : Nat.Prime 125509 := by
  apply lucas_primality 125509 (2 : ZMod 125509)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 125509 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((10459 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 125509)^62754 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 125509)^41836 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 10459 := Nat.prime_eq_prime_of_dvd_pow hq prime_10459 hd
        subst q
        change (2 : ZMod 125509)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_126013 : Nat.Prime 126013 := by
  apply lucas_primality 126013 (6 : ZMod 126013)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 126013 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((10501 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 126013)^63006 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 126013)^42004 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 10501 := Nat.prime_eq_prime_of_dvd_pow hq prime_10501 hd
        subst q
        change (6 : ZMod 126013)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_126097 : Nat.Prime 126097 := by
  apply lucas_primality 126097 (5 : ZMod 126097)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 126097 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((37 : ℕ)^1 * ((71 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 126097)^63048 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 126097)^42032 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (5 : ZMod 126097)^3408 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
          subst q
          change (5 : ZMod 126097)^1776 ≠ 1
          reduce_mod_char
          decide

theorem prime_126317 : Nat.Prime 126317 := by
  apply lucas_primality 126317 (2 : ZMod 126317)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 126317 - 1 = (2 : ℕ)^2 * ((23 : ℕ)^1 * ((1373 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 126317)^63158 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (2 : ZMod 126317)^5492 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1373 := Nat.prime_eq_prime_of_dvd_pow hq prime_1373 hd
        subst q
        change (2 : ZMod 126317)^92 ≠ 1
        reduce_mod_char
        decide

theorem prime_126691 : Nat.Prime 126691 := by
  apply lucas_primality 126691 (2 : ZMod 126691)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 126691 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((41 : ℕ)^1 * ((103 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 126691)^63345 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 126691)^42230 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 126691)^25338 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (2 : ZMod 126691)^3090 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
            subst q
            change (2 : ZMod 126691)^1230 ≠ 1
            reduce_mod_char
            decide

theorem prime_127549 : Nat.Prime 127549 := by
  apply lucas_primality 127549 (2 : ZMod 127549)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 127549 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((1181 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 127549)^63774 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 127549)^42516 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1181 := Nat.prime_eq_prime_of_dvd_pow hq prime_1181 hd
        subst q
        change (2 : ZMod 127549)^108 ≠ 1
        reduce_mod_char
        decide

theorem prime_127591 : Nat.Prime 127591 := by
  apply lucas_primality 127591 (3 : ZMod 127591)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 127591 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((4253 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 127591)^63795 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 127591)^42530 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 127591)^25518 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4253 := Nat.prime_eq_prime_of_dvd_pow hq prime_4253 hd
          subst q
          change (3 : ZMod 127591)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_128747 : Nat.Prime 128747 := by
  apply lucas_primality 128747 (2 : ZMod 128747)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 128747 - 1 = (2 : ℕ)^1 * ((64373 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 128747)^64373 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 64373 := Nat.prime_eq_prime_of_dvd_pow hq prime_64373 hd
      subst q
      change (2 : ZMod 128747)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_129403 : Nat.Prime 129403 := by
  apply lucas_primality 129403 (2 : ZMod 129403)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 129403 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((79 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 129403)^64701 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 129403)^43134 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 129403)^18486 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (2 : ZMod 129403)^9954 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
            subst q
            change (2 : ZMod 129403)^1638 ≠ 1
            reduce_mod_char
            decide

theorem prime_130211 : Nat.Prime 130211 := by
  apply lucas_primality 130211 (2 : ZMod 130211)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 130211 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((29 : ℕ)^1 * ((449 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 130211)^65105 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 130211)^26042 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (2 : ZMod 130211)^4490 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 449 := Nat.prime_eq_prime_of_dvd_pow hq prime_449 hd
          subst q
          change (2 : ZMod 130211)^290 ≠ 1
          reduce_mod_char
          decide

theorem prime_130261 : Nat.Prime 130261 := by
  apply lucas_primality 130261 (7 : ZMod 130261)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 130261 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((167 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 130261)^65130 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 130261)^43420 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 130261)^26052 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (7 : ZMod 130261)^10020 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
            subst q
            change (7 : ZMod 130261)^780 ≠ 1
            reduce_mod_char
            decide

theorem prime_130829 : Nat.Prime 130829 := by
  apply lucas_primality 130829 (2 : ZMod 130829)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 130829 - 1 = (2 : ℕ)^2 * ((32707 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 130829)^65414 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 32707 := Nat.prime_eq_prime_of_dvd_pow hq prime_32707 hd
      subst q
      change (2 : ZMod 130829)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_131671 : Nat.Prime 131671 := by
  apply lucas_primality 131671 (3 : ZMod 131671)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 131671 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((19 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 131671)^65835 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 131671)^43890 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 131671)^26334 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (3 : ZMod 131671)^18810 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
              subst q
              change (3 : ZMod 131671)^11970 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
              subst q
              change (3 : ZMod 131671)^6930 ≠ 1
              reduce_mod_char
              decide

theorem prime_131701 : Nat.Prime 131701 := by
  apply lucas_primality 131701 (6 : ZMod 131701)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 131701 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((439 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 131701)^65850 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 131701)^43900 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 131701)^26340 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 439 := Nat.prime_eq_prime_of_dvd_pow hq prime_439 hd
          subst q
          change (6 : ZMod 131701)^300 ≠ 1
          reduce_mod_char
          decide

theorem prime_133769 : Nat.Prime 133769 := by
  apply lucas_primality 133769 (3 : ZMod 133769)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 133769 - 1 = (2 : ℕ)^3 * ((23 : ℕ)^1 * ((727 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 133769)^66884 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (3 : ZMod 133769)^5816 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 727 := Nat.prime_eq_prime_of_dvd_pow hq prime_727 hd
        subst q
        change (3 : ZMod 133769)^184 ≠ 1
        reduce_mod_char
        decide

theorem prime_133801 : Nat.Prime 133801 := by
  apply lucas_primality 133801 (13 : ZMod 133801)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 133801 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((223 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 133801)^66900 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 133801)^44600 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 133801)^26760 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 223 := Nat.prime_eq_prime_of_dvd_pow hq prime_223 hd
          subst q
          change (13 : ZMod 133801)^600 ≠ 1
          reduce_mod_char
          decide

theorem prime_133831 : Nat.Prime 133831 := by
  apply lucas_primality 133831 (3 : ZMod 133831)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 133831 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((1487 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 133831)^66915 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 133831)^44610 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 133831)^26766 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1487 := Nat.prime_eq_prime_of_dvd_pow hq prime_1487 hd
          subst q
          change (3 : ZMod 133831)^90 ≠ 1
          reduce_mod_char
          decide

theorem prime_134353 : Nat.Prime 134353 := by
  apply lucas_primality 134353 (10 : ZMod 134353)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 134353 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^3 * ((311 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 134353)^67176 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 134353)^44784 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 311 := Nat.prime_eq_prime_of_dvd_pow hq prime_311 hd
        subst q
        change (10 : ZMod 134353)^432 ≠ 1
        reduce_mod_char
        decide

theorem prime_135029 : Nat.Prime 135029 := by
  apply lucas_primality 135029 (2 : ZMod 135029)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 135029 - 1 = (2 : ℕ)^2 * ((33757 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 135029)^67514 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 33757 := Nat.prime_eq_prime_of_dvd_pow hq prime_33757 hd
      subst q
      change (2 : ZMod 135029)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_135173 : Nat.Prime 135173 := by
  apply lucas_primality 135173 (2 : ZMod 135173)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 135173 - 1 = (2 : ℕ)^2 * ((47 : ℕ)^1 * ((719 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 135173)^67586 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (2 : ZMod 135173)^2876 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 719 := Nat.prime_eq_prime_of_dvd_pow hq prime_719 hd
        subst q
        change (2 : ZMod 135173)^188 ≠ 1
        reduce_mod_char
        decide

theorem prime_135427 : Nat.Prime 135427 := by
  apply lucas_primality 135427 (2 : ZMod 135427)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 135427 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((22571 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 135427)^67713 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 135427)^45142 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 22571 := Nat.prime_eq_prime_of_dvd_pow hq prime_22571 hd
        subst q
        change (2 : ZMod 135427)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_135467 : Nat.Prime 135467 := by
  apply lucas_primality 135467 (2 : ZMod 135467)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 135467 - 1 = (2 : ℕ)^1 * ((67733 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 135467)^67733 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 67733 := Nat.prime_eq_prime_of_dvd_pow hq prime_67733 hd
      subst q
      change (2 : ZMod 135467)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_135671 : Nat.Prime 135671 := by
  apply lucas_primality 135671 (7 : ZMod 135671)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 135671 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((13567 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 135671)^67835 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 135671)^27134 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13567 := Nat.prime_eq_prime_of_dvd_pow hq prime_13567 hd
        subst q
        change (7 : ZMod 135671)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_136429 : Nat.Prime 136429 := by
  apply lucas_primality 136429 (2 : ZMod 136429)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 136429 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((11369 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 136429)^68214 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 136429)^45476 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 11369 := Nat.prime_eq_prime_of_dvd_pow hq prime_11369 hd
        subst q
        change (2 : ZMod 136429)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_136531 : Nat.Prime 136531 := by
  apply lucas_primality 136531 (2 : ZMod 136531)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 136531 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((37 : ℕ)^1 * ((41 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 136531)^68265 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 136531)^45510 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 136531)^27306 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
            subst q
            change (2 : ZMod 136531)^3690 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (2 : ZMod 136531)^3330 ≠ 1
            reduce_mod_char
            decide

theorem prime_136709 : Nat.Prime 136709 := by
  apply lucas_primality 136709 (3 : ZMod 136709)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 136709 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((239 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 136709)^68354 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 136709)^12428 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 136709)^10516 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 239 := Nat.prime_eq_prime_of_dvd_pow hq prime_239 hd
          subst q
          change (3 : ZMod 136709)^572 ≠ 1
          reduce_mod_char
          decide

theorem prime_137593 : Nat.Prime 137593 := by
  apply lucas_primality 137593 (10 : ZMod 137593)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 137593 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((7 : ℕ)^2 * ((13 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 137593)^68796 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 137593)^45864 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (10 : ZMod 137593)^19656 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (10 : ZMod 137593)^10584 ≠ 1
          reduce_mod_char
          decide

theorem prime_137597 : Nat.Prime 137597 := by
  apply lucas_primality 137597 (2 : ZMod 137597)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 137597 - 1 = (2 : ℕ)^2 * ((41 : ℕ)^1 * ((839 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 137597)^68798 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
        subst q
        change (2 : ZMod 137597)^3356 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 839 := Nat.prime_eq_prime_of_dvd_pow hq prime_839 hd
        subst q
        change (2 : ZMod 137597)^164 ≠ 1
        reduce_mod_char
        decide

theorem prime_137723 : Nat.Prime 137723 := by
  apply lucas_primality 137723 (2 : ZMod 137723)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 137723 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((5297 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 137723)^68861 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 137723)^10594 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5297 := Nat.prime_eq_prime_of_dvd_pow hq prime_5297 hd
        subst q
        change (2 : ZMod 137723)^26 ≠ 1
        reduce_mod_char
        decide

theorem prime_138403 : Nat.Prime 138403 := by
  apply lucas_primality 138403 (2 : ZMod 138403)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 138403 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((11 : ℕ)^1 * ((233 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 138403)^69201 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 138403)^46134 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 138403)^12582 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
          subst q
          change (2 : ZMod 138403)^594 ≠ 1
          reduce_mod_char
          decide

theorem prime_138451 : Nat.Prime 138451 := by
  apply lucas_primality 138451 (2 : ZMod 138451)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 138451 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((13 : ℕ)^1 * ((71 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 138451)^69225 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 138451)^46150 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 138451)^27690 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (2 : ZMod 138451)^10650 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
            subst q
            change (2 : ZMod 138451)^1950 ≠ 1
            reduce_mod_char
            decide

theorem prime_139943 : Nat.Prime 139943 := by
  apply lucas_primality 139943 (5 : ZMod 139943)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 139943 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((6361 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 139943)^69971 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 139943)^12722 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 6361 := Nat.prime_eq_prime_of_dvd_pow hq prime_6361 hd
        subst q
        change (5 : ZMod 139943)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_140683 : Nat.Prime 140683 := by
  apply lucas_primality 140683 (2 : ZMod 140683)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 140683 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((23447 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 140683)^70341 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 140683)^46894 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 23447 := Nat.prime_eq_prime_of_dvd_pow hq prime_23447 hd
        subst q
        change (2 : ZMod 140683)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_141067 : Nat.Prime 141067 := by
  apply lucas_primality 141067 (2 : ZMod 141067)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 141067 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((17 : ℕ)^1 * ((461 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 141067)^70533 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 141067)^47022 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 141067)^8298 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 461 := Nat.prime_eq_prime_of_dvd_pow hq prime_461 hd
          subst q
          change (2 : ZMod 141067)^306 ≠ 1
          reduce_mod_char
          decide

theorem prime_141311 : Nat.Prime 141311 := by
  apply lucas_primality 141311 (7 : ZMod 141311)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 141311 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((1087 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 141311)^70655 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 141311)^28262 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (7 : ZMod 141311)^10870 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1087 := Nat.prime_eq_prime_of_dvd_pow hq prime_1087 hd
          subst q
          change (7 : ZMod 141311)^130 ≠ 1
          reduce_mod_char
          decide

theorem prime_141511 : Nat.Prime 141511 := by
  apply lucas_primality 141511 (3 : ZMod 141511)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 141511 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((53 : ℕ)^1 * ((89 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 141511)^70755 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 141511)^47170 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 141511)^28302 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
            subst q
            change (3 : ZMod 141511)^2670 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
            subst q
            change (3 : ZMod 141511)^1590 ≠ 1
            reduce_mod_char
            decide

theorem prime_142543 : Nat.Prime 142543 := by
  apply lucas_primality 142543 (3 : ZMod 142543)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 142543 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7919 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 142543)^71271 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 142543)^47514 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7919 := Nat.prime_eq_prime_of_dvd_pow hq prime_7919 hd
        subst q
        change (3 : ZMod 142543)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_142973 : Nat.Prime 142973 := by
  apply lucas_primality 142973 (2 : ZMod 142973)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 142973 - 1 = (2 : ℕ)^2 * ((31 : ℕ)^1 * ((1153 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 142973)^71486 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (2 : ZMod 142973)^4612 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1153 := Nat.prime_eq_prime_of_dvd_pow hq prime_1153 hd
        subst q
        change (2 : ZMod 142973)^124 ≠ 1
        reduce_mod_char
        decide

theorem prime_143249 : Nat.Prime 143249 := by
  apply lucas_primality 143249 (3 : ZMod 143249)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 143249 - 1 = (2 : ℕ)^4 * ((7 : ℕ)^1 * ((1279 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 143249)^71624 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 143249)^20464 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1279 := Nat.prime_eq_prime_of_dvd_pow hq prime_1279 hd
        subst q
        change (3 : ZMod 143249)^112 ≠ 1
        reduce_mod_char
        decide

theorem prime_143573 : Nat.Prime 143573 := by
  apply lucas_primality 143573 (2 : ZMod 143573)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 143573 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((251 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 143573)^71786 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 143573)^13052 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 143573)^11044 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 251 := Nat.prime_eq_prime_of_dvd_pow hq prime_251 hd
          subst q
          change (2 : ZMod 143573)^572 ≠ 1
          reduce_mod_char
          decide

theorem prime_145031 : Nat.Prime 145031 := by
  apply lucas_primality 145031 (19 : ZMod 145031)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 145031 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((14503 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 145031)^72515 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (19 : ZMod 145031)^29006 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 14503 := Nat.prime_eq_prime_of_dvd_pow hq prime_14503 hd
        subst q
        change (19 : ZMod 145031)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_146023 : Nat.Prime 146023 := by
  apply lucas_primality 146023 (3 : ZMod 146023)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 146023 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((24337 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 146023)^73011 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 146023)^48674 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 24337 := Nat.prime_eq_prime_of_dvd_pow hq prime_24337 hd
        subst q
        change (3 : ZMod 146023)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_146117 : Nat.Prime 146117 := by
  apply lucas_primality 146117 (2 : ZMod 146117)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 146117 - 1 = (2 : ℕ)^2 * ((36529 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 146117)^73058 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 36529 := Nat.prime_eq_prime_of_dvd_pow hq prime_36529 hd
      subst q
      change (2 : ZMod 146117)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_146309 : Nat.Prime 146309 := by
  apply lucas_primality 146309 (2 : ZMod 146309)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 146309 - 1 = (2 : ℕ)^2 * ((79 : ℕ)^1 * ((463 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 146309)^73154 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
        subst q
        change (2 : ZMod 146309)^1852 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 463 := Nat.prime_eq_prime_of_dvd_pow hq prime_463 hd
        subst q
        change (2 : ZMod 146309)^316 ≠ 1
        reduce_mod_char
        decide

theorem prime_146417 : Nat.Prime 146417 := by
  apply lucas_primality 146417 (3 : ZMod 146417)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 146417 - 1 = (2 : ℕ)^4 * ((9151 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 146417)^73208 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 9151 := Nat.prime_eq_prime_of_dvd_pow hq prime_9151 hd
      subst q
      change (3 : ZMod 146417)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_146437 : Nat.Prime 146437 := by
  apply lucas_primality 146437 (2 : ZMod 146437)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 146437 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((12203 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 146437)^73218 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 146437)^48812 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 12203 := Nat.prime_eq_prime_of_dvd_pow hq prime_12203 hd
        subst q
        change (2 : ZMod 146437)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_147073 : Nat.Prime 147073 := by
  apply lucas_primality 147073 (5 : ZMod 147073)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 147073 - 1 = (2 : ℕ)^7 * ((3 : ℕ)^1 * ((383 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 147073)^73536 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 147073)^49024 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 383 := Nat.prime_eq_prime_of_dvd_pow hq prime_383 hd
        subst q
        change (5 : ZMod 147073)^384 ≠ 1
        reduce_mod_char
        decide

theorem prime_148763 : Nat.Prime 148763 := by
  apply lucas_primality 148763 (2 : ZMod 148763)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 148763 - 1 = (2 : ℕ)^1 * ((74381 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 148763)^74381 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 74381 := Nat.prime_eq_prime_of_dvd_pow hq prime_74381 hd
      subst q
      change (2 : ZMod 148763)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_149153 : Nat.Prime 149153 := by
  apply lucas_primality 149153 (3 : ZMod 149153)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 149153 - 1 = (2 : ℕ)^5 * ((59 : ℕ)^1 * ((79 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 149153)^74576 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
        subst q
        change (3 : ZMod 149153)^2528 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
        subst q
        change (3 : ZMod 149153)^1888 ≠ 1
        reduce_mod_char
        decide

theorem prime_150151 : Nat.Prime 150151 := by
  apply lucas_primality 150151 (6 : ZMod 150151)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 150151 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 150151)^75075 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 150151)^50050 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 150151)^30030 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (6 : ZMod 150151)^21450 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
              subst q
              change (6 : ZMod 150151)^13650 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
              subst q
              change (6 : ZMod 150151)^11550 ≠ 1
              reduce_mod_char
              decide

theorem prime_150329 : Nat.Prime 150329 := by
  apply lucas_primality 150329 (3 : ZMod 150329)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 150329 - 1 = (2 : ℕ)^3 * ((19 : ℕ)^1 * ((23 : ℕ)^1 * ((43 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 150329)^75164 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (3 : ZMod 150329)^7912 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (3 : ZMod 150329)^6536 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (3 : ZMod 150329)^3496 ≠ 1
          reduce_mod_char
          decide

theorem prime_150383 : Nat.Prime 150383 := by
  apply lucas_primality 150383 (5 : ZMod 150383)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 150383 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((4423 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 150383)^75191 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (5 : ZMod 150383)^8846 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4423 := Nat.prime_eq_prime_of_dvd_pow hq prime_4423 hd
        subst q
        change (5 : ZMod 150383)^34 ≠ 1
        reduce_mod_char
        decide

theorem prime_150617 : Nat.Prime 150617 := by
  apply lucas_primality 150617 (3 : ZMod 150617)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 150617 - 1 = (2 : ℕ)^3 * ((67 : ℕ)^1 * ((281 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 150617)^75308 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
        subst q
        change (3 : ZMod 150617)^2248 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 281 := Nat.prime_eq_prime_of_dvd_pow hq prime_281 hd
        subst q
        change (3 : ZMod 150617)^536 ≠ 1
        reduce_mod_char
        decide

theorem prime_151289 : Nat.Prime 151289 := by
  apply lucas_primality 151289 (3 : ZMod 151289)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 151289 - 1 = (2 : ℕ)^3 * ((18911 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 151289)^75644 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 18911 := Nat.prime_eq_prime_of_dvd_pow hq prime_18911 hd
      subst q
      change (3 : ZMod 151289)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_151397 : Nat.Prime 151397 := by
  apply lucas_primality 151397 (2 : ZMod 151397)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 151397 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((5407 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 151397)^75698 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 151397)^21628 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5407 := Nat.prime_eq_prime_of_dvd_pow hq prime_5407 hd
        subst q
        change (2 : ZMod 151397)^28 ≠ 1
        reduce_mod_char
        decide

theorem prime_152377 : Nat.Prime 152377 := by
  apply lucas_primality 152377 (5 : ZMod 152377)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 152377 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((907 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 152377)^76188 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 152377)^50792 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 152377)^21768 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 907 := Nat.prime_eq_prime_of_dvd_pow hq prime_907 hd
          subst q
          change (5 : ZMod 152377)^168 ≠ 1
          reduce_mod_char
          decide

theorem prime_152441 : Nat.Prime 152441 := by
  apply lucas_primality 152441 (3 : ZMod 152441)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 152441 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((37 : ℕ)^1 * ((103 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 152441)^76220 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 152441)^30488 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (3 : ZMod 152441)^4120 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
          subst q
          change (3 : ZMod 152441)^1480 ≠ 1
          reduce_mod_char
          decide

theorem prime_153133 : Nat.Prime 153133 := by
  apply lucas_primality 153133 (2 : ZMod 153133)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 153133 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((1823 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 153133)^76566 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 153133)^51044 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 153133)^21876 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1823 := Nat.prime_eq_prime_of_dvd_pow hq prime_1823 hd
          subst q
          change (2 : ZMod 153133)^84 ≠ 1
          reduce_mod_char
          decide

theorem prime_153469 : Nat.Prime 153469 := by
  apply lucas_primality 153469 (2 : ZMod 153469)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 153469 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((7 : ℕ)^2 * ((29 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 153469)^76734 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 153469)^51156 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 153469)^21924 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (2 : ZMod 153469)^5292 ≠ 1
          reduce_mod_char
          decide

end LegendreK6.Pratt
