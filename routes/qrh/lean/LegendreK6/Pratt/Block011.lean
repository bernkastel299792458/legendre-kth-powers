import LegendreK6.Pratt.Block010

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LegendreK6.Pratt

theorem prime_694609 : Nat.Prime 694609 := by
  apply lucas_primality 694609 (13 : ZMod 694609)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 694609 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((29 : ℕ)^1 * ((499 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 694609)^347304 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 694609)^231536 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (13 : ZMod 694609)^23952 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 499 := Nat.prime_eq_prime_of_dvd_pow hq prime_499 hd
          subst q
          change (13 : ZMod 694609)^1392 ≠ 1
          reduce_mod_char
          decide

theorem prime_695881 : Nat.Prime 695881 := by
  apply lucas_primality 695881 (11 : ZMod 695881)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 695881 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((1933 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 695881)^347940 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 695881)^231960 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 695881)^139176 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1933 := Nat.prime_eq_prime_of_dvd_pow hq prime_1933 hd
          subst q
          change (11 : ZMod 695881)^360 ≠ 1
          reduce_mod_char
          decide

theorem prime_698827 : Nat.Prime 698827 := by
  apply lucas_primality 698827 (2 : ZMod 698827)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 698827 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((116471 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 698827)^349413 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 698827)^232942 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 116471 := Nat.prime_eq_prime_of_dvd_pow hq prime_116471 hd
        subst q
        change (2 : ZMod 698827)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_702113 : Nat.Prime 702113 := by
  apply lucas_primality 702113 (3 : ZMod 702113)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 702113 - 1 = (2 : ℕ)^5 * ((37 : ℕ)^1 * ((593 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 702113)^351056 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (3 : ZMod 702113)^18976 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 593 := Nat.prime_eq_prime_of_dvd_pow hq prime_593 hd
        subst q
        change (3 : ZMod 702113)^1184 ≠ 1
        reduce_mod_char
        decide

theorem prime_703349 : Nat.Prime 703349 := by
  apply lucas_primality 703349 (2 : ZMod 703349)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 703349 - 1 = (2 : ℕ)^2 * ((175837 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 703349)^351674 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 175837 := Nat.prime_eq_prime_of_dvd_pow hq prime_175837 hd
      subst q
      change (2 : ZMod 703349)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_716563 : Nat.Prime 716563 := by
  apply lucas_primality 716563 (7 : ZMod 716563)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 716563 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((11 : ℕ)^2 * ((47 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 716563)^358281 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 716563)^238854 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 716563)^102366 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (7 : ZMod 716563)^65142 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
            subst q
            change (7 : ZMod 716563)^15246 ≠ 1
            reduce_mod_char
            decide

theorem prime_725149 : Nat.Prime 725149 := by
  apply lucas_primality 725149 (11 : ZMod 725149)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 725149 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((20143 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 725149)^362574 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 725149)^241716 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 20143 := Nat.prime_eq_prime_of_dvd_pow hq prime_20143 hd
        subst q
        change (11 : ZMod 725149)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_725983 : Nat.Prime 725983 := by
  apply lucas_primality 725983 (5 : ZMod 725983)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 725983 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((120997 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 725983)^362991 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 725983)^241994 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 120997 := Nat.prime_eq_prime_of_dvd_pow hq prime_120997 hd
        subst q
        change (5 : ZMod 725983)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_729527 : Nat.Prime 729527 := by
  apply lucas_primality 729527 (5 : ZMod 729527)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 729527 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((107 : ℕ)^1 * ((487 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 729527)^364763 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 729527)^104218 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
          subst q
          change (5 : ZMod 729527)^6818 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 487 := Nat.prime_eq_prime_of_dvd_pow hq prime_487 hd
          subst q
          change (5 : ZMod 729527)^1498 ≠ 1
          reduce_mod_char
          decide

theorem prime_735419 : Nat.Prime 735419 := by
  apply lucas_primality 735419 (2 : ZMod 735419)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 735419 - 1 = (2 : ℕ)^1 * ((71 : ℕ)^1 * ((5179 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 735419)^367709 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
        subst q
        change (2 : ZMod 735419)^10358 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5179 := Nat.prime_eq_prime_of_dvd_pow hq prime_5179 hd
        subst q
        change (2 : ZMod 735419)^142 ≠ 1
        reduce_mod_char
        decide

theorem prime_736249 : Nat.Prime 736249 := by
  apply lucas_primality 736249 (7 : ZMod 736249)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 736249 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((30677 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 736249)^368124 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 736249)^245416 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 30677 := Nat.prime_eq_prime_of_dvd_pow hq prime_30677 hd
        subst q
        change (7 : ZMod 736249)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_739111 : Nat.Prime 739111 := by
  apply lucas_primality 739111 (3 : ZMod 739111)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 739111 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((71 : ℕ)^1 * ((347 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 739111)^369555 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 739111)^246370 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 739111)^147822 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
            subst q
            change (3 : ZMod 739111)^10410 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 347 := Nat.prime_eq_prime_of_dvd_pow hq prime_347 hd
            subst q
            change (3 : ZMod 739111)^2130 ≠ 1
            reduce_mod_char
            decide

theorem prime_740329 : Nat.Prime 740329 := by
  apply lucas_primality 740329 (11 : ZMod 740329)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 740329 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((109 : ℕ)^1 * ((283 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 740329)^370164 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 740329)^246776 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
          subst q
          change (11 : ZMod 740329)^6792 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 283 := Nat.prime_eq_prime_of_dvd_pow hq prime_283 hd
          subst q
          change (11 : ZMod 740329)^2616 ≠ 1
          reduce_mod_char
          decide

theorem prime_748807 : Nat.Prime 748807 := by
  apply lucas_primality 748807 (6 : ZMod 748807)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 748807 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((37 : ℕ)^1 * ((3373 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 748807)^374403 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 748807)^249602 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (6 : ZMod 748807)^20238 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3373 := Nat.prime_eq_prime_of_dvd_pow hq prime_3373 hd
          subst q
          change (6 : ZMod 748807)^222 ≠ 1
          reduce_mod_char
          decide

theorem prime_749461 : Nat.Prime 749461 := by
  apply lucas_primality 749461 (2 : ZMod 749461)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 749461 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((12491 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 749461)^374730 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 749461)^249820 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 749461)^149892 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 12491 := Nat.prime_eq_prime_of_dvd_pow hq prime_12491 hd
          subst q
          change (2 : ZMod 749461)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_751481 : Nat.Prime 751481 := by
  apply lucas_primality 751481 (3 : ZMod 751481)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 751481 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((18787 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 751481)^375740 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 751481)^150296 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 18787 := Nat.prime_eq_prime_of_dvd_pow hq prime_18787 hd
        subst q
        change (3 : ZMod 751481)^40 ≠ 1
        reduce_mod_char
        decide

theorem prime_751813 : Nat.Prime 751813 := by
  apply lucas_primality 751813 (6 : ZMod 751813)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 751813 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((31 : ℕ)^1 * ((43 : ℕ)^1 * ((47 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 751813)^375906 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 751813)^250604 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (6 : ZMod 751813)^24252 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (6 : ZMod 751813)^17484 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
            subst q
            change (6 : ZMod 751813)^15996 ≠ 1
            reduce_mod_char
            decide

theorem prime_752701 : Nat.Prime 752701 := by
  apply lucas_primality 752701 (10 : ZMod 752701)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 752701 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((13 : ℕ)^1 * ((193 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 752701)^376350 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 752701)^250900 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 752701)^150540 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (10 : ZMod 752701)^57900 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
            subst q
            change (10 : ZMod 752701)^3900 ≠ 1
            reduce_mod_char
            decide

theorem prime_756601 : Nat.Prime 756601 := by
  apply lucas_primality 756601 (11 : ZMod 756601)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 756601 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((13 : ℕ)^1 * ((97 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 756601)^378300 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 756601)^252200 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 756601)^151320 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (11 : ZMod 756601)^58200 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
            subst q
            change (11 : ZMod 756601)^7800 ≠ 1
            reduce_mod_char
            decide

theorem prime_756853 : Nat.Prime 756853 := by
  apply lucas_primality 756853 (2 : ZMod 756853)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 756853 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((59 : ℕ)^1 * ((1069 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 756853)^378426 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 756853)^252284 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (2 : ZMod 756853)^12828 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1069 := Nat.prime_eq_prime_of_dvd_pow hq prime_1069 hd
          subst q
          change (2 : ZMod 756853)^708 ≠ 1
          reduce_mod_char
          decide

theorem prime_763159 : Nat.Prime 763159 := by
  apply lucas_primality 763159 (6 : ZMod 763159)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 763159 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((31 : ℕ)^1 * ((373 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 763159)^381579 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 763159)^254386 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (6 : ZMod 763159)^69378 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (6 : ZMod 763159)^24618 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 373 := Nat.prime_eq_prime_of_dvd_pow hq prime_373 hd
            subst q
            change (6 : ZMod 763159)^2046 ≠ 1
            reduce_mod_char
            decide

theorem prime_763619 : Nat.Prime 763619 := by
  apply lucas_primality 763619 (2 : ZMod 763619)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 763619 - 1 = (2 : ℕ)^1 * ((191 : ℕ)^1 * ((1999 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 763619)^381809 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
        subst q
        change (2 : ZMod 763619)^3998 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1999 := Nat.prime_eq_prime_of_dvd_pow hq prime_1999 hd
        subst q
        change (2 : ZMod 763619)^382 ≠ 1
        reduce_mod_char
        decide

theorem prime_772441 : Nat.Prime 772441 := by
  apply lucas_primality 772441 (14 : ZMod 772441)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 772441 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((41 : ℕ)^1 * ((157 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 772441)^386220 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 772441)^257480 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (14 : ZMod 772441)^154488 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (14 : ZMod 772441)^18840 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
            subst q
            change (14 : ZMod 772441)^4920 ≠ 1
            reduce_mod_char
            decide

theorem prime_780323 : Nat.Prime 780323 := by
  apply lucas_primality 780323 (2 : ZMod 780323)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 780323 - 1 = (2 : ℕ)^1 * ((390161 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 780323)^390161 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 390161 := Nat.prime_eq_prime_of_dvd_pow hq prime_390161 hd
      subst q
      change (2 : ZMod 780323)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_783487 : Nat.Prime 783487 := by
  apply lucas_primality 783487 (3 : ZMod 783487)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 783487 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((11 : ℕ)^1 * ((1319 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 783487)^391743 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 783487)^261162 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 783487)^71226 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1319 := Nat.prime_eq_prime_of_dvd_pow hq prime_1319 hd
          subst q
          change (3 : ZMod 783487)^594 ≠ 1
          reduce_mod_char
          decide

theorem prime_788153 : Nat.Prime 788153 := by
  apply lucas_primality 788153 (3 : ZMod 788153)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 788153 - 1 = (2 : ℕ)^3 * ((98519 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 788153)^394076 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 98519 := Nat.prime_eq_prime_of_dvd_pow hq prime_98519 hd
      subst q
      change (3 : ZMod 788153)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_788701 : Nat.Prime 788701 := by
  apply lucas_primality 788701 (2 : ZMod 788701)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 788701 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((11 : ℕ)^1 * ((239 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 788701)^394350 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 788701)^262900 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 788701)^157740 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (2 : ZMod 788701)^71700 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 239 := Nat.prime_eq_prime_of_dvd_pow hq prime_239 hd
            subst q
            change (2 : ZMod 788701)^3300 ≠ 1
            reduce_mod_char
            decide

theorem prime_790819 : Nat.Prime 790819 := by
  apply lucas_primality 790819 (2 : ZMod 790819)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 790819 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((19 : ℕ)^1 * ((991 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 790819)^395409 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 790819)^263606 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 790819)^112974 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (2 : ZMod 790819)^41622 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 991 := Nat.prime_eq_prime_of_dvd_pow hq prime_991 hd
            subst q
            change (2 : ZMod 790819)^798 ≠ 1
            reduce_mod_char
            decide

theorem prime_790871 : Nat.Prime 790871 := by
  apply lucas_primality 790871 (7 : ZMod 790871)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 790871 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((79087 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 790871)^395435 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 790871)^158174 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 79087 := Nat.prime_eq_prime_of_dvd_pow hq prime_79087 hd
        subst q
        change (7 : ZMod 790871)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_797957 : Nat.Prime 797957 := by
  apply lucas_primality 797957 (2 : ZMod 797957)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 797957 - 1 = (2 : ℕ)^2 * ((199489 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 797957)^398978 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 199489 := Nat.prime_eq_prime_of_dvd_pow hq prime_199489 hd
      subst q
      change (2 : ZMod 797957)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_803867 : Nat.Prime 803867 := by
  apply lucas_primality 803867 (2 : ZMod 803867)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 803867 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((67 : ℕ)^1 * ((857 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 803867)^401933 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 803867)^114838 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (2 : ZMod 803867)^11998 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 857 := Nat.prime_eq_prime_of_dvd_pow hq prime_857 hd
          subst q
          change (2 : ZMod 803867)^938 ≠ 1
          reduce_mod_char
          decide

theorem prime_804847 : Nat.Prime 804847 := by
  apply lucas_primality 804847 (3 : ZMod 804847)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 804847 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((19163 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 804847)^402423 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 804847)^268282 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 804847)^114978 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 19163 := Nat.prime_eq_prime_of_dvd_pow hq prime_19163 hd
          subst q
          change (3 : ZMod 804847)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_804901 : Nat.Prime 804901 := by
  apply lucas_primality 804901 (2 : ZMod 804901)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 804901 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((2683 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 804901)^402450 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 804901)^268300 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 804901)^160980 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2683 := Nat.prime_eq_prime_of_dvd_pow hq prime_2683 hd
          subst q
          change (2 : ZMod 804901)^300 ≠ 1
          reduce_mod_char
          decide

theorem prime_812051 : Nat.Prime 812051 := by
  apply lucas_primality 812051 (2 : ZMod 812051)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 812051 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((109 : ℕ)^1 * ((149 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 812051)^406025 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 812051)^162410 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
          subst q
          change (2 : ZMod 812051)^7450 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
          subst q
          change (2 : ZMod 812051)^5450 ≠ 1
          reduce_mod_char
          decide

theorem prime_813107 : Nat.Prime 813107 := by
  apply lucas_primality 813107 (2 : ZMod 813107)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 813107 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^2 * ((8297 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 813107)^406553 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 813107)^116158 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 8297 := Nat.prime_eq_prime_of_dvd_pow hq prime_8297 hd
        subst q
        change (2 : ZMod 813107)^98 ≠ 1
        reduce_mod_char
        decide

theorem prime_813277 : Nat.Prime 813277 := by
  apply lucas_primality 813277 (2 : ZMod 813277)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 813277 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((19 : ℕ)^1 * ((29 : ℕ)^1 * ((41 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 813277)^406638 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 813277)^271092 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 813277)^42804 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (2 : ZMod 813277)^28044 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (2 : ZMod 813277)^19836 ≠ 1
            reduce_mod_char
            decide

theorem prime_813613 : Nat.Prime 813613 := by
  apply lucas_primality 813613 (2 : ZMod 813613)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 813613 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((67801 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 813613)^406806 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 813613)^271204 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 67801 := Nat.prime_eq_prime_of_dvd_pow hq prime_67801 hd
        subst q
        change (2 : ZMod 813613)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_819629 : Nat.Prime 819629 := by
  apply lucas_primality 819629 (2 : ZMod 819629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 819629 - 1 = (2 : ℕ)^2 * ((23 : ℕ)^1 * ((59 : ℕ)^1 * ((151 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 819629)^409814 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (2 : ZMod 819629)^35636 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (2 : ZMod 819629)^13892 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
          subst q
          change (2 : ZMod 819629)^5428 ≠ 1
          reduce_mod_char
          decide

theorem prime_821939 : Nat.Prime 821939 := by
  apply lucas_primality 821939 (2 : ZMod 821939)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 821939 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((101 : ℕ)^1 * ((313 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 821939)^410969 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 821939)^63226 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
          subst q
          change (2 : ZMod 821939)^8138 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 313 := Nat.prime_eq_prime_of_dvd_pow hq prime_313 hd
          subst q
          change (2 : ZMod 821939)^2626 ≠ 1
          reduce_mod_char
          decide

theorem prime_828953 : Nat.Prime 828953 := by
  apply lucas_primality 828953 (3 : ZMod 828953)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 828953 - 1 = (2 : ℕ)^3 * ((103619 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 828953)^414476 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 103619 := Nat.prime_eq_prime_of_dvd_pow hq prime_103619 hd
      subst q
      change (3 : ZMod 828953)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_829069 : Nat.Prime 829069 := by
  apply lucas_primality 829069 (2 : ZMod 829069)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 829069 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((59 : ℕ)^1 * ((1171 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 829069)^414534 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 829069)^276356 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (2 : ZMod 829069)^14052 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1171 := Nat.prime_eq_prime_of_dvd_pow hq prime_1171 hd
          subst q
          change (2 : ZMod 829069)^708 ≠ 1
          reduce_mod_char
          decide

theorem prime_830051 : Nat.Prime 830051 := by
  apply lucas_primality 830051 (6 : ZMod 830051)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 830051 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((13 : ℕ)^1 * ((1277 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 830051)^415025 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 830051)^166010 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (6 : ZMod 830051)^63850 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1277 := Nat.prime_eq_prime_of_dvd_pow hq prime_1277 hd
          subst q
          change (6 : ZMod 830051)^650 ≠ 1
          reduce_mod_char
          decide

theorem prime_833737 : Nat.Prime 833737 := by
  apply lucas_primality 833737 (5 : ZMod 833737)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 833737 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((34739 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 833737)^416868 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 833737)^277912 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 34739 := Nat.prime_eq_prime_of_dvd_pow hq prime_34739 hd
        subst q
        change (5 : ZMod 833737)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_835271 : Nat.Prime 835271 := by
  apply lucas_primality 835271 (23 : ZMod 835271)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 835271 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((101 : ℕ)^1 * ((827 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (23 : ZMod 835271)^417635 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (23 : ZMod 835271)^167054 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
          subst q
          change (23 : ZMod 835271)^8270 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 827 := Nat.prime_eq_prime_of_dvd_pow hq prime_827 hd
          subst q
          change (23 : ZMod 835271)^1010 ≠ 1
          reduce_mod_char
          decide

theorem prime_839771 : Nat.Prime 839771 := by
  apply lucas_primality 839771 (2 : ZMod 839771)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 839771 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((79 : ℕ)^1 * ((1063 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 839771)^419885 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 839771)^167954 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (2 : ZMod 839771)^10630 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1063 := Nat.prime_eq_prime_of_dvd_pow hq prime_1063 hd
          subst q
          change (2 : ZMod 839771)^790 ≠ 1
          reduce_mod_char
          decide

theorem prime_845879 : Nat.Prime 845879 := by
  apply lucas_primality 845879 (11 : ZMod 845879)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 845879 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((38449 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 845879)^422939 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (11 : ZMod 845879)^76898 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 38449 := Nat.prime_eq_prime_of_dvd_pow hq prime_38449 hd
        subst q
        change (11 : ZMod 845879)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_846647 : Nat.Prime 846647 := by
  apply lucas_primality 846647 (5 : ZMod 846647)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 846647 - 1 = (2 : ℕ)^1 * ((423323 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 846647)^423323 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 423323 := Nat.prime_eq_prime_of_dvd_pow hq prime_423323 hd
      subst q
      change (5 : ZMod 846647)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_846913 : Nat.Prime 846913 := by
  apply lucas_primality 846913 (5 : ZMod 846913)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 846913 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((401 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 846913)^423456 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 846913)^282304 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 846913)^76992 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 401 := Nat.prime_eq_prime_of_dvd_pow hq prime_401 hd
          subst q
          change (5 : ZMod 846913)^2112 ≠ 1
          reduce_mod_char
          decide

theorem prime_852013 : Nat.Prime 852013 := by
  apply lucas_primality 852013 (11 : ZMod 852013)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 852013 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((7 : ℕ)^3 * ((23 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 852013)^426006 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 852013)^284004 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (11 : ZMod 852013)^121716 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (11 : ZMod 852013)^37044 ≠ 1
          reduce_mod_char
          decide

theorem prime_854881 : Nat.Prime 854881 := by
  apply lucas_primality 854881 (14 : ZMod 854881)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 854881 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((137 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 854881)^427440 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 854881)^284960 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (14 : ZMod 854881)^170976 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (14 : ZMod 854881)^65760 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
            subst q
            change (14 : ZMod 854881)^6240 ≠ 1
            reduce_mod_char
            decide

theorem prime_856343 : Nat.Prime 856343 := by
  apply lucas_primality 856343 (5 : ZMod 856343)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 856343 - 1 = (2 : ℕ)^1 * ((103 : ℕ)^1 * ((4157 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 856343)^428171 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
        subst q
        change (5 : ZMod 856343)^8314 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4157 := Nat.prime_eq_prime_of_dvd_pow hq prime_4157 hd
        subst q
        change (5 : ZMod 856343)^206 ≠ 1
        reduce_mod_char
        decide

theorem prime_859363 : Nat.Prime 859363 := by
  apply lucas_primality 859363 (7 : ZMod 859363)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 859363 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((37 : ℕ)^1 * ((79 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 859363)^429681 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 859363)^286454 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 859363)^122766 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
            subst q
            change (7 : ZMod 859363)^23226 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
            subst q
            change (7 : ZMod 859363)^10878 ≠ 1
            reduce_mod_char
            decide

theorem prime_862331 : Nat.Prime 862331 := by
  apply lucas_primality 862331 (2 : ZMod 862331)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 862331 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((97 : ℕ)^1 * ((127 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 862331)^431165 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 862331)^172466 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 862331)^123190 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
            subst q
            change (2 : ZMod 862331)^8890 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
            subst q
            change (2 : ZMod 862331)^6790 ≠ 1
            reduce_mod_char
            decide

theorem prime_868051 : Nat.Prime 868051 := by
  apply lucas_primality 868051 (2 : ZMod 868051)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 868051 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((5 : ℕ)^2 * ((643 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 868051)^434025 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 868051)^289350 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 868051)^173610 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 643 := Nat.prime_eq_prime_of_dvd_pow hq prime_643 hd
          subst q
          change (2 : ZMod 868051)^1350 ≠ 1
          reduce_mod_char
          decide

theorem prime_871037 : Nat.Prime 871037 := by
  apply lucas_primality 871037 (2 : ZMod 871037)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 871037 - 1 = (2 : ℕ)^2 * ((19 : ℕ)^1 * ((73 : ℕ)^1 * ((157 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 871037)^435518 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 871037)^45844 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
          subst q
          change (2 : ZMod 871037)^11932 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
          subst q
          change (2 : ZMod 871037)^5548 ≠ 1
          reduce_mod_char
          decide

theorem prime_873293 : Nat.Prime 873293 := by
  apply lucas_primality 873293 (2 : ZMod 873293)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 873293 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((31189 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 873293)^436646 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 873293)^124756 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 31189 := Nat.prime_eq_prime_of_dvd_pow hq prime_31189 hd
        subst q
        change (2 : ZMod 873293)^28 ≠ 1
        reduce_mod_char
        decide

theorem prime_874109 : Nat.Prime 874109 := by
  apply lucas_primality 874109 (2 : ZMod 874109)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 874109 - 1 = (2 : ℕ)^2 * ((218527 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 874109)^437054 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 218527 := Nat.prime_eq_prime_of_dvd_pow hq prime_218527 hd
      subst q
      change (2 : ZMod 874109)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_874619 : Nat.Prime 874619 := by
  apply lucas_primality 874619 (2 : ZMod 874619)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 874619 - 1 = (2 : ℕ)^1 * ((61 : ℕ)^1 * ((67 : ℕ)^1 * ((107 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 874619)^437309 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
        subst q
        change (2 : ZMod 874619)^14338 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (2 : ZMod 874619)^13054 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
          subst q
          change (2 : ZMod 874619)^8174 ≠ 1
          reduce_mod_char
          decide

theorem prime_877837 : Nat.Prime 877837 := by
  apply lucas_primality 877837 (2 : ZMod 877837)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 877837 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((191 : ℕ)^1 * ((383 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 877837)^438918 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 877837)^292612 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
          subst q
          change (2 : ZMod 877837)^4596 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 383 := Nat.prime_eq_prime_of_dvd_pow hq prime_383 hd
          subst q
          change (2 : ZMod 877837)^2292 ≠ 1
          reduce_mod_char
          decide

theorem prime_881233 : Nat.Prime 881233 := by
  apply lucas_primality 881233 (7 : ZMod 881233)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 881233 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((1669 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 881233)^440616 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 881233)^293744 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (7 : ZMod 881233)^80112 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1669 := Nat.prime_eq_prime_of_dvd_pow hq prime_1669 hd
          subst q
          change (7 : ZMod 881233)^528 ≠ 1
          reduce_mod_char
          decide

theorem prime_883627 : Nat.Prime 883627 := by
  apply lucas_primality 883627 (3 : ZMod 883627)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 883627 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((8663 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 883627)^441813 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 883627)^294542 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (3 : ZMod 883627)^51978 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 8663 := Nat.prime_eq_prime_of_dvd_pow hq prime_8663 hd
          subst q
          change (3 : ZMod 883627)^102 ≠ 1
          reduce_mod_char
          decide

theorem prime_885509 : Nat.Prime 885509 := by
  apply lucas_primality 885509 (2 : ZMod 885509)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 885509 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((17029 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 885509)^442754 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 885509)^68116 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 17029 := Nat.prime_eq_prime_of_dvd_pow hq prime_17029 hd
        subst q
        change (2 : ZMod 885509)^52 ≠ 1
        reduce_mod_char
        decide

theorem prime_885803 : Nat.Prime 885803 := by
  apply lucas_primality 885803 (2 : ZMod 885803)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 885803 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((26053 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 885803)^442901 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 885803)^52106 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 26053 := Nat.prime_eq_prime_of_dvd_pow hq prime_26053 hd
        subst q
        change (2 : ZMod 885803)^34 ≠ 1
        reduce_mod_char
        decide

theorem prime_886511 : Nat.Prime 886511 := by
  apply lucas_primality 886511 (13 : ZMod 886511)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 886511 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((88651 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 886511)^443255 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (13 : ZMod 886511)^177302 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 88651 := Nat.prime_eq_prime_of_dvd_pow hq prime_88651 hd
        subst q
        change (13 : ZMod 886511)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_890867 : Nat.Prime 890867 := by
  apply lucas_primality 890867 (2 : ZMod 890867)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 890867 - 1 = (2 : ℕ)^1 * ((445433 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 890867)^445433 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 445433 := Nat.prime_eq_prime_of_dvd_pow hq prime_445433 hd
      subst q
      change (2 : ZMod 890867)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_891707 : Nat.Prime 891707 := by
  apply lucas_primality 891707 (2 : ZMod 891707)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 891707 - 1 = (2 : ℕ)^1 * ((445853 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 891707)^445853 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 445853 := Nat.prime_eq_prime_of_dvd_pow hq prime_445853 hd
      subst q
      change (2 : ZMod 891707)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_892579 : Nat.Prime 892579 := by
  apply lucas_primality 892579 (10 : ZMod 892579)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 892579 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((148763 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 892579)^446289 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 892579)^297526 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 148763 := Nat.prime_eq_prime_of_dvd_pow hq prime_148763 hd
        subst q
        change (10 : ZMod 892579)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_893567 : Nat.Prime 893567 := by
  apply lucas_primality 893567 (5 : ZMod 893567)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 893567 - 1 = (2 : ℕ)^1 * ((163 : ℕ)^1 * ((2741 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 893567)^446783 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
        subst q
        change (5 : ZMod 893567)^5482 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2741 := Nat.prime_eq_prime_of_dvd_pow hq prime_2741 hd
        subst q
        change (5 : ZMod 893567)^326 ≠ 1
        reduce_mod_char
        decide

theorem prime_895613 : Nat.Prime 895613 := by
  apply lucas_primality 895613 (2 : ZMod 895613)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 895613 - 1 = (2 : ℕ)^2 * ((223903 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 895613)^447806 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 223903 := Nat.prime_eq_prime_of_dvd_pow hq prime_223903 hd
      subst q
      change (2 : ZMod 895613)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_902659 : Nat.Prime 902659 := by
  apply lucas_primality 902659 (3 : ZMod 902659)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 902659 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((31 : ℕ)^1 * ((211 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 902659)^451329 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 902659)^300886 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (3 : ZMod 902659)^39246 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (3 : ZMod 902659)^29118 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 211 := Nat.prime_eq_prime_of_dvd_pow hq prime_211 hd
            subst q
            change (3 : ZMod 902659)^4278 ≠ 1
            reduce_mod_char
            decide

theorem prime_905621 : Nat.Prime 905621 := by
  apply lucas_primality 905621 (2 : ZMod 905621)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 905621 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((45281 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 905621)^452810 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 905621)^181124 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 45281 := Nat.prime_eq_prime_of_dvd_pow hq prime_45281 hd
        subst q
        change (2 : ZMod 905621)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_905963 : Nat.Prime 905963 := by
  apply lucas_primality 905963 (2 : ZMod 905963)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 905963 - 1 = (2 : ℕ)^1 * ((431 : ℕ)^1 * ((1051 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 905963)^452981 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 431 := Nat.prime_eq_prime_of_dvd_pow hq prime_431 hd
        subst q
        change (2 : ZMod 905963)^2102 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1051 := Nat.prime_eq_prime_of_dvd_pow hq prime_1051 hd
        subst q
        change (2 : ZMod 905963)^862 ≠ 1
        reduce_mod_char
        decide

theorem prime_906481 : Nat.Prime 906481 := by
  apply lucas_primality 906481 (17 : ZMod 906481)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 906481 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((1259 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 906481)^453240 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 906481)^302160 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (17 : ZMod 906481)^181296 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1259 := Nat.prime_eq_prime_of_dvd_pow hq prime_1259 hd
          subst q
          change (17 : ZMod 906481)^720 ≠ 1
          reduce_mod_char
          decide

theorem prime_911269 : Nat.Prime 911269 := by
  apply lucas_primality 911269 (2 : ZMod 911269)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 911269 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((17 : ℕ)^1 * ((1489 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 911269)^455634 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 911269)^303756 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 911269)^53604 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1489 := Nat.prime_eq_prime_of_dvd_pow hq prime_1489 hd
          subst q
          change (2 : ZMod 911269)^612 ≠ 1
          reduce_mod_char
          decide

theorem prime_913687 : Nat.Prime 913687 := by
  apply lucas_primality 913687 (3 : ZMod 913687)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 913687 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((197 : ℕ)^1 * ((773 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 913687)^456843 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 913687)^304562 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
          subst q
          change (3 : ZMod 913687)^4638 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 773 := Nat.prime_eq_prime_of_dvd_pow hq prime_773 hd
          subst q
          change (3 : ZMod 913687)^1182 ≠ 1
          reduce_mod_char
          decide

theorem prime_914321 : Nat.Prime 914321 := by
  apply lucas_primality 914321 (13 : ZMod 914321)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 914321 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((1039 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 914321)^457160 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (13 : ZMod 914321)^182864 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (13 : ZMod 914321)^83120 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1039 := Nat.prime_eq_prime_of_dvd_pow hq prime_1039 hd
          subst q
          change (13 : ZMod 914321)^880 ≠ 1
          reduce_mod_char
          decide

theorem prime_915391 : Nat.Prime 915391 := by
  apply lucas_primality 915391 (12 : ZMod 915391)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 915391 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((1453 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (12 : ZMod 915391)^457695 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (12 : ZMod 915391)^305130 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (12 : ZMod 915391)^183078 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (12 : ZMod 915391)^130770 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1453 := Nat.prime_eq_prime_of_dvd_pow hq prime_1453 hd
            subst q
            change (12 : ZMod 915391)^630 ≠ 1
            reduce_mod_char
            decide

theorem prime_918149 : Nat.Prime 918149 := by
  apply lucas_primality 918149 (10 : ZMod 918149)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 918149 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((11 : ℕ)^2 * ((271 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 918149)^459074 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (10 : ZMod 918149)^131164 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (10 : ZMod 918149)^83468 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 271 := Nat.prime_eq_prime_of_dvd_pow hq prime_271 hd
          subst q
          change (10 : ZMod 918149)^3388 ≠ 1
          reduce_mod_char
          decide

theorem prime_920641 : Nat.Prime 920641 := by
  apply lucas_primality 920641 (23 : ZMod 920641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 920641 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((137 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (23 : ZMod 920641)^460320 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (23 : ZMod 920641)^306880 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (23 : ZMod 920641)^184128 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (23 : ZMod 920641)^131520 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
            subst q
            change (23 : ZMod 920641)^6720 ≠ 1
            reduce_mod_char
            decide

theorem prime_921203 : Nat.Prime 921203 := by
  apply lucas_primality 921203 (2 : ZMod 921203)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 921203 - 1 = (2 : ℕ)^1 * ((317 : ℕ)^1 * ((1453 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 921203)^460601 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 317 := Nat.prime_eq_prime_of_dvd_pow hq prime_317 hd
        subst q
        change (2 : ZMod 921203)^2906 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1453 := Nat.prime_eq_prime_of_dvd_pow hq prime_1453 hd
        subst q
        change (2 : ZMod 921203)^634 ≠ 1
        reduce_mod_char
        decide

theorem prime_924421 : Nat.Prime 924421 := by
  apply lucas_primality 924421 (6 : ZMod 924421)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 924421 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((31 : ℕ)^1 * ((71 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 924421)^462210 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 924421)^308140 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 924421)^184884 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (6 : ZMod 924421)^132060 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
              subst q
              change (6 : ZMod 924421)^29820 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
              subst q
              change (6 : ZMod 924421)^13020 ≠ 1
              reduce_mod_char
              decide

theorem prime_925597 : Nat.Prime 925597 := by
  apply lucas_primality 925597 (5 : ZMod 925597)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 925597 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((3673 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 925597)^462798 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 925597)^308532 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 925597)^132228 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3673 := Nat.prime_eq_prime_of_dvd_pow hq prime_3673 hd
          subst q
          change (5 : ZMod 925597)^252 ≠ 1
          reduce_mod_char
          decide

theorem prime_925843 : Nat.Prime 925843 := by
  apply lucas_primality 925843 (5 : ZMod 925843)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 925843 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((6709 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 925843)^462921 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 925843)^308614 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (5 : ZMod 925843)^40254 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 6709 := Nat.prime_eq_prime_of_dvd_pow hq prime_6709 hd
          subst q
          change (5 : ZMod 925843)^138 ≠ 1
          reduce_mod_char
          decide

theorem prime_938129 : Nat.Prime 938129 := by
  apply lucas_primality 938129 (3 : ZMod 938129)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 938129 - 1 = (2 : ℕ)^4 * ((17 : ℕ)^1 * ((3449 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 938129)^469064 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (3 : ZMod 938129)^55184 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3449 := Nat.prime_eq_prime_of_dvd_pow hq prime_3449 hd
        subst q
        change (3 : ZMod 938129)^272 ≠ 1
        reduce_mod_char
        decide

theorem prime_940003 : Nat.Prime 940003 := by
  apply lucas_primality 940003 (3 : ZMod 940003)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 940003 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((22381 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 940003)^470001 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 940003)^313334 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 940003)^134286 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 22381 := Nat.prime_eq_prime_of_dvd_pow hq prime_22381 hd
          subst q
          change (3 : ZMod 940003)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_941741 : Nat.Prime 941741 := by
  apply lucas_primality 941741 (3 : ZMod 941741)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 941741 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((47087 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 941741)^470870 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 941741)^188348 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 47087 := Nat.prime_eq_prime_of_dvd_pow hq prime_47087 hd
        subst q
        change (3 : ZMod 941741)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_948053 : Nat.Prime 948053 := by
  apply lucas_primality 948053 (2 : ZMod 948053)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 948053 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^3 * ((691 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 948053)^474026 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 948053)^135436 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 691 := Nat.prime_eq_prime_of_dvd_pow hq prime_691 hd
        subst q
        change (2 : ZMod 948053)^1372 ≠ 1
        reduce_mod_char
        decide

theorem prime_948173 : Nat.Prime 948173 := by
  apply lucas_primality 948173 (2 : ZMod 948173)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 948173 - 1 = (2 : ℕ)^2 * ((237043 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 948173)^474086 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 237043 := Nat.prime_eq_prime_of_dvd_pow hq prime_237043 hd
      subst q
      change (2 : ZMod 948173)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_952169 : Nat.Prime 952169 := by
  apply lucas_primality 952169 (19 : ZMod 952169)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 952169 - 1 = (2 : ℕ)^3 * ((7 : ℕ)^3 * ((347 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 952169)^476084 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (19 : ZMod 952169)^136024 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 347 := Nat.prime_eq_prime_of_dvd_pow hq prime_347 hd
        subst q
        change (19 : ZMod 952169)^2744 ≠ 1
        reduce_mod_char
        decide

theorem prime_962837 : Nat.Prime 962837 := by
  apply lucas_primality 962837 (2 : ZMod 962837)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 962837 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((137 : ℕ)^1 * ((251 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 962837)^481418 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 962837)^137548 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
          subst q
          change (2 : ZMod 962837)^7028 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 251 := Nat.prime_eq_prime_of_dvd_pow hq prime_251 hd
          subst q
          change (2 : ZMod 962837)^3836 ≠ 1
          reduce_mod_char
          decide

theorem prime_965621 : Nat.Prime 965621 := by
  apply lucas_primality 965621 (3 : ZMod 965621)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 965621 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((48281 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 965621)^482810 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 965621)^193124 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 48281 := Nat.prime_eq_prime_of_dvd_pow hq prime_48281 hd
        subst q
        change (3 : ZMod 965621)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_975157 : Nat.Prime 975157 := by
  apply lucas_primality 975157 (2 : ZMod 975157)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 975157 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((19 : ℕ)^1 * ((47 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 975157)^487578 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 975157)^325052 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 975157)^139308 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (2 : ZMod 975157)^75012 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
              subst q
              change (2 : ZMod 975157)^51324 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
              subst q
              change (2 : ZMod 975157)^20748 ≠ 1
              reduce_mod_char
              decide

theorem prime_981091 : Nat.Prime 981091 := by
  apply lucas_primality 981091 (14 : ZMod 981091)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 981091 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((991 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 981091)^490545 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 981091)^327030 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (14 : ZMod 981091)^196218 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (14 : ZMod 981091)^89190 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 991 := Nat.prime_eq_prime_of_dvd_pow hq prime_991 hd
            subst q
            change (14 : ZMod 981091)^990 ≠ 1
            reduce_mod_char
            decide

theorem prime_990023 : Nat.Prime 990023 := by
  apply lucas_primality 990023 (5 : ZMod 990023)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 990023 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^2 * ((4091 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 990023)^495011 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 990023)^90002 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4091 := Nat.prime_eq_prime_of_dvd_pow hq prime_4091 hd
        subst q
        change (5 : ZMod 990023)^242 ≠ 1
        reduce_mod_char
        decide

theorem prime_995377 : Nat.Prime 995377 := by
  apply lucas_primality 995377 (5 : ZMod 995377)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 995377 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((89 : ℕ)^1 * ((233 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 995377)^497688 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 995377)^331792 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (5 : ZMod 995377)^11184 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
          subst q
          change (5 : ZMod 995377)^4272 ≠ 1
          reduce_mod_char
          decide

theorem prime_997891 : Nat.Prime 997891 := by
  apply lucas_primality 997891 (12 : ZMod 997891)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 997891 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((29 : ℕ)^1 * ((31 : ℕ)^1 * ((37 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (12 : ZMod 997891)^498945 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (12 : ZMod 997891)^332630 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (12 : ZMod 997891)^199578 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (12 : ZMod 997891)^34410 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
              subst q
              change (12 : ZMod 997891)^32190 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
              subst q
              change (12 : ZMod 997891)^26970 ≠ 1
              reduce_mod_char
              decide

theorem prime_1000003 : Nat.Prime 1000003 := by
  apply lucas_primality 1000003 (2 : ZMod 1000003)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1000003 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((166667 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1000003)^500001 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1000003)^333334 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 166667 := Nat.prime_eq_prime_of_dvd_pow hq prime_166667 hd
        subst q
        change (2 : ZMod 1000003)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_1003753 : Nat.Prime 1003753 := by
  apply lucas_primality 1003753 (10 : ZMod 1003753)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1003753 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^4 * ((1549 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 1003753)^501876 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 1003753)^334584 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1549 := Nat.prime_eq_prime_of_dvd_pow hq prime_1549 hd
        subst q
        change (10 : ZMod 1003753)^648 ≠ 1
        reduce_mod_char
        decide

theorem prime_1004977 : Nat.Prime 1004977 := by
  apply lucas_primality 1004977 (5 : ZMod 1004977)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1004977 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((997 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1004977)^502488 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1004977)^334992 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 1004977)^143568 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 997 := Nat.prime_eq_prime_of_dvd_pow hq prime_997 hd
          subst q
          change (5 : ZMod 1004977)^1008 ≠ 1
          reduce_mod_char
          decide

theorem prime_1031119 : Nat.Prime 1031119 := by
  apply lucas_primality 1031119 (3 : ZMod 1031119)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1031119 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((919 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1031119)^515559 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1031119)^343706 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 1031119)^93738 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (3 : ZMod 1031119)^60654 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 919 := Nat.prime_eq_prime_of_dvd_pow hq prime_919 hd
            subst q
            change (3 : ZMod 1031119)^1122 ≠ 1
            reduce_mod_char
            decide

theorem prime_1036039 : Nat.Prime 1036039 := by
  apply lucas_primality 1036039 (6 : ZMod 1036039)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1036039 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((172673 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 1036039)^518019 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 1036039)^345346 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 172673 := Nat.prime_eq_prime_of_dvd_pow hq prime_172673 hd
        subst q
        change (6 : ZMod 1036039)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_1041343 : Nat.Prime 1041343 := by
  apply lucas_primality 1041343 (3 : ZMod 1041343)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1041343 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((197 : ℕ)^1 * ((881 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1041343)^520671 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1041343)^347114 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
          subst q
          change (3 : ZMod 1041343)^5286 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 881 := Nat.prime_eq_prime_of_dvd_pow hq prime_881 hd
          subst q
          change (3 : ZMod 1041343)^1182 ≠ 1
          reduce_mod_char
          decide

theorem prime_1041671 : Nat.Prime 1041671 := by
  apply lucas_primality 1041671 (7 : ZMod 1041671)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1041671 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((23 : ℕ)^1 * ((647 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1041671)^520835 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 1041671)^208334 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 1041671)^148810 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (7 : ZMod 1041671)^45290 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 647 := Nat.prime_eq_prime_of_dvd_pow hq prime_647 hd
            subst q
            change (7 : ZMod 1041671)^1610 ≠ 1
            reduce_mod_char
            decide

theorem prime_1043543 : Nat.Prime 1043543 := by
  apply lucas_primality 1043543 (5 : ZMod 1043543)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1043543 - 1 = (2 : ℕ)^1 * ((313 : ℕ)^1 * ((1667 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1043543)^521771 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 313 := Nat.prime_eq_prime_of_dvd_pow hq prime_313 hd
        subst q
        change (5 : ZMod 1043543)^3334 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1667 := Nat.prime_eq_prime_of_dvd_pow hq prime_1667 hd
        subst q
        change (5 : ZMod 1043543)^626 ≠ 1
        reduce_mod_char
        decide

theorem prime_1043839 : Nat.Prime 1043839 := by
  apply lucas_primality 1043839 (3 : ZMod 1043839)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1043839 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((57991 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1043839)^521919 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1043839)^347946 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 57991 := Nat.prime_eq_prime_of_dvd_pow hq prime_57991 hd
        subst q
        change (3 : ZMod 1043839)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_1046627 : Nat.Prime 1046627 := by
  apply lucas_primality 1046627 (2 : ZMod 1046627)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1046627 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((74759 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1046627)^523313 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 1046627)^149518 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 74759 := Nat.prime_eq_prime_of_dvd_pow hq prime_74759 hd
        subst q
        change (2 : ZMod 1046627)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_1047391 : Nat.Prime 1047391 := by
  apply lucas_primality 1047391 (3 : ZMod 1047391)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1047391 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((34913 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1047391)^523695 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1047391)^349130 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 1047391)^209478 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 34913 := Nat.prime_eq_prime_of_dvd_pow hq prime_34913 hd
          subst q
          change (3 : ZMod 1047391)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_1047751 : Nat.Prime 1047751 := by
  apply lucas_primality 1047751 (3 : ZMod 1047751)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1047751 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^3 * ((11 : ℕ)^1 * ((127 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1047751)^523875 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1047751)^349250 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 1047751)^209550 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (3 : ZMod 1047751)^95250 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
            subst q
            change (3 : ZMod 1047751)^8250 ≠ 1
            reduce_mod_char
            decide

theorem prime_1054373 : Nat.Prime 1054373 := by
  apply lucas_primality 1054373 (2 : ZMod 1054373)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1054373 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((31 : ℕ)^1 * ((773 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1054373)^527186 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 1054373)^95852 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (2 : ZMod 1054373)^34012 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 773 := Nat.prime_eq_prime_of_dvd_pow hq prime_773 hd
          subst q
          change (2 : ZMod 1054373)^1364 ≠ 1
          reduce_mod_char
          decide

theorem prime_1060937 : Nat.Prime 1060937 := by
  apply lucas_primality 1060937 (3 : ZMod 1060937)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1060937 - 1 = (2 : ℕ)^3 * ((17 : ℕ)^1 * ((29 : ℕ)^1 * ((269 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1060937)^530468 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (3 : ZMod 1060937)^62408 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (3 : ZMod 1060937)^36584 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
          subst q
          change (3 : ZMod 1060937)^3944 ≠ 1
          reduce_mod_char
          decide

theorem prime_1061261 : Nat.Prime 1061261 := by
  apply lucas_primality 1061261 (2 : ZMod 1061261)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1061261 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((47 : ℕ)^1 * ((1129 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1061261)^530630 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 1061261)^212252 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (2 : ZMod 1061261)^22580 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1129 := Nat.prime_eq_prime_of_dvd_pow hq prime_1129 hd
          subst q
          change (2 : ZMod 1061261)^940 ≠ 1
          reduce_mod_char
          decide

theorem prime_1070423 : Nat.Prime 1070423 := by
  apply lucas_primality 1070423 (5 : ZMod 1070423)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1070423 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((19 : ℕ)^1 * ((1657 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1070423)^535211 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (5 : ZMod 1070423)^62966 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (5 : ZMod 1070423)^56338 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1657 := Nat.prime_eq_prime_of_dvd_pow hq prime_1657 hd
          subst q
          change (5 : ZMod 1070423)^646 ≠ 1
          reduce_mod_char
          decide

theorem prime_1072129 : Nat.Prime 1072129 := by
  apply lucas_primality 1072129 (13 : ZMod 1072129)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1072129 - 1 = (2 : ℕ)^10 * ((3 : ℕ)^1 * ((349 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 1072129)^536064 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 1072129)^357376 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 349 := Nat.prime_eq_prime_of_dvd_pow hq prime_349 hd
        subst q
        change (13 : ZMod 1072129)^3072 ≠ 1
        reduce_mod_char
        decide

theorem prime_1090909 : Nat.Prime 1090909 := by
  apply lucas_primality 1090909 (2 : ZMod 1090909)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1090909 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^4 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((37 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1090909)^545454 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1090909)^363636 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 1090909)^155844 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (2 : ZMod 1090909)^83916 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
            subst q
            change (2 : ZMod 1090909)^29484 ≠ 1
            reduce_mod_char
            decide

theorem prime_1108463 : Nat.Prime 1108463 := by
  apply lucas_primality 1108463 (5 : ZMod 1108463)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1108463 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((24097 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1108463)^554231 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (5 : ZMod 1108463)^48194 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 24097 := Nat.prime_eq_prime_of_dvd_pow hq prime_24097 hd
        subst q
        change (5 : ZMod 1108463)^46 ≠ 1
        reduce_mod_char
        decide

theorem prime_1111559 : Nat.Prime 1111559 := by
  apply lucas_primality 1111559 (7 : ZMod 1111559)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1111559 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((79397 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1111559)^555779 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 1111559)^158794 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 79397 := Nat.prime_eq_prime_of_dvd_pow hq prime_79397 hd
        subst q
        change (7 : ZMod 1111559)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_1114039 : Nat.Prime 1114039 := by
  apply lucas_primality 1114039 (6 : ZMod 1114039)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1114039 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((59 : ℕ)^1 * ((1049 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 1114039)^557019 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 1114039)^371346 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (6 : ZMod 1114039)^18882 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1049 := Nat.prime_eq_prime_of_dvd_pow hq prime_1049 hd
          subst q
          change (6 : ZMod 1114039)^1062 ≠ 1
          reduce_mod_char
          decide

theorem prime_1116937 : Nat.Prime 1116937 := by
  apply lucas_primality 1116937 (5 : ZMod 1116937)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1116937 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((5171 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1116937)^558468 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1116937)^372312 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5171 := Nat.prime_eq_prime_of_dvd_pow hq prime_5171 hd
        subst q
        change (5 : ZMod 1116937)^216 ≠ 1
        reduce_mod_char
        decide

theorem prime_1120369 : Nat.Prime 1120369 := by
  apply lucas_primality 1120369 (7 : ZMod 1120369)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1120369 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((1373 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1120369)^560184 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 1120369)^373456 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (7 : ZMod 1120369)^65904 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1373 := Nat.prime_eq_prime_of_dvd_pow hq prime_1373 hd
          subst q
          change (7 : ZMod 1120369)^816 ≠ 1
          reduce_mod_char
          decide

theorem prime_1122157 : Nat.Prime 1122157 := by
  apply lucas_primality 1122157 (6 : ZMod 1122157)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1122157 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((61 : ℕ)^1 * ((73 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 1122157)^561078 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 1122157)^374052 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 1122157)^160308 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
            subst q
            change (6 : ZMod 1122157)^18396 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
            subst q
            change (6 : ZMod 1122157)^15372 ≠ 1
            reduce_mod_char
            decide

theorem prime_1127101 : Nat.Prime 1127101 := by
  apply lucas_primality 1127101 (2 : ZMod 1127101)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1127101 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((13 : ℕ)^1 * ((17 : ℕ)^2)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1127101)^563550 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1127101)^375700 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 1127101)^225420 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (2 : ZMod 1127101)^86700 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (2 : ZMod 1127101)^66300 ≠ 1
            reduce_mod_char
            decide

theorem prime_1142923 : Nat.Prime 1142923 := by
  apply lucas_primality 1142923 (2 : ZMod 1142923)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1142923 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((17317 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1142923)^571461 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1142923)^380974 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 1142923)^103902 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17317 := Nat.prime_eq_prime_of_dvd_pow hq prime_17317 hd
          subst q
          change (2 : ZMod 1142923)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_1143091 : Nat.Prime 1143091 := by
  apply lucas_primality 1143091 (12 : ZMod 1143091)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1143091 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((977 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (12 : ZMod 1143091)^571545 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (12 : ZMod 1143091)^381030 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (12 : ZMod 1143091)^228618 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (12 : ZMod 1143091)^87930 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 977 := Nat.prime_eq_prime_of_dvd_pow hq prime_977 hd
            subst q
            change (12 : ZMod 1143091)^1170 ≠ 1
            reduce_mod_char
            decide

theorem prime_1154017 : Nat.Prime 1154017 := by
  apply lucas_primality 1154017 (5 : ZMod 1154017)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1154017 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^2 * ((4007 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1154017)^577008 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1154017)^384672 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4007 := Nat.prime_eq_prime_of_dvd_pow hq prime_4007 hd
        subst q
        change (5 : ZMod 1154017)^288 ≠ 1
        reduce_mod_char
        decide

theorem prime_1154551 : Nat.Prime 1154551 := by
  apply lucas_primality 1154551 (3 : ZMod 1154551)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1154551 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((43 : ℕ)^1 * ((179 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1154551)^577275 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1154551)^384850 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 1154551)^230910 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (3 : ZMod 1154551)^26850 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 179 := Nat.prime_eq_prime_of_dvd_pow hq prime_179 hd
            subst q
            change (3 : ZMod 1154551)^6450 ≠ 1
            reduce_mod_char
            decide

theorem prime_1155169 : Nat.Prime 1155169 := by
  apply lucas_primality 1155169 (13 : ZMod 1155169)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1155169 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((191 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 1155169)^577584 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 1155169)^385056 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (13 : ZMod 1155169)^165024 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
          subst q
          change (13 : ZMod 1155169)^6048 ≠ 1
          reduce_mod_char
          decide

theorem prime_1162649 : Nat.Prime 1162649 := by
  apply lucas_primality 1162649 (3 : ZMod 1162649)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1162649 - 1 = (2 : ℕ)^3 * ((19 : ℕ)^1 * ((7649 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1162649)^581324 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (3 : ZMod 1162649)^61192 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7649 := Nat.prime_eq_prime_of_dvd_pow hq prime_7649 hd
        subst q
        change (3 : ZMod 1162649)^152 ≠ 1
        reduce_mod_char
        decide

theorem prime_1168319 : Nat.Prime 1168319 := by
  apply lucas_primality 1168319 (11 : ZMod 1168319)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1168319 - 1 = (2 : ℕ)^1 * ((59 : ℕ)^1 * ((9901 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 1168319)^584159 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
        subst q
        change (11 : ZMod 1168319)^19802 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 9901 := Nat.prime_eq_prime_of_dvd_pow hq prime_9901 hd
        subst q
        change (11 : ZMod 1168319)^118 ≠ 1
        reduce_mod_char
        decide

theorem prime_1171619 : Nat.Prime 1171619 := by
  apply lucas_primality 1171619 (2 : ZMod 1171619)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1171619 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((53 : ℕ)^1 * ((1579 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1171619)^585809 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 1171619)^167374 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (2 : ZMod 1171619)^22106 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1579 := Nat.prime_eq_prime_of_dvd_pow hq prime_1579 hd
          subst q
          change (2 : ZMod 1171619)^742 ≠ 1
          reduce_mod_char
          decide

theorem prime_1175249 : Nat.Prime 1175249 := by
  apply lucas_primality 1175249 (3 : ZMod 1175249)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1175249 - 1 = (2 : ℕ)^4 * ((73453 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1175249)^587624 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 73453 := Nat.prime_eq_prime_of_dvd_pow hq prime_73453 hd
      subst q
      change (3 : ZMod 1175249)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_1196309 : Nat.Prime 1196309 := by
  apply lucas_primality 1196309 (2 : ZMod 1196309)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1196309 - 1 = (2 : ℕ)^2 * ((29 : ℕ)^1 * ((10313 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1196309)^598154 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (2 : ZMod 1196309)^41252 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 10313 := Nat.prime_eq_prime_of_dvd_pow hq prime_10313 hd
        subst q
        change (2 : ZMod 1196309)^116 ≠ 1
        reduce_mod_char
        decide

theorem prime_1204519 : Nat.Prime 1204519 := by
  apply lucas_primality 1204519 (6 : ZMod 1204519)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1204519 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((17 : ℕ)^1 * ((241 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 1204519)^602259 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 1204519)^401506 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 1204519)^172074 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (6 : ZMod 1204519)^70854 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 241 := Nat.prime_eq_prime_of_dvd_pow hq prime_241 hd
            subst q
            change (6 : ZMod 1204519)^4998 ≠ 1
            reduce_mod_char
            decide

theorem prime_1206703 : Nat.Prime 1206703 := by
  apply lucas_primality 1206703 (7 : ZMod 1206703)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1206703 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((61 : ℕ)^1 * ((157 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1206703)^603351 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 1206703)^402234 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 1206703)^172386 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
            subst q
            change (7 : ZMod 1206703)^19782 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
            subst q
            change (7 : ZMod 1206703)^7686 ≠ 1
            reduce_mod_char
            decide

theorem prime_1211911 : Nat.Prime 1211911 := by
  apply lucas_primality 1211911 (6 : ZMod 1211911)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1211911 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((29 : ℕ)^1 * ((199 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 1211911)^605955 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 1211911)^403970 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 1211911)^242382 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (6 : ZMod 1211911)^173130 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
              subst q
              change (6 : ZMod 1211911)^41790 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 199 := Nat.prime_eq_prime_of_dvd_pow hq prime_199 hd
              subst q
              change (6 : ZMod 1211911)^6090 ≠ 1
              reduce_mod_char
              decide

theorem prime_1216711 : Nat.Prime 1216711 := by
  apply lucas_primality 1216711 (13 : ZMod 1216711)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1216711 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((1229 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 1216711)^608355 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 1216711)^405570 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 1216711)^243342 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (13 : ZMod 1216711)^110610 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1229 := Nat.prime_eq_prime_of_dvd_pow hq prime_1229 hd
            subst q
            change (13 : ZMod 1216711)^990 ≠ 1
            reduce_mod_char
            decide

theorem prime_1217947 : Nat.Prime 1217947 := by
  apply lucas_primality 1217947 (2 : ZMod 1217947)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1217947 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((41 : ℕ)^1 * ((4951 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1217947)^608973 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1217947)^405982 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (2 : ZMod 1217947)^29706 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4951 := Nat.prime_eq_prime_of_dvd_pow hq prime_4951 hd
          subst q
          change (2 : ZMod 1217947)^246 ≠ 1
          reduce_mod_char
          decide

theorem prime_1230743 : Nat.Prime 1230743 := by
  apply lucas_primality 1230743 (5 : ZMod 1230743)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1230743 - 1 = (2 : ℕ)^1 * ((47 : ℕ)^1 * ((13093 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1230743)^615371 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (5 : ZMod 1230743)^26186 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13093 := Nat.prime_eq_prime_of_dvd_pow hq prime_13093 hd
        subst q
        change (5 : ZMod 1230743)^94 ≠ 1
        reduce_mod_char
        decide

theorem prime_1246573 : Nat.Prime 1246573 := by
  apply lucas_primality 1246573 (5 : ZMod 1246573)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1246573 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((31 : ℕ)^1 * ((1117 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1246573)^623286 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1246573)^415524 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (5 : ZMod 1246573)^40212 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1117 := Nat.prime_eq_prime_of_dvd_pow hq prime_1117 hd
          subst q
          change (5 : ZMod 1246573)^1116 ≠ 1
          reduce_mod_char
          decide

theorem prime_1269643 : Nat.Prime 1269643 := by
  apply lucas_primality 1269643 (3 : ZMod 1269643)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1269643 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((19237 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1269643)^634821 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1269643)^423214 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 1269643)^115422 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 19237 := Nat.prime_eq_prime_of_dvd_pow hq prime_19237 hd
          subst q
          change (3 : ZMod 1269643)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_1273739 : Nat.Prime 1273739 := by
  apply lucas_primality 1273739 (2 : ZMod 1273739)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1273739 - 1 = (2 : ℕ)^1 * ((29 : ℕ)^1 * ((21961 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1273739)^636869 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (2 : ZMod 1273739)^43922 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 21961 := Nat.prime_eq_prime_of_dvd_pow hq prime_21961 hd
        subst q
        change (2 : ZMod 1273739)^58 ≠ 1
        reduce_mod_char
        decide

theorem prime_1286629 : Nat.Prime 1286629 := by
  apply lucas_primality 1286629 (6 : ZMod 1286629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1286629 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((17 : ℕ)^2 * ((53 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 1286629)^643314 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 1286629)^428876 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 1286629)^183804 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (6 : ZMod 1286629)^75684 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
            subst q
            change (6 : ZMod 1286629)^24276 ≠ 1
            reduce_mod_char
            decide

theorem prime_1299317 : Nat.Prime 1299317 := by
  apply lucas_primality 1299317 (2 : ZMod 1299317)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1299317 - 1 = (2 : ℕ)^2 * ((23 : ℕ)^1 * ((29 : ℕ)^1 * ((487 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1299317)^649658 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (2 : ZMod 1299317)^56492 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (2 : ZMod 1299317)^44804 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 487 := Nat.prime_eq_prime_of_dvd_pow hq prime_487 hd
          subst q
          change (2 : ZMod 1299317)^2668 ≠ 1
          reduce_mod_char
          decide

theorem prime_1303823 : Nat.Prime 1303823 := by
  apply lucas_primality 1303823 (10 : ZMod 1303823)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1303823 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((50147 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 1303823)^651911 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (10 : ZMod 1303823)^100294 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 50147 := Nat.prime_eq_prime_of_dvd_pow hq prime_50147 hd
        subst q
        change (10 : ZMod 1303823)^26 ≠ 1
        reduce_mod_char
        decide

theorem prime_1306159 : Nat.Prime 1306159 := by
  apply lucas_primality 1306159 (7 : ZMod 1306159)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1306159 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((137 : ℕ)^1 * ((227 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1306159)^653079 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 1306159)^435386 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 1306159)^186594 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
            subst q
            change (7 : ZMod 1306159)^9534 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 227 := Nat.prime_eq_prime_of_dvd_pow hq prime_227 hd
            subst q
            change (7 : ZMod 1306159)^5754 ≠ 1
            reduce_mod_char
            decide

theorem prime_1308499 : Nat.Prime 1308499 := by
  apply lucas_primality 1308499 (2 : ZMod 1308499)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1308499 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((218083 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1308499)^654249 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1308499)^436166 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 218083 := Nat.prime_eq_prime_of_dvd_pow hq prime_218083 hd
        subst q
        change (2 : ZMod 1308499)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_1319869 : Nat.Prime 1319869 := by
  apply lucas_primality 1319869 (2 : ZMod 1319869)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1319869 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((11 : ℕ)^2 * ((101 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1319869)^659934 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1319869)^439956 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 1319869)^119988 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
          subst q
          change (2 : ZMod 1319869)^13068 ≠ 1
          reduce_mod_char
          decide

theorem prime_1326683 : Nat.Prime 1326683 := by
  apply lucas_primality 1326683 (2 : ZMod 1326683)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1326683 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((193 : ℕ)^1 * ((491 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1326683)^663341 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 1326683)^189526 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
          subst q
          change (2 : ZMod 1326683)^6874 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 491 := Nat.prime_eq_prime_of_dvd_pow hq prime_491 hd
          subst q
          change (2 : ZMod 1326683)^2702 ≠ 1
          reduce_mod_char
          decide

theorem prime_1335259 : Nat.Prime 1335259 := by
  apply lucas_primality 1335259 (2 : ZMod 1335259)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1335259 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((79 : ℕ)^1 * ((313 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1335259)^667629 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1335259)^445086 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (2 : ZMod 1335259)^16902 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 313 := Nat.prime_eq_prime_of_dvd_pow hq prime_313 hd
          subst q
          change (2 : ZMod 1335259)^4266 ≠ 1
          reduce_mod_char
          decide

theorem prime_1338499 : Nat.Prime 1338499 := by
  apply lucas_primality 1338499 (2 : ZMod 1338499)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1338499 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((3541 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1338499)^669249 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1338499)^446166 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 1338499)^191214 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3541 := Nat.prime_eq_prime_of_dvd_pow hq prime_3541 hd
          subst q
          change (2 : ZMod 1338499)^378 ≠ 1
          reduce_mod_char
          decide

theorem prime_1350317 : Nat.Prime 1350317 := by
  apply lucas_primality 1350317 (2 : ZMod 1350317)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1350317 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((30689 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1350317)^675158 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 1350317)^122756 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 30689 := Nat.prime_eq_prime_of_dvd_pow hq prime_30689 hd
        subst q
        change (2 : ZMod 1350317)^44 ≠ 1
        reduce_mod_char
        decide

theorem prime_1351853 : Nat.Prime 1351853 := by
  apply lucas_primality 1351853 (2 : ZMod 1351853)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1351853 - 1 = (2 : ℕ)^2 * ((41 : ℕ)^1 * ((8243 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1351853)^675926 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
        subst q
        change (2 : ZMod 1351853)^32972 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 8243 := Nat.prime_eq_prime_of_dvd_pow hq prime_8243 hd
        subst q
        change (2 : ZMod 1351853)^164 ≠ 1
        reduce_mod_char
        decide

theorem prime_1367101 : Nat.Prime 1367101 := by
  apply lucas_primality 1367101 (2 : ZMod 1367101)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1367101 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^2 * ((7 : ℕ)^2 * ((31 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1367101)^683550 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1367101)^455700 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 1367101)^273420 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (2 : ZMod 1367101)^195300 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (2 : ZMod 1367101)^44100 ≠ 1
            reduce_mod_char
            decide

theorem prime_1369229 : Nat.Prime 1369229 := by
  apply lucas_primality 1369229 (3 : ZMod 1369229)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1369229 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((79 : ℕ)^1 * ((619 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1369229)^684614 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 1369229)^195604 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (3 : ZMod 1369229)^17332 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 619 := Nat.prime_eq_prime_of_dvd_pow hq prime_619 hd
          subst q
          change (3 : ZMod 1369229)^2212 ≠ 1
          reduce_mod_char
          decide

theorem prime_1369559 : Nat.Prime 1369559 := by
  apply lucas_primality 1369559 (7 : ZMod 1369559)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1369559 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((23 : ℕ)^1 * ((1567 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1369559)^684779 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (7 : ZMod 1369559)^72082 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (7 : ZMod 1369559)^59546 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1567 := Nat.prime_eq_prime_of_dvd_pow hq prime_1567 hd
          subst q
          change (7 : ZMod 1369559)^874 ≠ 1
          reduce_mod_char
          decide

theorem prime_1372127 : Nat.Prime 1372127 := by
  apply lucas_primality 1372127 (7 : ZMod 1372127)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1372127 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((98009 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1372127)^686063 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 1372127)^196018 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 98009 := Nat.prime_eq_prime_of_dvd_pow hq prime_98009 hd
        subst q
        change (7 : ZMod 1372127)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_1384813 : Nat.Prime 1384813 := by
  apply lucas_primality 1384813 (5 : ZMod 1384813)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1384813 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((269 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1384813)^692406 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1384813)^461604 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 1384813)^125892 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (5 : ZMod 1384813)^106524 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
            subst q
            change (5 : ZMod 1384813)^5148 ≠ 1
            reduce_mod_char
            decide

theorem prime_1388623 : Nat.Prime 1388623 := by
  apply lucas_primality 1388623 (3 : ZMod 1388623)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1388623 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((199 : ℕ)^1 * ((1163 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1388623)^694311 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1388623)^462874 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 199 := Nat.prime_eq_prime_of_dvd_pow hq prime_199 hd
          subst q
          change (3 : ZMod 1388623)^6978 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1163 := Nat.prime_eq_prime_of_dvd_pow hq prime_1163 hd
          subst q
          change (3 : ZMod 1388623)^1194 ≠ 1
          reduce_mod_char
          decide

theorem prime_1394711 : Nat.Prime 1394711 := by
  apply lucas_primality 1394711 (26 : ZMod 1394711)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1394711 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((211 : ℕ)^1 * ((661 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (26 : ZMod 1394711)^697355 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (26 : ZMod 1394711)^278942 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 211 := Nat.prime_eq_prime_of_dvd_pow hq prime_211 hd
          subst q
          change (26 : ZMod 1394711)^6610 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 661 := Nat.prime_eq_prime_of_dvd_pow hq prime_661 hd
          subst q
          change (26 : ZMod 1394711)^2110 ≠ 1
          reduce_mod_char
          decide

theorem prime_1396987 : Nat.Prime 1396987 := by
  apply lucas_primality 1396987 (2 : ZMod 1396987)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1396987 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((157 : ℕ)^1 * ((1483 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1396987)^698493 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1396987)^465662 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
          subst q
          change (2 : ZMod 1396987)^8898 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1483 := Nat.prime_eq_prime_of_dvd_pow hq prime_1483 hd
          subst q
          change (2 : ZMod 1396987)^942 ≠ 1
          reduce_mod_char
          decide

theorem prime_1400039 : Nat.Prime 1400039 := by
  apply lucas_primality 1400039 (7 : ZMod 1400039)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1400039 - 1 = (2 : ℕ)^1 * ((79 : ℕ)^1 * ((8861 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1400039)^700019 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
        subst q
        change (7 : ZMod 1400039)^17722 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 8861 := Nat.prime_eq_prime_of_dvd_pow hq prime_8861 hd
        subst q
        change (7 : ZMod 1400039)^158 ≠ 1
        reduce_mod_char
        decide

theorem prime_1404283 : Nat.Prime 1404283 := by
  apply lucas_primality 1404283 (2 : ZMod 1404283)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1404283 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((21277 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1404283)^702141 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1404283)^468094 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 1404283)^127662 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 21277 := Nat.prime_eq_prime_of_dvd_pow hq prime_21277 hd
          subst q
          change (2 : ZMod 1404283)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_1404937 : Nat.Prime 1404937 := by
  apply lucas_primality 1404937 (5 : ZMod 1404937)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1404937 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((13 : ℕ)^1 * ((19 : ℕ)^1 * ((79 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1404937)^702468 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1404937)^468312 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (5 : ZMod 1404937)^108072 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (5 : ZMod 1404937)^73944 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
            subst q
            change (5 : ZMod 1404937)^17784 ≠ 1
            reduce_mod_char
            decide

theorem prime_1415317 : Nat.Prime 1415317 := by
  apply lucas_primality 1415317 (2 : ZMod 1415317)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1415317 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((29 : ℕ)^1 * ((83 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1415317)^707658 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1415317)^471772 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 1415317)^202188 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (2 : ZMod 1415317)^48804 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
            subst q
            change (2 : ZMod 1415317)^17052 ≠ 1
            reduce_mod_char
            decide

theorem prime_1417189 : Nat.Prime 1417189 := by
  apply lucas_primality 1417189 (2 : ZMod 1417189)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1417189 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((6947 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1417189)^708594 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1417189)^472396 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 1417189)^83364 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 6947 := Nat.prime_eq_prime_of_dvd_pow hq prime_6947 hd
          subst q
          change (2 : ZMod 1417189)^204 ≠ 1
          reduce_mod_char
          decide

theorem prime_1427221 : Nat.Prime 1427221 := by
  apply lucas_primality 1427221 (6 : ZMod 1427221)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1427221 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^4 * ((5 : ℕ)^1 * ((881 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 1427221)^713610 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 1427221)^475740 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 1427221)^285444 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 881 := Nat.prime_eq_prime_of_dvd_pow hq prime_881 hd
          subst q
          change (6 : ZMod 1427221)^1620 ≠ 1
          reduce_mod_char
          decide

theorem prime_1436999 : Nat.Prime 1436999 := by
  apply lucas_primality 1436999 (7 : ZMod 1436999)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1436999 - 1 = (2 : ℕ)^1 * ((269 : ℕ)^1 * ((2671 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1436999)^718499 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
        subst q
        change (7 : ZMod 1436999)^5342 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2671 := Nat.prime_eq_prime_of_dvd_pow hq prime_2671 hd
        subst q
        change (7 : ZMod 1436999)^538 ≠ 1
        reduce_mod_char
        decide

theorem prime_1441201 : Nat.Prime 1441201 := by
  apply lucas_primality 1441201 (7 : ZMod 1441201)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1441201 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((1201 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1441201)^720600 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 1441201)^480400 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 1441201)^288240 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1201 := Nat.prime_eq_prime_of_dvd_pow hq prime_1201 hd
          subst q
          change (7 : ZMod 1441201)^1200 ≠ 1
          reduce_mod_char
          decide

theorem prime_1457083 : Nat.Prime 1457083 := by
  apply lucas_primality 1457083 (3 : ZMod 1457083)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1457083 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((11 : ℕ)^2 * ((223 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1457083)^728541 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1457083)^485694 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 1457083)^132462 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 223 := Nat.prime_eq_prime_of_dvd_pow hq prime_223 hd
          subst q
          change (3 : ZMod 1457083)^6534 ≠ 1
          reduce_mod_char
          decide

theorem prime_1470727 : Nat.Prime 1470727 := by
  apply lucas_primality 1470727 (3 : ZMod 1470727)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1470727 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((81707 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1470727)^735363 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1470727)^490242 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 81707 := Nat.prime_eq_prime_of_dvd_pow hq prime_81707 hd
        subst q
        change (3 : ZMod 1470727)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_1470839 : Nat.Prime 1470839 := by
  apply lucas_primality 1470839 (13 : ZMod 1470839)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1470839 - 1 = (2 : ℕ)^1 * ((735419 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 1470839)^735419 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 735419 := Nat.prime_eq_prime_of_dvd_pow hq prime_735419 hd
      subst q
      change (13 : ZMod 1470839)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_1472467 : Nat.Prime 1472467 := by
  apply lucas_primality 1472467 (3 : ZMod 1472467)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1472467 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((245411 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1472467)^736233 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1472467)^490822 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 245411 := Nat.prime_eq_prime_of_dvd_pow hq prime_245411 hd
        subst q
        change (3 : ZMod 1472467)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_1485017 : Nat.Prime 1485017 := by
  apply lucas_primality 1485017 (3 : ZMod 1485017)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1485017 - 1 = (2 : ℕ)^3 * ((13 : ℕ)^1 * ((109 : ℕ)^1 * ((131 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1485017)^742508 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 1485017)^114232 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
          subst q
          change (3 : ZMod 1485017)^13624 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
          subst q
          change (3 : ZMod 1485017)^11336 ≠ 1
          reduce_mod_char
          decide

theorem prime_1488869 : Nat.Prime 1488869 := by
  apply lucas_primality 1488869 (2 : ZMod 1488869)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1488869 - 1 = (2 : ℕ)^2 * ((31 : ℕ)^1 * ((12007 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1488869)^744434 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (2 : ZMod 1488869)^48028 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 12007 := Nat.prime_eq_prime_of_dvd_pow hq prime_12007 hd
        subst q
        change (2 : ZMod 1488869)^124 ≠ 1
        reduce_mod_char
        decide

theorem prime_1521913 : Nat.Prime 1521913 := by
  apply lucas_primality 1521913 (5 : ZMod 1521913)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1521913 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((9059 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1521913)^760956 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1521913)^507304 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 1521913)^217416 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 9059 := Nat.prime_eq_prime_of_dvd_pow hq prime_9059 hd
          subst q
          change (5 : ZMod 1521913)^168 ≠ 1
          reduce_mod_char
          decide

theorem prime_1550173 : Nat.Prime 1550173 := by
  apply lucas_primality 1550173 (2 : ZMod 1550173)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1550173 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((19 : ℕ)^1 * ((523 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1550173)^775086 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1550173)^516724 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 1550173)^119244 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (2 : ZMod 1550173)^81588 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 523 := Nat.prime_eq_prime_of_dvd_pow hq prime_523 hd
            subst q
            change (2 : ZMod 1550173)^2964 ≠ 1
            reduce_mod_char
            decide

theorem prime_1555129 : Nat.Prime 1555129 := by
  apply lucas_primality 1555129 (17 : ZMod 1555129)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1555129 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((21599 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 1555129)^777564 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 1555129)^518376 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 21599 := Nat.prime_eq_prime_of_dvd_pow hq prime_21599 hd
        subst q
        change (17 : ZMod 1555129)^72 ≠ 1
        reduce_mod_char
        decide

theorem prime_1557313 : Nat.Prime 1557313 := by
  apply lucas_primality 1557313 (10 : ZMod 1557313)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1557313 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^1 * ((8111 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 1557313)^778656 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 1557313)^519104 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 8111 := Nat.prime_eq_prime_of_dvd_pow hq prime_8111 hd
        subst q
        change (10 : ZMod 1557313)^192 ≠ 1
        reduce_mod_char
        decide

theorem prime_1557509 : Nat.Prime 1557509 := by
  apply lucas_primality 1557509 (2 : ZMod 1557509)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1557509 - 1 = (2 : ℕ)^2 * ((41 : ℕ)^1 * ((9497 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1557509)^778754 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
        subst q
        change (2 : ZMod 1557509)^37988 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 9497 := Nat.prime_eq_prime_of_dvd_pow hq prime_9497 hd
        subst q
        change (2 : ZMod 1557509)^164 ≠ 1
        reduce_mod_char
        decide

theorem prime_1579597 : Nat.Prime 1579597 := by
  apply lucas_primality 1579597 (2 : ZMod 1579597)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1579597 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((139 : ℕ)^1 * ((947 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1579597)^789798 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1579597)^526532 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
          subst q
          change (2 : ZMod 1579597)^11364 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 947 := Nat.prime_eq_prime_of_dvd_pow hq prime_947 hd
          subst q
          change (2 : ZMod 1579597)^1668 ≠ 1
          reduce_mod_char
          decide

theorem prime_1581743 : Nat.Prime 1581743 := by
  apply lucas_primality 1581743 (5 : ZMod 1581743)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1581743 - 1 = (2 : ℕ)^1 * ((790871 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1581743)^790871 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 790871 := Nat.prime_eq_prime_of_dvd_pow hq prime_790871 hd
      subst q
      change (5 : ZMod 1581743)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_1595339 : Nat.Prime 1595339 := by
  apply lucas_primality 1595339 (2 : ZMod 1595339)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1595339 - 1 = (2 : ℕ)^1 * ((193 : ℕ)^1 * ((4133 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1595339)^797669 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
        subst q
        change (2 : ZMod 1595339)^8266 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4133 := Nat.prime_eq_prime_of_dvd_pow hq prime_4133 hd
        subst q
        change (2 : ZMod 1595339)^386 ≠ 1
        reduce_mod_char
        decide

theorem prime_1614413 : Nat.Prime 1614413 := by
  apply lucas_primality 1614413 (2 : ZMod 1614413)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1614413 - 1 = (2 : ℕ)^2 * ((403603 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1614413)^807206 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 403603 := Nat.prime_eq_prime_of_dvd_pow hq prime_403603 hd
      subst q
      change (2 : ZMod 1614413)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_1614733 : Nat.Prime 1614733 := by
  apply lucas_primality 1614733 (2 : ZMod 1614733)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1614733 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((47 : ℕ)^1 * ((409 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1614733)^807366 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1614733)^538244 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 1614733)^230676 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
            subst q
            change (2 : ZMod 1614733)^34356 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 409 := Nat.prime_eq_prime_of_dvd_pow hq prime_409 hd
            subst q
            change (2 : ZMod 1614733)^3948 ≠ 1
            reduce_mod_char
            decide

theorem prime_1615723 : Nat.Prime 1615723 := by
  apply lucas_primality 1615723 (3 : ZMod 1615723)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1615723 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((14173 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1615723)^807861 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1615723)^538574 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (3 : ZMod 1615723)^85038 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 14173 := Nat.prime_eq_prime_of_dvd_pow hq prime_14173 hd
          subst q
          change (3 : ZMod 1615723)^114 ≠ 1
          reduce_mod_char
          decide

theorem prime_1646989 : Nat.Prime 1646989 := by
  apply lucas_primality 1646989 (17 : ZMod 1646989)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1646989 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((2801 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 1646989)^823494 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 1646989)^548996 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (17 : ZMod 1646989)^235284 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2801 := Nat.prime_eq_prime_of_dvd_pow hq prime_2801 hd
          subst q
          change (17 : ZMod 1646989)^588 ≠ 1
          reduce_mod_char
          decide

theorem prime_1660103 : Nat.Prime 1660103 := by
  apply lucas_primality 1660103 (5 : ZMod 1660103)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1660103 - 1 = (2 : ℕ)^1 * ((830051 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1660103)^830051 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 830051 := Nat.prime_eq_prime_of_dvd_pow hq prime_830051 hd
      subst q
      change (5 : ZMod 1660103)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_1677359 : Nat.Prime 1677359 := by
  apply lucas_primality 1677359 (13 : ZMod 1677359)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1677359 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((37 : ℕ)^1 * ((1193 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 1677359)^838679 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (13 : ZMod 1677359)^88282 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (13 : ZMod 1677359)^45334 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1193 := Nat.prime_eq_prime_of_dvd_pow hq prime_1193 hd
          subst q
          change (13 : ZMod 1677359)^1406 ≠ 1
          reduce_mod_char
          decide

theorem prime_1685473 : Nat.Prime 1685473 := by
  apply lucas_primality 1685473 (10 : ZMod 1685473)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1685473 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((97 : ℕ)^1 * ((181 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 1685473)^842736 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 1685473)^561824 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
          subst q
          change (10 : ZMod 1685473)^17376 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 181 := Nat.prime_eq_prime_of_dvd_pow hq prime_181 hd
          subst q
          change (10 : ZMod 1685473)^9312 ≠ 1
          reduce_mod_char
          decide

theorem prime_1694191 : Nat.Prime 1694191 := by
  apply lucas_primality 1694191 (7 : ZMod 1694191)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1694191 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((56473 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1694191)^847095 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 1694191)^564730 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 1694191)^338838 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 56473 := Nat.prime_eq_prime_of_dvd_pow hq prime_56473 hd
          subst q
          change (7 : ZMod 1694191)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_1694599 : Nat.Prime 1694599 := by
  apply lucas_primality 1694599 (6 : ZMod 1694599)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1694599 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((59 : ℕ)^1 * ((4787 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 1694599)^847299 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 1694599)^564866 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (6 : ZMod 1694599)^28722 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4787 := Nat.prime_eq_prime_of_dvd_pow hq prime_4787 hd
          subst q
          change (6 : ZMod 1694599)^354 ≠ 1
          reduce_mod_char
          decide

theorem prime_1718567 : Nat.Prime 1718567 := by
  apply lucas_primality 1718567 (5 : ZMod 1718567)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1718567 - 1 = (2 : ℕ)^1 * ((73 : ℕ)^1 * ((79 : ℕ)^1 * ((149 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1718567)^859283 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
        subst q
        change (5 : ZMod 1718567)^23542 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (5 : ZMod 1718567)^21754 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
          subst q
          change (5 : ZMod 1718567)^11534 ≠ 1
          reduce_mod_char
          decide

theorem prime_1724929 : Nat.Prime 1724929 := by
  apply lucas_primality 1724929 (7 : ZMod 1724929)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1724929 - 1 = (2 : ℕ)^9 * ((3 : ℕ)^1 * ((1123 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1724929)^862464 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 1724929)^574976 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1123 := Nat.prime_eq_prime_of_dvd_pow hq prime_1123 hd
        subst q
        change (7 : ZMod 1724929)^1536 ≠ 1
        reduce_mod_char
        decide

theorem prime_1730089 : Nat.Prime 1730089 := by
  apply lucas_primality 1730089 (37 : ZMod 1730089)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1730089 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((24029 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (37 : ZMod 1730089)^865044 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (37 : ZMod 1730089)^576696 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 24029 := Nat.prime_eq_prime_of_dvd_pow hq prime_24029 hd
        subst q
        change (37 : ZMod 1730089)^72 ≠ 1
        reduce_mod_char
        decide

theorem prime_1749239 : Nat.Prime 1749239 := by
  apply lucas_primality 1749239 (7 : ZMod 1749239)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1749239 - 1 = (2 : ℕ)^1 * ((874619 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1749239)^874619 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 874619 := Nat.prime_eq_prime_of_dvd_pow hq prime_874619 hd
      subst q
      change (7 : ZMod 1749239)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_1750681 : Nat.Prime 1750681 := by
  apply lucas_primality 1750681 (41 : ZMod 1750681)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1750681 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((1621 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (41 : ZMod 1750681)^875340 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (41 : ZMod 1750681)^583560 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (41 : ZMod 1750681)^350136 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1621 := Nat.prime_eq_prime_of_dvd_pow hq prime_1621 hd
          subst q
          change (41 : ZMod 1750681)^1080 ≠ 1
          reduce_mod_char
          decide

theorem prime_1765343 : Nat.Prime 1765343 := by
  apply lucas_primality 1765343 (5 : ZMod 1765343)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1765343 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((38377 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1765343)^882671 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (5 : ZMod 1765343)^76754 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 38377 := Nat.prime_eq_prime_of_dvd_pow hq prime_38377 hd
        subst q
        change (5 : ZMod 1765343)^46 ≠ 1
        reduce_mod_char
        decide

theorem prime_1771607 : Nat.Prime 1771607 := by
  apply lucas_primality 1771607 (5 : ZMod 1771607)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1771607 - 1 = (2 : ℕ)^1 * ((885803 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1771607)^885803 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 885803 := Nat.prime_eq_prime_of_dvd_pow hq prime_885803 hd
      subst q
      change (5 : ZMod 1771607)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_1775867 : Nat.Prime 1775867 := by
  apply lucas_primality 1775867 (2 : ZMod 1775867)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1775867 - 1 = (2 : ℕ)^1 * ((31 : ℕ)^1 * ((28643 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1775867)^887933 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (2 : ZMod 1775867)^57286 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 28643 := Nat.prime_eq_prime_of_dvd_pow hq prime_28643 hd
        subst q
        change (2 : ZMod 1775867)^62 ≠ 1
        reduce_mod_char
        decide

theorem prime_1800017 : Nat.Prime 1800017 := by
  apply lucas_primality 1800017 (3 : ZMod 1800017)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1800017 - 1 = (2 : ℕ)^4 * ((112501 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1800017)^900008 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 112501 := Nat.prime_eq_prime_of_dvd_pow hq prime_112501 hd
      subst q
      change (3 : ZMod 1800017)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_1804963 : Nat.Prime 1804963 := by
  apply lucas_primality 1804963 (2 : ZMod 1804963)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1804963 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((71 : ℕ)^1 * ((223 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1804963)^902481 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1804963)^601654 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 1804963)^94998 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
            subst q
            change (2 : ZMod 1804963)^25422 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 223 := Nat.prime_eq_prime_of_dvd_pow hq prime_223 hd
            subst q
            change (2 : ZMod 1804963)^8094 ≠ 1
            reduce_mod_char
            decide

end LegendreK6.Pratt
