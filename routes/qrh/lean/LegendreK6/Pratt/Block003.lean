import LegendreK6.Pratt.Block002

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LegendreK6.Pratt

theorem prime_5407 : Nat.Prime 5407 := by
  apply lucas_primality 5407 (3 : ZMod 5407)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5407 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((53 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 5407)^2703 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 5407)^1802 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (3 : ZMod 5407)^318 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (3 : ZMod 5407)^102 ≠ 1
          reduce_mod_char
          decide

theorem prime_5417 : Nat.Prime 5417 := by
  apply lucas_primality 5417 (3 : ZMod 5417)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5417 - 1 = (2 : ℕ)^3 * ((677 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 5417)^2708 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 677 := Nat.prime_eq_prime_of_dvd_pow hq prime_677 hd
      subst q
      change (3 : ZMod 5417)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_5419 : Nat.Prime 5419 := by
  apply lucas_primality 5419 (3 : ZMod 5419)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5419 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((43 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 5419)^2709 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 5419)^1806 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 5419)^774 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (3 : ZMod 5419)^126 ≠ 1
          reduce_mod_char
          decide

theorem prime_5449 : Nat.Prime 5449 := by
  apply lucas_primality 5449 (7 : ZMod 5449)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5449 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((227 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 5449)^2724 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 5449)^1816 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 227 := Nat.prime_eq_prime_of_dvd_pow hq prime_227 hd
        subst q
        change (7 : ZMod 5449)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_5483 : Nat.Prime 5483 := by
  apply lucas_primality 5483 (2 : ZMod 5483)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5483 - 1 = (2 : ℕ)^1 * ((2741 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5483)^2741 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 2741 := Nat.prime_eq_prime_of_dvd_pow hq prime_2741 hd
      subst q
      change (2 : ZMod 5483)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_5501 : Nat.Prime 5501 := by
  apply lucas_primality 5501 (2 : ZMod 5501)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5501 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^3 * ((11 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5501)^2750 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 5501)^1100 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 5501)^500 ≠ 1
        reduce_mod_char
        decide

theorem prime_5503 : Nat.Prime 5503 := by
  apply lucas_primality 5503 (3 : ZMod 5503)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5503 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((131 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 5503)^2751 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 5503)^1834 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 5503)^786 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
          subst q
          change (3 : ZMod 5503)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_5519 : Nat.Prime 5519 := by
  apply lucas_primality 5519 (13 : ZMod 5519)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5519 - 1 = (2 : ℕ)^1 * ((31 : ℕ)^1 * ((89 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 5519)^2759 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (13 : ZMod 5519)^178 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
        subst q
        change (13 : ZMod 5519)^62 ≠ 1
        reduce_mod_char
        decide

theorem prime_5521 : Nat.Prime 5521 := by
  apply lucas_primality 5521 (11 : ZMod 5521)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5521 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((23 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 5521)^2760 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 5521)^1840 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 5521)^1104 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (11 : ZMod 5521)^240 ≠ 1
          reduce_mod_char
          decide

theorem prime_5531 : Nat.Prime 5531 := by
  apply lucas_primality 5531 (10 : ZMod 5531)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5531 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((79 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 5531)^2765 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (10 : ZMod 5531)^1106 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (10 : ZMod 5531)^790 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (10 : ZMod 5531)^70 ≠ 1
          reduce_mod_char
          decide

theorem prime_5573 : Nat.Prime 5573 := by
  apply lucas_primality 5573 (2 : ZMod 5573)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5573 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((199 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5573)^2786 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 5573)^796 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 199 := Nat.prime_eq_prime_of_dvd_pow hq prime_199 hd
        subst q
        change (2 : ZMod 5573)^28 ≠ 1
        reduce_mod_char
        decide

theorem prime_5581 : Nat.Prime 5581 := by
  apply lucas_primality 5581 (6 : ZMod 5581)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5581 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((31 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 5581)^2790 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 5581)^1860 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 5581)^1116 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (6 : ZMod 5581)^180 ≠ 1
          reduce_mod_char
          decide

theorem prime_5591 : Nat.Prime 5591 := by
  apply lucas_primality 5591 (11 : ZMod 5591)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5591 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((43 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 5591)^2795 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 5591)^1118 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (11 : ZMod 5591)^430 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (11 : ZMod 5591)^130 ≠ 1
          reduce_mod_char
          decide

theorem prime_5639 : Nat.Prime 5639 := by
  apply lucas_primality 5639 (7 : ZMod 5639)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5639 - 1 = (2 : ℕ)^1 * ((2819 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 5639)^2819 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 2819 := Nat.prime_eq_prime_of_dvd_pow hq prime_2819 hd
      subst q
      change (7 : ZMod 5639)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_5641 : Nat.Prime 5641 := by
  apply lucas_primality 5641 (14 : ZMod 5641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5641 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((47 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 5641)^2820 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 5641)^1880 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (14 : ZMod 5641)^1128 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (14 : ZMod 5641)^120 ≠ 1
          reduce_mod_char
          decide

theorem prime_5651 : Nat.Prime 5651 := by
  apply lucas_primality 5651 (2 : ZMod 5651)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5651 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((113 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5651)^2825 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 5651)^1130 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
        subst q
        change (2 : ZMod 5651)^50 ≠ 1
        reduce_mod_char
        decide

theorem prime_5653 : Nat.Prime 5653 := by
  apply lucas_primality 5653 (5 : ZMod 5653)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5653 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((157 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 5653)^2826 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 5653)^1884 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
        subst q
        change (5 : ZMod 5653)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_5683 : Nat.Prime 5683 := by
  apply lucas_primality 5683 (2 : ZMod 5683)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5683 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((947 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5683)^2841 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 5683)^1894 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 947 := Nat.prime_eq_prime_of_dvd_pow hq prime_947 hd
        subst q
        change (2 : ZMod 5683)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_5693 : Nat.Prime 5693 := by
  apply lucas_primality 5693 (2 : ZMod 5693)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5693 - 1 = (2 : ℕ)^2 * ((1423 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5693)^2846 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1423 := Nat.prime_eq_prime_of_dvd_pow hq prime_1423 hd
      subst q
      change (2 : ZMod 5693)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_5711 : Nat.Prime 5711 := by
  apply lucas_primality 5711 (19 : ZMod 5711)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5711 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((571 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 5711)^2855 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (19 : ZMod 5711)^1142 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 571 := Nat.prime_eq_prime_of_dvd_pow hq prime_571 hd
        subst q
        change (19 : ZMod 5711)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_5717 : Nat.Prime 5717 := by
  apply lucas_primality 5717 (2 : ZMod 5717)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5717 - 1 = (2 : ℕ)^2 * ((1429 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5717)^2858 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1429 := Nat.prime_eq_prime_of_dvd_pow hq prime_1429 hd
      subst q
      change (2 : ZMod 5717)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_5737 : Nat.Prime 5737 := by
  apply lucas_primality 5737 (5 : ZMod 5737)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5737 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((239 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 5737)^2868 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 5737)^1912 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 239 := Nat.prime_eq_prime_of_dvd_pow hq prime_239 hd
        subst q
        change (5 : ZMod 5737)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_5741 : Nat.Prime 5741 := by
  apply lucas_primality 5741 (2 : ZMod 5741)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5741 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((41 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5741)^2870 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 5741)^1148 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 5741)^820 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (2 : ZMod 5741)^140 ≠ 1
          reduce_mod_char
          decide

theorem prime_5801 : Nat.Prime 5801 := by
  apply lucas_primality 5801 (3 : ZMod 5801)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5801 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^2 * ((29 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 5801)^2900 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 5801)^1160 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (3 : ZMod 5801)^200 ≠ 1
        reduce_mod_char
        decide

theorem prime_5821 : Nat.Prime 5821 := by
  apply lucas_primality 5821 (6 : ZMod 5821)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5821 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((97 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 5821)^2910 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 5821)^1940 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 5821)^1164 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
          subst q
          change (6 : ZMod 5821)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_5843 : Nat.Prime 5843 := by
  apply lucas_primality 5843 (2 : ZMod 5843)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5843 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((127 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5843)^2921 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (2 : ZMod 5843)^254 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
        subst q
        change (2 : ZMod 5843)^46 ≠ 1
        reduce_mod_char
        decide

theorem prime_5851 : Nat.Prime 5851 := by
  apply lucas_primality 5851 (2 : ZMod 5851)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5851 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^2 * ((13 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5851)^2925 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 5851)^1950 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 5851)^1170 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 5851)^450 ≠ 1
          reduce_mod_char
          decide

theorem prime_5867 : Nat.Prime 5867 := by
  apply lucas_primality 5867 (5 : ZMod 5867)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5867 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((419 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 5867)^2933 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 5867)^838 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 419 := Nat.prime_eq_prime_of_dvd_pow hq prime_419 hd
        subst q
        change (5 : ZMod 5867)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_5869 : Nat.Prime 5869 := by
  apply lucas_primality 5869 (2 : ZMod 5869)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5869 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((163 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5869)^2934 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 5869)^1956 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
        subst q
        change (2 : ZMod 5869)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_5897 : Nat.Prime 5897 := by
  apply lucas_primality 5897 (3 : ZMod 5897)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5897 - 1 = (2 : ℕ)^3 * ((11 : ℕ)^1 * ((67 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 5897)^2948 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 5897)^536 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
        subst q
        change (3 : ZMod 5897)^88 ≠ 1
        reduce_mod_char
        decide

theorem prime_5903 : Nat.Prime 5903 := by
  apply lucas_primality 5903 (5 : ZMod 5903)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5903 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((227 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 5903)^2951 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (5 : ZMod 5903)^454 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 227 := Nat.prime_eq_prime_of_dvd_pow hq prime_227 hd
        subst q
        change (5 : ZMod 5903)^26 ≠ 1
        reduce_mod_char
        decide

theorem prime_5923 : Nat.Prime 5923 := by
  apply lucas_primality 5923 (2 : ZMod 5923)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5923 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((47 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5923)^2961 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 5923)^1974 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 5923)^846 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (2 : ZMod 5923)^126 ≠ 1
          reduce_mod_char
          decide

theorem prime_5939 : Nat.Prime 5939 := by
  apply lucas_primality 5939 (2 : ZMod 5939)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5939 - 1 = (2 : ℕ)^1 * ((2969 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5939)^2969 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 2969 := Nat.prime_eq_prime_of_dvd_pow hq prime_2969 hd
      subst q
      change (2 : ZMod 5939)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_5953 : Nat.Prime 5953 := by
  apply lucas_primality 5953 (7 : ZMod 5953)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5953 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^1 * ((31 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 5953)^2976 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 5953)^1984 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (7 : ZMod 5953)^192 ≠ 1
        reduce_mod_char
        decide

theorem prime_5981 : Nat.Prime 5981 := by
  apply lucas_primality 5981 (3 : ZMod 5981)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5981 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((23 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 5981)^2990 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 5981)^1196 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 5981)^460 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (3 : ZMod 5981)^260 ≠ 1
          reduce_mod_char
          decide

theorem prime_5987 : Nat.Prime 5987 := by
  apply lucas_primality 5987 (2 : ZMod 5987)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5987 - 1 = (2 : ℕ)^1 * ((41 : ℕ)^1 * ((73 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5987)^2993 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
        subst q
        change (2 : ZMod 5987)^146 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
        subst q
        change (2 : ZMod 5987)^82 ≠ 1
        reduce_mod_char
        decide

theorem prime_6007 : Nat.Prime 6007 := by
  apply lucas_primality 6007 (3 : ZMod 6007)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6007 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 6007)^3003 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 6007)^2002 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 6007)^858 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (3 : ZMod 6007)^546 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (3 : ZMod 6007)^462 ≠ 1
            reduce_mod_char
            decide

theorem prime_6073 : Nat.Prime 6073 := by
  apply lucas_primality 6073 (10 : ZMod 6073)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6073 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((23 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 6073)^3036 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 6073)^2024 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (10 : ZMod 6073)^552 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (10 : ZMod 6073)^264 ≠ 1
          reduce_mod_char
          decide

theorem prime_6079 : Nat.Prime 6079 := by
  apply lucas_primality 6079 (17 : ZMod 6079)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6079 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1013 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 6079)^3039 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 6079)^2026 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1013 := Nat.prime_eq_prime_of_dvd_pow hq prime_1013 hd
        subst q
        change (17 : ZMod 6079)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_6091 : Nat.Prime 6091 := by
  apply lucas_primality 6091 (7 : ZMod 6091)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6091 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((29 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 6091)^3045 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 6091)^2030 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 6091)^1218 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (7 : ZMod 6091)^870 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (7 : ZMod 6091)^210 ≠ 1
            reduce_mod_char
            decide

theorem prime_6101 : Nat.Prime 6101 := by
  apply lucas_primality 6101 (2 : ZMod 6101)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6101 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((61 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6101)^3050 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 6101)^1220 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
        subst q
        change (2 : ZMod 6101)^100 ≠ 1
        reduce_mod_char
        decide

theorem prime_6113 : Nat.Prime 6113 := by
  apply lucas_primality 6113 (3 : ZMod 6113)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6113 - 1 = (2 : ℕ)^5 * ((191 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 6113)^3056 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
      subst q
      change (3 : ZMod 6113)^32 ≠ 1
      reduce_mod_char
      decide

theorem prime_6121 : Nat.Prime 6121 := by
  apply lucas_primality 6121 (7 : ZMod 6121)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6121 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((17 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 6121)^3060 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 6121)^2040 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 6121)^1224 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (7 : ZMod 6121)^360 ≠ 1
          reduce_mod_char
          decide

theorem prime_6133 : Nat.Prime 6133 := by
  apply lucas_primality 6133 (5 : ZMod 6133)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6133 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((73 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 6133)^3066 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 6133)^2044 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 6133)^876 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
          subst q
          change (5 : ZMod 6133)^84 ≠ 1
          reduce_mod_char
          decide

theorem prime_6143 : Nat.Prime 6143 := by
  apply lucas_primality 6143 (5 : ZMod 6143)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6143 - 1 = (2 : ℕ)^1 * ((37 : ℕ)^1 * ((83 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 6143)^3071 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (5 : ZMod 6143)^166 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
        subst q
        change (5 : ZMod 6143)^74 ≠ 1
        reduce_mod_char
        decide

theorem prime_6163 : Nat.Prime 6163 := by
  apply lucas_primality 6163 (3 : ZMod 6163)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6163 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((79 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 6163)^3081 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 6163)^2054 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 6163)^474 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (3 : ZMod 6163)^78 ≠ 1
          reduce_mod_char
          decide

theorem prime_6203 : Nat.Prime 6203 := by
  apply lucas_primality 6203 (2 : ZMod 6203)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6203 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((443 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6203)^3101 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 6203)^886 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 443 := Nat.prime_eq_prime_of_dvd_pow hq prime_443 hd
        subst q
        change (2 : ZMod 6203)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_6217 : Nat.Prime 6217 := by
  apply lucas_primality 6217 (5 : ZMod 6217)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6217 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((37 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 6217)^3108 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 6217)^2072 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 6217)^888 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (5 : ZMod 6217)^168 ≠ 1
          reduce_mod_char
          decide

theorem prime_6229 : Nat.Prime 6229 := by
  apply lucas_primality 6229 (2 : ZMod 6229)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6229 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((173 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6229)^3114 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 6229)^2076 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
        subst q
        change (2 : ZMod 6229)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_6247 : Nat.Prime 6247 := by
  apply lucas_primality 6247 (5 : ZMod 6247)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6247 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((347 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 6247)^3123 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 6247)^2082 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 347 := Nat.prime_eq_prime_of_dvd_pow hq prime_347 hd
        subst q
        change (5 : ZMod 6247)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_6263 : Nat.Prime 6263 := by
  apply lucas_primality 6263 (5 : ZMod 6263)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6263 - 1 = (2 : ℕ)^1 * ((31 : ℕ)^1 * ((101 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 6263)^3131 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (5 : ZMod 6263)^202 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
        subst q
        change (5 : ZMod 6263)^62 ≠ 1
        reduce_mod_char
        decide

theorem prime_6269 : Nat.Prime 6269 := by
  apply lucas_primality 6269 (2 : ZMod 6269)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6269 - 1 = (2 : ℕ)^2 * ((1567 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6269)^3134 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1567 := Nat.prime_eq_prime_of_dvd_pow hq prime_1567 hd
      subst q
      change (2 : ZMod 6269)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_6277 : Nat.Prime 6277 := by
  apply lucas_primality 6277 (2 : ZMod 6277)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6277 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((523 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6277)^3138 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 6277)^2092 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 523 := Nat.prime_eq_prime_of_dvd_pow hq prime_523 hd
        subst q
        change (2 : ZMod 6277)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_6299 : Nat.Prime 6299 := by
  apply lucas_primality 6299 (2 : ZMod 6299)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6299 - 1 = (2 : ℕ)^1 * ((47 : ℕ)^1 * ((67 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6299)^3149 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (2 : ZMod 6299)^134 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
        subst q
        change (2 : ZMod 6299)^94 ≠ 1
        reduce_mod_char
        decide

theorem prime_6311 : Nat.Prime 6311 := by
  apply lucas_primality 6311 (7 : ZMod 6311)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6311 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((631 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 6311)^3155 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 6311)^1262 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 631 := Nat.prime_eq_prime_of_dvd_pow hq prime_631 hd
        subst q
        change (7 : ZMod 6311)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_6323 : Nat.Prime 6323 := by
  apply lucas_primality 6323 (2 : ZMod 6323)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6323 - 1 = (2 : ℕ)^1 * ((29 : ℕ)^1 * ((109 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6323)^3161 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (2 : ZMod 6323)^218 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
        subst q
        change (2 : ZMod 6323)^58 ≠ 1
        reduce_mod_char
        decide

theorem prime_6329 : Nat.Prime 6329 := by
  apply lucas_primality 6329 (3 : ZMod 6329)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6329 - 1 = (2 : ℕ)^3 * ((7 : ℕ)^1 * ((113 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 6329)^3164 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 6329)^904 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
        subst q
        change (3 : ZMod 6329)^56 ≠ 1
        reduce_mod_char
        decide

theorem prime_6337 : Nat.Prime 6337 := by
  apply lucas_primality 6337 (10 : ZMod 6337)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6337 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^2 * ((11 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 6337)^3168 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 6337)^2112 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (10 : ZMod 6337)^576 ≠ 1
        reduce_mod_char
        decide

theorem prime_6343 : Nat.Prime 6343 := by
  apply lucas_primality 6343 (3 : ZMod 6343)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6343 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((151 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 6343)^3171 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 6343)^2114 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 6343)^906 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
          subst q
          change (3 : ZMod 6343)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_6361 : Nat.Prime 6361 := by
  apply lucas_primality 6361 (19 : ZMod 6361)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6361 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((53 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 6361)^3180 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 6361)^2120 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (19 : ZMod 6361)^1272 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (19 : ZMod 6361)^120 ≠ 1
          reduce_mod_char
          decide

theorem prime_6373 : Nat.Prime 6373 := by
  apply lucas_primality 6373 (2 : ZMod 6373)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6373 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((59 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6373)^3186 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 6373)^2124 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
        subst q
        change (2 : ZMod 6373)^108 ≠ 1
        reduce_mod_char
        decide

theorem prime_6389 : Nat.Prime 6389 := by
  apply lucas_primality 6389 (2 : ZMod 6389)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6389 - 1 = (2 : ℕ)^2 * ((1597 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6389)^3194 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1597 := Nat.prime_eq_prime_of_dvd_pow hq prime_1597 hd
      subst q
      change (2 : ZMod 6389)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_6397 : Nat.Prime 6397 := by
  apply lucas_primality 6397 (2 : ZMod 6397)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6397 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((41 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6397)^3198 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 6397)^2132 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 6397)^492 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (2 : ZMod 6397)^156 ≠ 1
          reduce_mod_char
          decide

theorem prime_6421 : Nat.Prime 6421 := by
  apply lucas_primality 6421 (6 : ZMod 6421)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6421 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((107 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 6421)^3210 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 6421)^2140 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 6421)^1284 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
          subst q
          change (6 : ZMod 6421)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_6427 : Nat.Prime 6427 := by
  apply lucas_primality 6427 (3 : ZMod 6427)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6427 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((17 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 6427)^3213 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 6427)^2142 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 6427)^918 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (3 : ZMod 6427)^378 ≠ 1
          reduce_mod_char
          decide

theorem prime_6449 : Nat.Prime 6449 := by
  apply lucas_primality 6449 (3 : ZMod 6449)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6449 - 1 = (2 : ℕ)^4 * ((13 : ℕ)^1 * ((31 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 6449)^3224 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 6449)^496 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (3 : ZMod 6449)^208 ≠ 1
        reduce_mod_char
        decide

theorem prime_6451 : Nat.Prime 6451 := by
  apply lucas_primality 6451 (3 : ZMod 6451)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6451 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((43 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 6451)^3225 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 6451)^2150 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 6451)^1290 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (3 : ZMod 6451)^150 ≠ 1
          reduce_mod_char
          decide

theorem prime_6481 : Nat.Prime 6481 := by
  apply lucas_primality 6481 (7 : ZMod 6481)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6481 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^4 * ((5 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 6481)^3240 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 6481)^2160 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 6481)^1296 ≠ 1
        reduce_mod_char
        decide

theorem prime_6491 : Nat.Prime 6491 := by
  apply lucas_primality 6491 (2 : ZMod 6491)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6491 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((59 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6491)^3245 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 6491)^1298 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 6491)^590 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (2 : ZMod 6491)^110 ≠ 1
          reduce_mod_char
          decide

theorem prime_6521 : Nat.Prime 6521 := by
  apply lucas_primality 6521 (6 : ZMod 6521)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6521 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((163 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 6521)^3260 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 6521)^1304 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
        subst q
        change (6 : ZMod 6521)^40 ≠ 1
        reduce_mod_char
        decide

theorem prime_6563 : Nat.Prime 6563 := by
  apply lucas_primality 6563 (5 : ZMod 6563)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6563 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((193 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 6563)^3281 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (5 : ZMod 6563)^386 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
        subst q
        change (5 : ZMod 6563)^34 ≠ 1
        reduce_mod_char
        decide

theorem prime_6577 : Nat.Prime 6577 := by
  apply lucas_primality 6577 (5 : ZMod 6577)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6577 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((137 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 6577)^3288 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 6577)^2192 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
        subst q
        change (5 : ZMod 6577)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_6619 : Nat.Prime 6619 := by
  apply lucas_primality 6619 (2 : ZMod 6619)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6619 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1103 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6619)^3309 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 6619)^2206 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1103 := Nat.prime_eq_prime_of_dvd_pow hq prime_1103 hd
        subst q
        change (2 : ZMod 6619)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_6659 : Nat.Prime 6659 := by
  apply lucas_primality 6659 (2 : ZMod 6659)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6659 - 1 = (2 : ℕ)^1 * ((3329 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6659)^3329 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3329 := Nat.prime_eq_prime_of_dvd_pow hq prime_3329 hd
      subst q
      change (2 : ZMod 6659)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_6661 : Nat.Prime 6661 := by
  apply lucas_primality 6661 (6 : ZMod 6661)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6661 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((37 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 6661)^3330 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 6661)^2220 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 6661)^1332 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (6 : ZMod 6661)^180 ≠ 1
          reduce_mod_char
          decide

theorem prime_6679 : Nat.Prime 6679 := by
  apply lucas_primality 6679 (7 : ZMod 6679)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6679 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((53 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 6679)^3339 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 6679)^2226 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 6679)^954 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (7 : ZMod 6679)^126 ≠ 1
          reduce_mod_char
          decide

theorem prime_6689 : Nat.Prime 6689 := by
  apply lucas_primality 6689 (3 : ZMod 6689)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6689 - 1 = (2 : ℕ)^5 * ((11 : ℕ)^1 * ((19 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 6689)^3344 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 6689)^608 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (3 : ZMod 6689)^352 ≠ 1
        reduce_mod_char
        decide

theorem prime_6691 : Nat.Prime 6691 := by
  apply lucas_primality 6691 (2 : ZMod 6691)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6691 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((223 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6691)^3345 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 6691)^2230 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 6691)^1338 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 223 := Nat.prime_eq_prime_of_dvd_pow hq prime_223 hd
          subst q
          change (2 : ZMod 6691)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_6701 : Nat.Prime 6701 := by
  apply lucas_primality 6701 (2 : ZMod 6701)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6701 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((67 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6701)^3350 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 6701)^1340 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
        subst q
        change (2 : ZMod 6701)^100 ≠ 1
        reduce_mod_char
        decide

theorem prime_6703 : Nat.Prime 6703 := by
  apply lucas_primality 6703 (5 : ZMod 6703)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6703 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1117 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 6703)^3351 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 6703)^2234 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1117 := Nat.prime_eq_prime_of_dvd_pow hq prime_1117 hd
        subst q
        change (5 : ZMod 6703)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_6709 : Nat.Prime 6709 := by
  apply lucas_primality 6709 (2 : ZMod 6709)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6709 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((43 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6709)^3354 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 6709)^2236 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 6709)^516 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (2 : ZMod 6709)^156 ≠ 1
          reduce_mod_char
          decide

theorem prime_6719 : Nat.Prime 6719 := by
  apply lucas_primality 6719 (11 : ZMod 6719)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6719 - 1 = (2 : ℕ)^1 * ((3359 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 6719)^3359 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3359 := Nat.prime_eq_prime_of_dvd_pow hq prime_3359 hd
      subst q
      change (11 : ZMod 6719)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_6761 : Nat.Prime 6761 := by
  apply lucas_primality 6761 (3 : ZMod 6761)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6761 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((13 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 6761)^3380 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 6761)^1352 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 6761)^520 ≠ 1
        reduce_mod_char
        decide

theorem prime_6827 : Nat.Prime 6827 := by
  apply lucas_primality 6827 (2 : ZMod 6827)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6827 - 1 = (2 : ℕ)^1 * ((3413 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6827)^3413 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3413 := Nat.prime_eq_prime_of_dvd_pow hq prime_3413 hd
      subst q
      change (2 : ZMod 6827)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_6829 : Nat.Prime 6829 := by
  apply lucas_primality 6829 (2 : ZMod 6829)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6829 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((569 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6829)^3414 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 6829)^2276 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 569 := Nat.prime_eq_prime_of_dvd_pow hq prime_569 hd
        subst q
        change (2 : ZMod 6829)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_6841 : Nat.Prime 6841 := by
  apply lucas_primality 6841 (22 : ZMod 6841)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6841 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((19 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (22 : ZMod 6841)^3420 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (22 : ZMod 6841)^2280 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (22 : ZMod 6841)^1368 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (22 : ZMod 6841)^360 ≠ 1
          reduce_mod_char
          decide

theorem prime_6871 : Nat.Prime 6871 := by
  apply lucas_primality 6871 (3 : ZMod 6871)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6871 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((229 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 6871)^3435 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 6871)^2290 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 6871)^1374 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 229 := Nat.prime_eq_prime_of_dvd_pow hq prime_229 hd
          subst q
          change (3 : ZMod 6871)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_6883 : Nat.Prime 6883 := by
  apply lucas_primality 6883 (2 : ZMod 6883)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6883 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((31 : ℕ)^1 * ((37 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6883)^3441 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 6883)^2294 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (2 : ZMod 6883)^222 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (2 : ZMod 6883)^186 ≠ 1
          reduce_mod_char
          decide

theorem prime_6899 : Nat.Prime 6899 := by
  apply lucas_primality 6899 (2 : ZMod 6899)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6899 - 1 = (2 : ℕ)^1 * ((3449 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6899)^3449 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3449 := Nat.prime_eq_prime_of_dvd_pow hq prime_3449 hd
      subst q
      change (2 : ZMod 6899)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_6947 : Nat.Prime 6947 := by
  apply lucas_primality 6947 (2 : ZMod 6947)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6947 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((151 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6947)^3473 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (2 : ZMod 6947)^302 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
        subst q
        change (2 : ZMod 6947)^46 ≠ 1
        reduce_mod_char
        decide

theorem prime_6949 : Nat.Prime 6949 := by
  apply lucas_primality 6949 (2 : ZMod 6949)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6949 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((193 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6949)^3474 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 6949)^2316 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
        subst q
        change (2 : ZMod 6949)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_6967 : Nat.Prime 6967 := by
  apply lucas_primality 6967 (5 : ZMod 6967)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6967 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((43 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 6967)^3483 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 6967)^2322 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
        subst q
        change (5 : ZMod 6967)^162 ≠ 1
        reduce_mod_char
        decide

theorem prime_6971 : Nat.Prime 6971 := by
  apply lucas_primality 6971 (2 : ZMod 6971)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6971 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((41 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6971)^3485 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 6971)^1394 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 6971)^410 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (2 : ZMod 6971)^170 ≠ 1
          reduce_mod_char
          decide

theorem prime_6977 : Nat.Prime 6977 := by
  apply lucas_primality 6977 (3 : ZMod 6977)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6977 - 1 = (2 : ℕ)^6 * ((109 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 6977)^3488 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
      subst q
      change (3 : ZMod 6977)^64 ≠ 1
      reduce_mod_char
      decide

theorem prime_6983 : Nat.Prime 6983 := by
  apply lucas_primality 6983 (5 : ZMod 6983)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6983 - 1 = (2 : ℕ)^1 * ((3491 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 6983)^3491 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3491 := Nat.prime_eq_prime_of_dvd_pow hq prime_3491 hd
      subst q
      change (5 : ZMod 6983)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_6991 : Nat.Prime 6991 := by
  apply lucas_primality 6991 (6 : ZMod 6991)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6991 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((233 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 6991)^3495 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 6991)^2330 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 6991)^1398 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
          subst q
          change (6 : ZMod 6991)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_6997 : Nat.Prime 6997 := by
  apply lucas_primality 6997 (5 : ZMod 6997)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6997 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((53 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 6997)^3498 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 6997)^2332 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 6997)^636 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (5 : ZMod 6997)^132 ≠ 1
          reduce_mod_char
          decide

theorem prime_7019 : Nat.Prime 7019 := by
  apply lucas_primality 7019 (2 : ZMod 7019)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7019 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^2 * ((29 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 7019)^3509 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 7019)^638 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (2 : ZMod 7019)^242 ≠ 1
        reduce_mod_char
        decide

theorem prime_7027 : Nat.Prime 7027 := by
  apply lucas_primality 7027 (2 : ZMod 7027)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7027 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1171 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 7027)^3513 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 7027)^2342 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1171 := Nat.prime_eq_prime_of_dvd_pow hq prime_1171 hd
        subst q
        change (2 : ZMod 7027)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_7057 : Nat.Prime 7057 := by
  apply lucas_primality 7057 (5 : ZMod 7057)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7057 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((7 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 7057)^3528 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 7057)^2352 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 7057)^1008 ≠ 1
        reduce_mod_char
        decide

theorem prime_7079 : Nat.Prime 7079 := by
  apply lucas_primality 7079 (7 : ZMod 7079)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7079 - 1 = (2 : ℕ)^1 * ((3539 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 7079)^3539 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3539 := Nat.prime_eq_prime_of_dvd_pow hq prime_3539 hd
      subst q
      change (7 : ZMod 7079)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_7121 : Nat.Prime 7121 := by
  apply lucas_primality 7121 (3 : ZMod 7121)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7121 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((89 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 7121)^3560 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 7121)^1424 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
        subst q
        change (3 : ZMod 7121)^80 ≠ 1
        reduce_mod_char
        decide

theorem prime_7129 : Nat.Prime 7129 := by
  apply lucas_primality 7129 (7 : ZMod 7129)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7129 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^4 * ((11 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 7129)^3564 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 7129)^2376 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (7 : ZMod 7129)^648 ≠ 1
        reduce_mod_char
        decide

theorem prime_7177 : Nat.Prime 7177 := by
  apply lucas_primality 7177 (10 : ZMod 7177)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7177 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((23 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 7177)^3588 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 7177)^2392 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (10 : ZMod 7177)^552 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (10 : ZMod 7177)^312 ≠ 1
          reduce_mod_char
          decide

theorem prime_7211 : Nat.Prime 7211 := by
  apply lucas_primality 7211 (2 : ZMod 7211)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7211 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((103 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 7211)^3605 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 7211)^1442 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 7211)^1030 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
          subst q
          change (2 : ZMod 7211)^70 ≠ 1
          reduce_mod_char
          decide

theorem prime_7229 : Nat.Prime 7229 := by
  apply lucas_primality 7229 (2 : ZMod 7229)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7229 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((139 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 7229)^3614 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 7229)^556 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
        subst q
        change (2 : ZMod 7229)^52 ≠ 1
        reduce_mod_char
        decide

theorem prime_7237 : Nat.Prime 7237 := by
  apply lucas_primality 7237 (2 : ZMod 7237)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7237 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((67 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 7237)^3618 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 7237)^2412 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
        subst q
        change (2 : ZMod 7237)^108 ≠ 1
        reduce_mod_char
        decide

theorem prime_7253 : Nat.Prime 7253 := by
  apply lucas_primality 7253 (2 : ZMod 7253)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7253 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^2 * ((37 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 7253)^3626 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 7253)^1036 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (2 : ZMod 7253)^196 ≠ 1
        reduce_mod_char
        decide

theorem prime_7297 : Nat.Prime 7297 := by
  apply lucas_primality 7297 (5 : ZMod 7297)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7297 - 1 = (2 : ℕ)^7 * ((3 : ℕ)^1 * ((19 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 7297)^3648 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 7297)^2432 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (5 : ZMod 7297)^384 ≠ 1
        reduce_mod_char
        decide

theorem prime_7307 : Nat.Prime 7307 := by
  apply lucas_primality 7307 (2 : ZMod 7307)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7307 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((281 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 7307)^3653 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 7307)^562 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 281 := Nat.prime_eq_prime_of_dvd_pow hq prime_281 hd
        subst q
        change (2 : ZMod 7307)^26 ≠ 1
        reduce_mod_char
        decide

theorem prime_7333 : Nat.Prime 7333 := by
  apply lucas_primality 7333 (6 : ZMod 7333)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7333 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((47 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 7333)^3666 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 7333)^2444 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (6 : ZMod 7333)^564 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (6 : ZMod 7333)^156 ≠ 1
          reduce_mod_char
          decide

theorem prime_7349 : Nat.Prime 7349 := by
  apply lucas_primality 7349 (2 : ZMod 7349)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7349 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((167 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 7349)^3674 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 7349)^668 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
        subst q
        change (2 : ZMod 7349)^44 ≠ 1
        reduce_mod_char
        decide

theorem prime_7369 : Nat.Prime 7369 := by
  apply lucas_primality 7369 (7 : ZMod 7369)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7369 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((307 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 7369)^3684 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 7369)^2456 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 307 := Nat.prime_eq_prime_of_dvd_pow hq prime_307 hd
        subst q
        change (7 : ZMod 7369)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_7393 : Nat.Prime 7393 := by
  apply lucas_primality 7393 (5 : ZMod 7393)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7393 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 7393)^3696 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 7393)^2464 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 7393)^1056 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 7393)^672 ≠ 1
          reduce_mod_char
          decide

theorem prime_7433 : Nat.Prime 7433 := by
  apply lucas_primality 7433 (3 : ZMod 7433)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7433 - 1 = (2 : ℕ)^3 * ((929 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 7433)^3716 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 929 := Nat.prime_eq_prime_of_dvd_pow hq prime_929 hd
      subst q
      change (3 : ZMod 7433)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_7477 : Nat.Prime 7477 := by
  apply lucas_primality 7477 (2 : ZMod 7477)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7477 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((89 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 7477)^3738 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 7477)^2492 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 7477)^1068 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (2 : ZMod 7477)^84 ≠ 1
          reduce_mod_char
          decide

theorem prime_7487 : Nat.Prime 7487 := by
  apply lucas_primality 7487 (5 : ZMod 7487)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7487 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((197 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 7487)^3743 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (5 : ZMod 7487)^394 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
        subst q
        change (5 : ZMod 7487)^38 ≠ 1
        reduce_mod_char
        decide

theorem prime_7489 : Nat.Prime 7489 := by
  apply lucas_primality 7489 (7 : ZMod 7489)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7489 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^2 * ((13 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 7489)^3744 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 7489)^2496 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (7 : ZMod 7489)^576 ≠ 1
        reduce_mod_char
        decide

theorem prime_7561 : Nat.Prime 7561 := by
  apply lucas_primality 7561 (13 : ZMod 7561)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7561 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((7 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 7561)^3780 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 7561)^2520 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 7561)^1512 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (13 : ZMod 7561)^1080 ≠ 1
          reduce_mod_char
          decide

theorem prime_7577 : Nat.Prime 7577 := by
  apply lucas_primality 7577 (3 : ZMod 7577)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7577 - 1 = (2 : ℕ)^3 * ((947 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 7577)^3788 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 947 := Nat.prime_eq_prime_of_dvd_pow hq prime_947 hd
      subst q
      change (3 : ZMod 7577)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_7591 : Nat.Prime 7591 := by
  apply lucas_primality 7591 (6 : ZMod 7591)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7591 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((23 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 7591)^3795 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 7591)^2530 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 7591)^1518 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (6 : ZMod 7591)^690 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (6 : ZMod 7591)^330 ≠ 1
            reduce_mod_char
            decide

theorem prime_7607 : Nat.Prime 7607 := by
  apply lucas_primality 7607 (5 : ZMod 7607)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7607 - 1 = (2 : ℕ)^1 * ((3803 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 7607)^3803 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3803 := Nat.prime_eq_prime_of_dvd_pow hq prime_3803 hd
      subst q
      change (5 : ZMod 7607)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_7621 : Nat.Prime 7621 := by
  apply lucas_primality 7621 (2 : ZMod 7621)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7621 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((127 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 7621)^3810 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 7621)^2540 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 7621)^1524 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
          subst q
          change (2 : ZMod 7621)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_7639 : Nat.Prime 7639 := by
  apply lucas_primality 7639 (7 : ZMod 7639)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7639 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((67 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 7639)^3819 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 7639)^2546 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (7 : ZMod 7639)^402 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (7 : ZMod 7639)^114 ≠ 1
          reduce_mod_char
          decide

theorem prime_7649 : Nat.Prime 7649 := by
  apply lucas_primality 7649 (3 : ZMod 7649)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7649 - 1 = (2 : ℕ)^5 * ((239 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 7649)^3824 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 239 := Nat.prime_eq_prime_of_dvd_pow hq prime_239 hd
      subst q
      change (3 : ZMod 7649)^32 ≠ 1
      reduce_mod_char
      decide

theorem prime_7669 : Nat.Prime 7669 := by
  apply lucas_primality 7669 (2 : ZMod 7669)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7669 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((71 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 7669)^3834 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 7669)^2556 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
        subst q
        change (2 : ZMod 7669)^108 ≠ 1
        reduce_mod_char
        decide

theorem prime_7673 : Nat.Prime 7673 := by
  apply lucas_primality 7673 (3 : ZMod 7673)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7673 - 1 = (2 : ℕ)^3 * ((7 : ℕ)^1 * ((137 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 7673)^3836 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 7673)^1096 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
        subst q
        change (3 : ZMod 7673)^56 ≠ 1
        reduce_mod_char
        decide

theorem prime_7699 : Nat.Prime 7699 := by
  apply lucas_primality 7699 (3 : ZMod 7699)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7699 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1283 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 7699)^3849 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 7699)^2566 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1283 := Nat.prime_eq_prime_of_dvd_pow hq prime_1283 hd
        subst q
        change (3 : ZMod 7699)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_7703 : Nat.Prime 7703 := by
  apply lucas_primality 7703 (5 : ZMod 7703)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7703 - 1 = (2 : ℕ)^1 * ((3851 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 7703)^3851 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3851 := Nat.prime_eq_prime_of_dvd_pow hq prime_3851 hd
      subst q
      change (5 : ZMod 7703)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_7717 : Nat.Prime 7717 := by
  apply lucas_primality 7717 (2 : ZMod 7717)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7717 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((643 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 7717)^3858 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 7717)^2572 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 643 := Nat.prime_eq_prime_of_dvd_pow hq prime_643 hd
        subst q
        change (2 : ZMod 7717)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_7789 : Nat.Prime 7789 := by
  apply lucas_primality 7789 (2 : ZMod 7789)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7789 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((59 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 7789)^3894 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 7789)^2596 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 7789)^708 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (2 : ZMod 7789)^132 ≠ 1
          reduce_mod_char
          decide

theorem prime_7817 : Nat.Prime 7817 := by
  apply lucas_primality 7817 (3 : ZMod 7817)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7817 - 1 = (2 : ℕ)^3 * ((977 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 7817)^3908 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 977 := Nat.prime_eq_prime_of_dvd_pow hq prime_977 hd
      subst q
      change (3 : ZMod 7817)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_7841 : Nat.Prime 7841 := by
  apply lucas_primality 7841 (12 : ZMod 7841)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7841 - 1 = (2 : ℕ)^5 * ((5 : ℕ)^1 * ((7 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (12 : ZMod 7841)^3920 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (12 : ZMod 7841)^1568 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (12 : ZMod 7841)^1120 ≠ 1
        reduce_mod_char
        decide

theorem prime_7873 : Nat.Prime 7873 := by
  apply lucas_primality 7873 (5 : ZMod 7873)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7873 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^1 * ((41 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 7873)^3936 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 7873)^2624 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
        subst q
        change (5 : ZMod 7873)^192 ≠ 1
        reduce_mod_char
        decide

theorem prime_7883 : Nat.Prime 7883 := by
  apply lucas_primality 7883 (2 : ZMod 7883)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7883 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((563 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 7883)^3941 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 7883)^1126 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 563 := Nat.prime_eq_prime_of_dvd_pow hq prime_563 hd
        subst q
        change (2 : ZMod 7883)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_7901 : Nat.Prime 7901 := by
  apply lucas_primality 7901 (2 : ZMod 7901)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7901 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((79 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 7901)^3950 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 7901)^1580 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
        subst q
        change (2 : ZMod 7901)^100 ≠ 1
        reduce_mod_char
        decide

theorem prime_7919 : Nat.Prime 7919 := by
  apply lucas_primality 7919 (7 : ZMod 7919)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7919 - 1 = (2 : ℕ)^1 * ((37 : ℕ)^1 * ((107 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 7919)^3959 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (7 : ZMod 7919)^214 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
        subst q
        change (7 : ZMod 7919)^74 ≠ 1
        reduce_mod_char
        decide

theorem prime_7993 : Nat.Prime 7993 := by
  apply lucas_primality 7993 (5 : ZMod 7993)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7993 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((37 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 7993)^3996 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 7993)^2664 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (5 : ZMod 7993)^216 ≠ 1
        reduce_mod_char
        decide

theorem prime_8059 : Nat.Prime 8059 := by
  apply lucas_primality 8059 (3 : ZMod 8059)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8059 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((79 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 8059)^4029 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 8059)^2686 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (3 : ZMod 8059)^474 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (3 : ZMod 8059)^102 ≠ 1
          reduce_mod_char
          decide

theorem prime_8101 : Nat.Prime 8101 := by
  apply lucas_primality 8101 (6 : ZMod 8101)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8101 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^4 * ((5 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 8101)^4050 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 8101)^2700 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 8101)^1620 ≠ 1
        reduce_mod_char
        decide

theorem prime_8111 : Nat.Prime 8111 := by
  apply lucas_primality 8111 (11 : ZMod 8111)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8111 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((811 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 8111)^4055 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 8111)^1622 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 811 := Nat.prime_eq_prime_of_dvd_pow hq prime_811 hd
        subst q
        change (11 : ZMod 8111)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_8161 : Nat.Prime 8161 := by
  apply lucas_primality 8161 (7 : ZMod 8161)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8161 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((17 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 8161)^4080 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 8161)^2720 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 8161)^1632 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (7 : ZMod 8161)^480 ≠ 1
          reduce_mod_char
          decide

theorem prime_8167 : Nat.Prime 8167 := by
  apply lucas_primality 8167 (3 : ZMod 8167)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8167 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1361 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 8167)^4083 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 8167)^2722 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1361 := Nat.prime_eq_prime_of_dvd_pow hq prime_1361 hd
        subst q
        change (3 : ZMod 8167)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_8209 : Nat.Prime 8209 := by
  apply lucas_primality 8209 (7 : ZMod 8209)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8209 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^3 * ((19 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 8209)^4104 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 8209)^2736 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (7 : ZMod 8209)^432 ≠ 1
        reduce_mod_char
        decide

theorem prime_8219 : Nat.Prime 8219 := by
  apply lucas_primality 8219 (2 : ZMod 8219)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8219 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((587 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8219)^4109 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 8219)^1174 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 587 := Nat.prime_eq_prime_of_dvd_pow hq prime_587 hd
        subst q
        change (2 : ZMod 8219)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_8243 : Nat.Prime 8243 := by
  apply lucas_primality 8243 (2 : ZMod 8243)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8243 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((317 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8243)^4121 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 8243)^634 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 317 := Nat.prime_eq_prime_of_dvd_pow hq prime_317 hd
        subst q
        change (2 : ZMod 8243)^26 ≠ 1
        reduce_mod_char
        decide

theorem prime_8269 : Nat.Prime 8269 := by
  apply lucas_primality 8269 (2 : ZMod 8269)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8269 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((53 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8269)^4134 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 8269)^2756 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 8269)^636 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (2 : ZMod 8269)^156 ≠ 1
          reduce_mod_char
          decide

theorem prime_8273 : Nat.Prime 8273 := by
  apply lucas_primality 8273 (3 : ZMod 8273)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8273 - 1 = (2 : ℕ)^4 * ((11 : ℕ)^1 * ((47 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 8273)^4136 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 8273)^752 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (3 : ZMod 8273)^176 ≠ 1
        reduce_mod_char
        decide

theorem prime_8293 : Nat.Prime 8293 := by
  apply lucas_primality 8293 (2 : ZMod 8293)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8293 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((691 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8293)^4146 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 8293)^2764 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 691 := Nat.prime_eq_prime_of_dvd_pow hq prime_691 hd
        subst q
        change (2 : ZMod 8293)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_8297 : Nat.Prime 8297 := by
  apply lucas_primality 8297 (3 : ZMod 8297)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8297 - 1 = (2 : ℕ)^3 * ((17 : ℕ)^1 * ((61 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 8297)^4148 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (3 : ZMod 8297)^488 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
        subst q
        change (3 : ZMod 8297)^136 ≠ 1
        reduce_mod_char
        decide

theorem prime_8317 : Nat.Prime 8317 := by
  apply lucas_primality 8317 (6 : ZMod 8317)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8317 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((11 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 8317)^4158 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 8317)^2772 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 8317)^1188 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (6 : ZMod 8317)^756 ≠ 1
          reduce_mod_char
          decide

theorem prime_8329 : Nat.Prime 8329 := by
  apply lucas_primality 8329 (7 : ZMod 8329)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8329 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((347 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 8329)^4164 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 8329)^2776 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 347 := Nat.prime_eq_prime_of_dvd_pow hq prime_347 hd
        subst q
        change (7 : ZMod 8329)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_8363 : Nat.Prime 8363 := by
  apply lucas_primality 8363 (2 : ZMod 8363)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8363 - 1 = (2 : ℕ)^1 * ((37 : ℕ)^1 * ((113 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8363)^4181 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (2 : ZMod 8363)^226 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
        subst q
        change (2 : ZMod 8363)^74 ≠ 1
        reduce_mod_char
        decide

theorem prime_8369 : Nat.Prime 8369 := by
  apply lucas_primality 8369 (3 : ZMod 8369)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8369 - 1 = (2 : ℕ)^4 * ((523 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 8369)^4184 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 523 := Nat.prime_eq_prime_of_dvd_pow hq prime_523 hd
      subst q
      change (3 : ZMod 8369)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_8387 : Nat.Prime 8387 := by
  apply lucas_primality 8387 (2 : ZMod 8387)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8387 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((599 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8387)^4193 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 8387)^1198 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 599 := Nat.prime_eq_prime_of_dvd_pow hq prime_599 hd
        subst q
        change (2 : ZMod 8387)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_8389 : Nat.Prime 8389 := by
  apply lucas_primality 8389 (6 : ZMod 8389)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8389 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((233 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 8389)^4194 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 8389)^2796 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
        subst q
        change (6 : ZMod 8389)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_8429 : Nat.Prime 8429 := by
  apply lucas_primality 8429 (2 : ZMod 8429)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8429 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^2 * ((43 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8429)^4214 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 8429)^1204 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
        subst q
        change (2 : ZMod 8429)^196 ≠ 1
        reduce_mod_char
        decide

theorem prime_8501 : Nat.Prime 8501 := by
  apply lucas_primality 8501 (7 : ZMod 8501)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8501 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^3 * ((17 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 8501)^4250 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 8501)^1700 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (7 : ZMod 8501)^500 ≠ 1
        reduce_mod_char
        decide

theorem prime_8513 : Nat.Prime 8513 := by
  apply lucas_primality 8513 (5 : ZMod 8513)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8513 - 1 = (2 : ℕ)^6 * ((7 : ℕ)^1 * ((19 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 8513)^4256 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 8513)^1216 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (5 : ZMod 8513)^448 ≠ 1
        reduce_mod_char
        decide

theorem prime_8521 : Nat.Prime 8521 := by
  apply lucas_primality 8521 (13 : ZMod 8521)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8521 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((71 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 8521)^4260 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 8521)^2840 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 8521)^1704 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
          subst q
          change (13 : ZMod 8521)^120 ≠ 1
          reduce_mod_char
          decide

theorem prime_8527 : Nat.Prime 8527 := by
  apply lucas_primality 8527 (5 : ZMod 8527)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8527 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((29 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 8527)^4263 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 8527)^2842 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 8527)^1218 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (5 : ZMod 8527)^294 ≠ 1
          reduce_mod_char
          decide

theorem prime_8563 : Nat.Prime 8563 := by
  apply lucas_primality 8563 (2 : ZMod 8563)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8563 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1427 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8563)^4281 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 8563)^2854 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1427 := Nat.prime_eq_prime_of_dvd_pow hq prime_1427 hd
        subst q
        change (2 : ZMod 8563)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_8581 : Nat.Prime 8581 := by
  apply lucas_primality 8581 (6 : ZMod 8581)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8581 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 8581)^4290 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 8581)^2860 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 8581)^1716 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (6 : ZMod 8581)^780 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (6 : ZMod 8581)^660 ≠ 1
            reduce_mod_char
            decide

theorem prime_8599 : Nat.Prime 8599 := by
  apply lucas_primality 8599 (3 : ZMod 8599)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8599 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1433 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 8599)^4299 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 8599)^2866 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1433 := Nat.prime_eq_prime_of_dvd_pow hq prime_1433 hd
        subst q
        change (3 : ZMod 8599)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_8609 : Nat.Prime 8609 := by
  apply lucas_primality 8609 (3 : ZMod 8609)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8609 - 1 = (2 : ℕ)^5 * ((269 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 8609)^4304 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
      subst q
      change (3 : ZMod 8609)^32 ≠ 1
      reduce_mod_char
      decide

theorem prime_8629 : Nat.Prime 8629 := by
  apply lucas_primality 8629 (6 : ZMod 8629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8629 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((719 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 8629)^4314 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 8629)^2876 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 719 := Nat.prime_eq_prime_of_dvd_pow hq prime_719 hd
        subst q
        change (6 : ZMod 8629)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_8663 : Nat.Prime 8663 := by
  apply lucas_primality 8663 (5 : ZMod 8663)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8663 - 1 = (2 : ℕ)^1 * ((61 : ℕ)^1 * ((71 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 8663)^4331 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
        subst q
        change (5 : ZMod 8663)^142 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
        subst q
        change (5 : ZMod 8663)^122 ≠ 1
        reduce_mod_char
        decide

theorem prime_8669 : Nat.Prime 8669 := by
  apply lucas_primality 8669 (2 : ZMod 8669)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8669 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((197 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8669)^4334 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 8669)^788 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
        subst q
        change (2 : ZMod 8669)^44 ≠ 1
        reduce_mod_char
        decide

theorem prime_8681 : Nat.Prime 8681 := by
  apply lucas_primality 8681 (15 : ZMod 8681)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8681 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((31 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (15 : ZMod 8681)^4340 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (15 : ZMod 8681)^1736 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (15 : ZMod 8681)^1240 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (15 : ZMod 8681)^280 ≠ 1
          reduce_mod_char
          decide

theorem prime_8719 : Nat.Prime 8719 := by
  apply lucas_primality 8719 (3 : ZMod 8719)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8719 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1453 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 8719)^4359 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 8719)^2906 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1453 := Nat.prime_eq_prime_of_dvd_pow hq prime_1453 hd
        subst q
        change (3 : ZMod 8719)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_8737 : Nat.Prime 8737 := by
  apply lucas_primality 8737 (5 : ZMod 8737)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8737 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 8737)^4368 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 8737)^2912 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 8737)^1248 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (5 : ZMod 8737)^672 ≠ 1
          reduce_mod_char
          decide

theorem prime_8741 : Nat.Prime 8741 := by
  apply lucas_primality 8741 (2 : ZMod 8741)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8741 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((19 : ℕ)^1 * ((23 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8741)^4370 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 8741)^1748 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 8741)^460 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 8741)^380 ≠ 1
          reduce_mod_char
          decide

theorem prime_8761 : Nat.Prime 8761 := by
  apply lucas_primality 8761 (23 : ZMod 8761)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8761 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((73 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (23 : ZMod 8761)^4380 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (23 : ZMod 8761)^2920 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (23 : ZMod 8761)^1752 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
          subst q
          change (23 : ZMod 8761)^120 ≠ 1
          reduce_mod_char
          decide

theorem prime_8803 : Nat.Prime 8803 := by
  apply lucas_primality 8803 (2 : ZMod 8803)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8803 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((163 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8803)^4401 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 8803)^2934 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
        subst q
        change (2 : ZMod 8803)^54 ≠ 1
        reduce_mod_char
        decide

theorem prime_8807 : Nat.Prime 8807 := by
  apply lucas_primality 8807 (5 : ZMod 8807)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8807 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((17 : ℕ)^1 * ((37 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 8807)^4403 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 8807)^1258 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (5 : ZMod 8807)^518 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (5 : ZMod 8807)^238 ≠ 1
          reduce_mod_char
          decide

theorem prime_8821 : Nat.Prime 8821 := by
  apply lucas_primality 8821 (2 : ZMod 8821)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8821 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^2))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8821)^4410 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 8821)^2940 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 8821)^1764 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 8821)^1260 ≠ 1
          reduce_mod_char
          decide

theorem prime_8831 : Nat.Prime 8831 := by
  apply lucas_primality 8831 (7 : ZMod 8831)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8831 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((883 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 8831)^4415 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 8831)^1766 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 883 := Nat.prime_eq_prime_of_dvd_pow hq prime_883 hd
        subst q
        change (7 : ZMod 8831)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_8839 : Nat.Prime 8839 := by
  apply lucas_primality 8839 (3 : ZMod 8839)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8839 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((491 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 8839)^4419 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 8839)^2946 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 491 := Nat.prime_eq_prime_of_dvd_pow hq prime_491 hd
        subst q
        change (3 : ZMod 8839)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_8861 : Nat.Prime 8861 := by
  apply lucas_primality 8861 (2 : ZMod 8861)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8861 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((443 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8861)^4430 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 8861)^1772 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 443 := Nat.prime_eq_prime_of_dvd_pow hq prime_443 hd
        subst q
        change (2 : ZMod 8861)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_8971 : Nat.Prime 8971 := by
  apply lucas_primality 8971 (2 : ZMod 8971)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8971 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((23 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8971)^4485 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 8971)^2990 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 8971)^1794 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (2 : ZMod 8971)^690 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (2 : ZMod 8971)^390 ≠ 1
            reduce_mod_char
            decide

theorem prime_8999 : Nat.Prime 8999 := by
  apply lucas_primality 8999 (7 : ZMod 8999)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8999 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((409 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 8999)^4499 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (7 : ZMod 8999)^818 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 409 := Nat.prime_eq_prime_of_dvd_pow hq prime_409 hd
        subst q
        change (7 : ZMod 8999)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_9001 : Nat.Prime 9001 := by
  apply lucas_primality 9001 (7 : ZMod 9001)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9001 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((5 : ℕ)^3)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 9001)^4500 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 9001)^3000 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 9001)^1800 ≠ 1
        reduce_mod_char
        decide

theorem prime_9013 : Nat.Prime 9013 := by
  apply lucas_primality 9013 (5 : ZMod 9013)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9013 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((751 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 9013)^4506 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 9013)^3004 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 751 := Nat.prime_eq_prime_of_dvd_pow hq prime_751 hd
        subst q
        change (5 : ZMod 9013)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_9041 : Nat.Prime 9041 := by
  apply lucas_primality 9041 (3 : ZMod 9041)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9041 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((113 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 9041)^4520 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 9041)^1808 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
        subst q
        change (3 : ZMod 9041)^80 ≠ 1
        reduce_mod_char
        decide

theorem prime_9049 : Nat.Prime 9049 := by
  apply lucas_primality 9049 (7 : ZMod 9049)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9049 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((29 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 9049)^4524 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 9049)^3016 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (7 : ZMod 9049)^696 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (7 : ZMod 9049)^312 ≠ 1
          reduce_mod_char
          decide

theorem prime_9059 : Nat.Prime 9059 := by
  apply lucas_primality 9059 (2 : ZMod 9059)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9059 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((647 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9059)^4529 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 9059)^1294 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 647 := Nat.prime_eq_prime_of_dvd_pow hq prime_647 hd
        subst q
        change (2 : ZMod 9059)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_9103 : Nat.Prime 9103 := by
  apply lucas_primality 9103 (6 : ZMod 9103)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9103 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((37 : ℕ)^1 * ((41 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 9103)^4551 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 9103)^3034 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (6 : ZMod 9103)^246 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (6 : ZMod 9103)^222 ≠ 1
          reduce_mod_char
          decide

theorem prime_9109 : Nat.Prime 9109 := by
  apply lucas_primality 9109 (10 : ZMod 9109)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9109 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((23 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 9109)^4554 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 9109)^3036 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (10 : ZMod 9109)^828 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (10 : ZMod 9109)^396 ≠ 1
          reduce_mod_char
          decide

theorem prime_9137 : Nat.Prime 9137 := by
  apply lucas_primality 9137 (3 : ZMod 9137)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9137 - 1 = (2 : ℕ)^4 * ((571 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 9137)^4568 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 571 := Nat.prime_eq_prime_of_dvd_pow hq prime_571 hd
      subst q
      change (3 : ZMod 9137)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_9151 : Nat.Prime 9151 := by
  apply lucas_primality 9151 (3 : ZMod 9151)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9151 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((61 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 9151)^4575 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 9151)^3050 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 9151)^1830 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (3 : ZMod 9151)^150 ≠ 1
          reduce_mod_char
          decide

theorem prime_9173 : Nat.Prime 9173 := by
  apply lucas_primality 9173 (2 : ZMod 9173)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9173 - 1 = (2 : ℕ)^2 * ((2293 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9173)^4586 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 2293 := Nat.prime_eq_prime_of_dvd_pow hq prime_2293 hd
      subst q
      change (2 : ZMod 9173)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_9181 : Nat.Prime 9181 := by
  apply lucas_primality 9181 (2 : ZMod 9181)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9181 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((17 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9181)^4590 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 9181)^3060 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 9181)^1836 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 9181)^540 ≠ 1
          reduce_mod_char
          decide

theorem prime_9199 : Nat.Prime 9199 := by
  apply lucas_primality 9199 (3 : ZMod 9199)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9199 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((73 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 9199)^4599 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 9199)^3066 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 9199)^1314 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
          subst q
          change (3 : ZMod 9199)^126 ≠ 1
          reduce_mod_char
          decide

theorem prime_9221 : Nat.Prime 9221 := by
  apply lucas_primality 9221 (2 : ZMod 9221)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9221 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((461 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9221)^4610 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 9221)^1844 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 461 := Nat.prime_eq_prime_of_dvd_pow hq prime_461 hd
        subst q
        change (2 : ZMod 9221)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_9241 : Nat.Prime 9241 := by
  apply lucas_primality 9241 (13 : ZMod 9241)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9241 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 9241)^4620 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 9241)^3080 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 9241)^1848 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (13 : ZMod 9241)^1320 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (13 : ZMod 9241)^840 ≠ 1
            reduce_mod_char
            decide

theorem prime_9257 : Nat.Prime 9257 := by
  apply lucas_primality 9257 (3 : ZMod 9257)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9257 - 1 = (2 : ℕ)^3 * ((13 : ℕ)^1 * ((89 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 9257)^4628 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 9257)^712 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
        subst q
        change (3 : ZMod 9257)^104 ≠ 1
        reduce_mod_char
        decide

theorem prime_9281 : Nat.Prime 9281 := by
  apply lucas_primality 9281 (3 : ZMod 9281)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9281 - 1 = (2 : ℕ)^6 * ((5 : ℕ)^1 * ((29 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 9281)^4640 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 9281)^1856 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (3 : ZMod 9281)^320 ≠ 1
        reduce_mod_char
        decide

theorem prime_9293 : Nat.Prime 9293 := by
  apply lucas_primality 9293 (2 : ZMod 9293)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9293 - 1 = (2 : ℕ)^2 * ((23 : ℕ)^1 * ((101 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9293)^4646 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (2 : ZMod 9293)^404 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
        subst q
        change (2 : ZMod 9293)^92 ≠ 1
        reduce_mod_char
        decide

theorem prime_9349 : Nat.Prime 9349 := by
  apply lucas_primality 9349 (2 : ZMod 9349)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9349 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((41 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9349)^4674 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 9349)^3116 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 9349)^492 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (2 : ZMod 9349)^228 ≠ 1
          reduce_mod_char
          decide

theorem prime_9403 : Nat.Prime 9403 := by
  apply lucas_primality 9403 (3 : ZMod 9403)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9403 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1567 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 9403)^4701 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 9403)^3134 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1567 := Nat.prime_eq_prime_of_dvd_pow hq prime_1567 hd
        subst q
        change (3 : ZMod 9403)^6 ≠ 1
        reduce_mod_char
        decide

end LegendreK6.Pratt
