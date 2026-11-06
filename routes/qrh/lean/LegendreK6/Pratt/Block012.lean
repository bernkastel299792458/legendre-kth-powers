import LegendreK6.Pratt.Block011

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LegendreK6.Pratt

theorem prime_1811731 : Nat.Prime 1811731 := by
  apply lucas_primality 1811731 (2 : ZMod 1811731)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1811731 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((131 : ℕ)^1 * ((461 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1811731)^905865 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1811731)^603910 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 1811731)^362346 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
            subst q
            change (2 : ZMod 1811731)^13830 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 461 := Nat.prime_eq_prime_of_dvd_pow hq prime_461 hd
            subst q
            change (2 : ZMod 1811731)^3930 ≠ 1
            reduce_mod_char
            decide

theorem prime_1811983 : Nat.Prime 1811983 := by
  apply lucas_primality 1811983 (3 : ZMod 1811983)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1811983 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((301997 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1811983)^905991 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1811983)^603994 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 301997 := Nat.prime_eq_prime_of_dvd_pow hq prime_301997 hd
        subst q
        change (3 : ZMod 1811983)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_1814669 : Nat.Prime 1814669 := by
  apply lucas_primality 1814669 (2 : ZMod 1814669)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1814669 - 1 = (2 : ℕ)^2 * ((453667 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1814669)^907334 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 453667 := Nat.prime_eq_prime_of_dvd_pow hq prime_453667 hd
      subst q
      change (2 : ZMod 1814669)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_1815403 : Nat.Prime 1815403 := by
  apply lucas_primality 1815403 (5 : ZMod 1815403)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1815403 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((302567 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1815403)^907701 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1815403)^605134 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 302567 := Nat.prime_eq_prime_of_dvd_pow hq prime_302567 hd
        subst q
        change (5 : ZMod 1815403)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_1823293 : Nat.Prime 1823293 := by
  apply lucas_primality 1823293 (2 : ZMod 1823293)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1823293 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((50647 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1823293)^911646 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1823293)^607764 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 50647 := Nat.prime_eq_prime_of_dvd_pow hq prime_50647 hd
        subst q
        change (2 : ZMod 1823293)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_1825157 : Nat.Prime 1825157 := by
  apply lucas_primality 1825157 (2 : ZMod 1825157)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1825157 - 1 = (2 : ℕ)^2 * ((31 : ℕ)^1 * ((41 : ℕ)^1 * ((359 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1825157)^912578 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (2 : ZMod 1825157)^58876 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (2 : ZMod 1825157)^44516 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 359 := Nat.prime_eq_prime_of_dvd_pow hq prime_359 hd
          subst q
          change (2 : ZMod 1825157)^5084 ≠ 1
          reduce_mod_char
          decide

theorem prime_1836581 : Nat.Prime 1836581 := by
  apply lucas_primality 1836581 (2 : ZMod 1836581)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1836581 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((229 : ℕ)^1 * ((401 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1836581)^918290 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 1836581)^367316 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 229 := Nat.prime_eq_prime_of_dvd_pow hq prime_229 hd
          subst q
          change (2 : ZMod 1836581)^8020 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 401 := Nat.prime_eq_prime_of_dvd_pow hq prime_401 hd
          subst q
          change (2 : ZMod 1836581)^4580 ≠ 1
          reduce_mod_char
          decide

theorem prime_1865329 : Nat.Prime 1865329 := by
  apply lucas_primality 1865329 (13 : ZMod 1865329)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1865329 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((38861 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 1865329)^932664 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 1865329)^621776 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 38861 := Nat.prime_eq_prime_of_dvd_pow hq prime_38861 hd
        subst q
        change (13 : ZMod 1865329)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_1868717 : Nat.Prime 1868717 := by
  apply lucas_primality 1868717 (2 : ZMod 1868717)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1868717 - 1 = (2 : ℕ)^2 * ((139 : ℕ)^1 * ((3361 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1868717)^934358 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
        subst q
        change (2 : ZMod 1868717)^13444 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3361 := Nat.prime_eq_prime_of_dvd_pow hq prime_3361 hd
        subst q
        change (2 : ZMod 1868717)^556 ≠ 1
        reduce_mod_char
        decide

theorem prime_1873409 : Nat.Prime 1873409 := by
  apply lucas_primality 1873409 (3 : ZMod 1873409)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1873409 - 1 = (2 : ℕ)^9 * ((3659 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1873409)^936704 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3659 := Nat.prime_eq_prime_of_dvd_pow hq prime_3659 hd
      subst q
      change (3 : ZMod 1873409)^512 ≠ 1
      reduce_mod_char
      decide

theorem prime_1873441 : Nat.Prime 1873441 := by
  apply lucas_primality 1873441 (13 : ZMod 1873441)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1873441 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((1301 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 1873441)^936720 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 1873441)^624480 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 1873441)^374688 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1301 := Nat.prime_eq_prime_of_dvd_pow hq prime_1301 hd
          subst q
          change (13 : ZMod 1873441)^1440 ≠ 1
          reduce_mod_char
          decide

theorem prime_1878677 : Nat.Prime 1878677 := by
  apply lucas_primality 1878677 (2 : ZMod 1878677)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1878677 - 1 = (2 : ℕ)^2 * ((191 : ℕ)^1 * ((2459 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1878677)^939338 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
        subst q
        change (2 : ZMod 1878677)^9836 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2459 := Nat.prime_eq_prime_of_dvd_pow hq prime_2459 hd
        subst q
        change (2 : ZMod 1878677)^764 ≠ 1
        reduce_mod_char
        decide

theorem prime_1888763 : Nat.Prime 1888763 := by
  apply lucas_primality 1888763 (2 : ZMod 1888763)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1888763 - 1 = (2 : ℕ)^1 * ((409 : ℕ)^1 * ((2309 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1888763)^944381 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 409 := Nat.prime_eq_prime_of_dvd_pow hq prime_409 hd
        subst q
        change (2 : ZMod 1888763)^4618 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2309 := Nat.prime_eq_prime_of_dvd_pow hq prime_2309 hd
        subst q
        change (2 : ZMod 1888763)^818 ≠ 1
        reduce_mod_char
        decide

theorem prime_1900049 : Nat.Prime 1900049 := by
  apply lucas_primality 1900049 (3 : ZMod 1900049)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1900049 - 1 = (2 : ℕ)^4 * ((149 : ℕ)^1 * ((797 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1900049)^950024 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
        subst q
        change (3 : ZMod 1900049)^12752 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 797 := Nat.prime_eq_prime_of_dvd_pow hq prime_797 hd
        subst q
        change (3 : ZMod 1900049)^2384 ≠ 1
        reduce_mod_char
        decide

theorem prime_1912583 : Nat.Prime 1912583 := by
  apply lucas_primality 1912583 (5 : ZMod 1912583)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1912583 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((67 : ℕ)^1 * ((2039 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1912583)^956291 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 1912583)^273226 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (5 : ZMod 1912583)^28546 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2039 := Nat.prime_eq_prime_of_dvd_pow hq prime_2039 hd
          subst q
          change (5 : ZMod 1912583)^938 ≠ 1
          reduce_mod_char
          decide

theorem prime_1912951 : Nat.Prime 1912951 := by
  apply lucas_primality 1912951 (6 : ZMod 1912951)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1912951 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((5 : ℕ)^2 * ((13 : ℕ)^1 * ((109 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 1912951)^956475 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 1912951)^637650 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 1912951)^382590 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (6 : ZMod 1912951)^147150 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
            subst q
            change (6 : ZMod 1912951)^17550 ≠ 1
            reduce_mod_char
            decide

theorem prime_1916443 : Nat.Prime 1916443 := by
  apply lucas_primality 1916443 (2 : ZMod 1916443)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1916443 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((9679 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1916443)^958221 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1916443)^638814 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 1916443)^174222 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 9679 := Nat.prime_eq_prime_of_dvd_pow hq prime_9679 hd
          subst q
          change (2 : ZMod 1916443)^198 ≠ 1
          reduce_mod_char
          decide

theorem prime_1953101 : Nat.Prime 1953101 := by
  apply lucas_primality 1953101 (2 : ZMod 1953101)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1953101 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((19531 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1953101)^976550 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 1953101)^390620 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 19531 := Nat.prime_eq_prime_of_dvd_pow hq prime_19531 hd
        subst q
        change (2 : ZMod 1953101)^100 ≠ 1
        reduce_mod_char
        decide

theorem prime_1970519 : Nat.Prime 1970519 := by
  apply lucas_primality 1970519 (11 : ZMod 1970519)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1970519 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((43 : ℕ)^1 * ((2083 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 1970519)^985259 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (11 : ZMod 1970519)^179138 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (11 : ZMod 1970519)^45826 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2083 := Nat.prime_eq_prime_of_dvd_pow hq prime_2083 hd
          subst q
          change (11 : ZMod 1970519)^946 ≠ 1
          reduce_mod_char
          decide

theorem prime_1986913 : Nat.Prime 1986913 := by
  apply lucas_primality 1986913 (5 : ZMod 1986913)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1986913 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^2 * ((6899 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1986913)^993456 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1986913)^662304 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 6899 := Nat.prime_eq_prime_of_dvd_pow hq prime_6899 hd
        subst q
        change (5 : ZMod 1986913)^288 ≠ 1
        reduce_mod_char
        decide

theorem prime_2011601 : Nat.Prime 2011601 := by
  apply lucas_primality 2011601 (3 : ZMod 2011601)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2011601 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^2 * ((47 : ℕ)^1 * ((107 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2011601)^1005800 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 2011601)^402320 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (3 : ZMod 2011601)^42800 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
          subst q
          change (3 : ZMod 2011601)^18800 ≠ 1
          reduce_mod_char
          decide

theorem prime_2016139 : Nat.Prime 2016139 := by
  apply lucas_primality 2016139 (2 : ZMod 2016139)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2016139 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((29 : ℕ)^1 * ((11587 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2016139)^1008069 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2016139)^672046 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (2 : ZMod 2016139)^69522 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11587 := Nat.prime_eq_prime_of_dvd_pow hq prime_11587 hd
          subst q
          change (2 : ZMod 2016139)^174 ≠ 1
          reduce_mod_char
          decide

theorem prime_2019133 : Nat.Prime 2019133 := by
  apply lucas_primality 2019133 (2 : ZMod 2019133)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2019133 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((56087 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2019133)^1009566 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2019133)^673044 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 56087 := Nat.prime_eq_prime_of_dvd_pow hq prime_56087 hd
        subst q
        change (2 : ZMod 2019133)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_2026841 : Nat.Prime 2026841 := by
  apply lucas_primality 2026841 (6 : ZMod 2026841)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2026841 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((50671 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 2026841)^1013420 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 2026841)^405368 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 50671 := Nat.prime_eq_prime_of_dvd_pow hq prime_50671 hd
        subst q
        change (6 : ZMod 2026841)^40 ≠ 1
        reduce_mod_char
        decide

theorem prime_2028647 : Nat.Prime 2028647 := by
  apply lucas_primality 2028647 (5 : ZMod 2028647)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2028647 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((44101 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2028647)^1014323 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (5 : ZMod 2028647)^88202 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 44101 := Nat.prime_eq_prime_of_dvd_pow hq prime_44101 hd
        subst q
        change (5 : ZMod 2028647)^46 ≠ 1
        reduce_mod_char
        decide

theorem prime_2030981 : Nat.Prime 2030981 := by
  apply lucas_primality 2030981 (2 : ZMod 2030981)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2030981 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((89 : ℕ)^1 * ((163 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2030981)^1015490 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 2030981)^406196 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 2030981)^290140 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
            subst q
            change (2 : ZMod 2030981)^22820 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
            subst q
            change (2 : ZMod 2030981)^12460 ≠ 1
            reduce_mod_char
            decide

theorem prime_2043721 : Nat.Prime 2043721 := by
  apply lucas_primality 2043721 (23 : ZMod 2043721)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2043721 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((811 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (23 : ZMod 2043721)^1021860 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (23 : ZMod 2043721)^681240 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (23 : ZMod 2043721)^408744 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (23 : ZMod 2043721)^291960 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 811 := Nat.prime_eq_prime_of_dvd_pow hq prime_811 hd
            subst q
            change (23 : ZMod 2043721)^2520 ≠ 1
            reduce_mod_char
            decide

theorem prime_2051767 : Nat.Prime 2051767 := by
  apply lucas_primality 2051767 (3 : ZMod 2051767)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2051767 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((31 : ℕ)^1 * ((3677 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2051767)^1025883 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 2051767)^683922 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (3 : ZMod 2051767)^66186 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3677 := Nat.prime_eq_prime_of_dvd_pow hq prime_3677 hd
          subst q
          change (3 : ZMod 2051767)^558 ≠ 1
          reduce_mod_char
          decide

theorem prime_2081033 : Nat.Prime 2081033 := by
  apply lucas_primality 2081033 (3 : ZMod 2081033)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2081033 - 1 = (2 : ℕ)^3 * ((19 : ℕ)^1 * ((13691 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2081033)^1040516 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (3 : ZMod 2081033)^109528 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13691 := Nat.prime_eq_prime_of_dvd_pow hq prime_13691 hd
        subst q
        change (3 : ZMod 2081033)^152 ≠ 1
        reduce_mod_char
        decide

theorem prime_2084009 : Nat.Prime 2084009 := by
  apply lucas_primality 2084009 (3 : ZMod 2084009)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2084009 - 1 = (2 : ℕ)^3 * ((337 : ℕ)^1 * ((773 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2084009)^1042004 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 337 := Nat.prime_eq_prime_of_dvd_pow hq prime_337 hd
        subst q
        change (3 : ZMod 2084009)^6184 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 773 := Nat.prime_eq_prime_of_dvd_pow hq prime_773 hd
        subst q
        change (3 : ZMod 2084009)^2696 ≠ 1
        reduce_mod_char
        decide

theorem prime_2088913 : Nat.Prime 2088913 := by
  apply lucas_primality 2088913 (10 : ZMod 2088913)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2088913 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((6217 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 2088913)^1044456 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 2088913)^696304 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (10 : ZMod 2088913)^298416 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 6217 := Nat.prime_eq_prime_of_dvd_pow hq prime_6217 hd
          subst q
          change (10 : ZMod 2088913)^336 ≠ 1
          reduce_mod_char
          decide

theorem prime_2091269 : Nat.Prime 2091269 := by
  apply lucas_primality 2091269 (2 : ZMod 2091269)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2091269 - 1 = (2 : ℕ)^2 * ((83 : ℕ)^1 * ((6299 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2091269)^1045634 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
        subst q
        change (2 : ZMod 2091269)^25196 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 6299 := Nat.prime_eq_prime_of_dvd_pow hq prime_6299 hd
        subst q
        change (2 : ZMod 2091269)^332 ≠ 1
        reduce_mod_char
        decide

theorem prime_2113039 : Nat.Prime 2113039 := by
  apply lucas_primality 2113039 (3 : ZMod 2113039)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2113039 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((89 : ℕ)^1 * ((1319 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2113039)^1056519 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 2113039)^704346 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (3 : ZMod 2113039)^23742 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1319 := Nat.prime_eq_prime_of_dvd_pow hq prime_1319 hd
          subst q
          change (3 : ZMod 2113039)^1602 ≠ 1
          reduce_mod_char
          decide

theorem prime_2113957 : Nat.Prime 2113957 := by
  apply lucas_primality 2113957 (2 : ZMod 2113957)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2113957 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((13 : ℕ)^1 * ((4517 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2113957)^1056978 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2113957)^704652 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 2113957)^162612 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4517 := Nat.prime_eq_prime_of_dvd_pow hq prime_4517 hd
          subst q
          change (2 : ZMod 2113957)^468 ≠ 1
          reduce_mod_char
          decide

theorem prime_2116663 : Nat.Prime 2116663 := by
  apply lucas_primality 2116663 (5 : ZMod 2116663)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2116663 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((191 : ℕ)^1 * ((1847 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2116663)^1058331 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 2116663)^705554 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
          subst q
          change (5 : ZMod 2116663)^11082 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1847 := Nat.prime_eq_prime_of_dvd_pow hq prime_1847 hd
          subst q
          change (5 : ZMod 2116663)^1146 ≠ 1
          reduce_mod_char
          decide

theorem prime_2122723 : Nat.Prime 2122723 := by
  apply lucas_primality 2122723 (2 : ZMod 2122723)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2122723 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((17 : ℕ)^1 * ((991 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2122723)^1061361 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2122723)^707574 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 2122723)^303246 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (2 : ZMod 2122723)^124866 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 991 := Nat.prime_eq_prime_of_dvd_pow hq prime_991 hd
            subst q
            change (2 : ZMod 2122723)^2142 ≠ 1
            reduce_mod_char
            decide

theorem prime_2124443 : Nat.Prime 2124443 := by
  apply lucas_primality 2124443 (2 : ZMod 2124443)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2124443 - 1 = (2 : ℕ)^1 * ((149 : ℕ)^1 * ((7129 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2124443)^1062221 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
        subst q
        change (2 : ZMod 2124443)^14258 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7129 := Nat.prime_eq_prime_of_dvd_pow hq prime_7129 hd
        subst q
        change (2 : ZMod 2124443)^298 ≠ 1
        reduce_mod_char
        decide

theorem prime_2130013 : Nat.Prime 2130013 := by
  apply lucas_primality 2130013 (6 : ZMod 2130013)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2130013 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((59167 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 2130013)^1065006 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 2130013)^710004 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 59167 := Nat.prime_eq_prime_of_dvd_pow hq prime_59167 hd
        subst q
        change (6 : ZMod 2130013)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_2187421 : Nat.Prime 2187421 := by
  apply lucas_primality 2187421 (2 : ZMod 2187421)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2187421 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((36457 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2187421)^1093710 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2187421)^729140 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 2187421)^437484 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 36457 := Nat.prime_eq_prime_of_dvd_pow hq prime_36457 hd
          subst q
          change (2 : ZMod 2187421)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_2191339 : Nat.Prime 2191339 := by
  apply lucas_primality 2191339 (13 : ZMod 2191339)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2191339 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((53 : ℕ)^1 * ((2297 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 2191339)^1095669 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 2191339)^730446 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (13 : ZMod 2191339)^41346 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2297 := Nat.prime_eq_prime_of_dvd_pow hq prime_2297 hd
          subst q
          change (13 : ZMod 2191339)^954 ≠ 1
          reduce_mod_char
          decide

theorem prime_2207831 : Nat.Prime 2207831 := by
  apply lucas_primality 2207831 (13 : ZMod 2207831)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2207831 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((220783 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 2207831)^1103915 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (13 : ZMod 2207831)^441566 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 220783 := Nat.prime_eq_prime_of_dvd_pow hq prime_220783 hd
        subst q
        change (13 : ZMod 2207831)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_2213839 : Nat.Prime 2213839 := by
  apply lucas_primality 2213839 (6 : ZMod 2213839)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2213839 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((11 : ℕ)^1 * ((3727 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 2213839)^1106919 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 2213839)^737946 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (6 : ZMod 2213839)^201258 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3727 := Nat.prime_eq_prime_of_dvd_pow hq prime_3727 hd
          subst q
          change (6 : ZMod 2213839)^594 ≠ 1
          reduce_mod_char
          decide

theorem prime_2217491 : Nat.Prime 2217491 := by
  apply lucas_primality 2217491 (6 : ZMod 2217491)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2217491 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((19 : ℕ)^1 * ((1061 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 2217491)^1108745 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 2217491)^443498 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (6 : ZMod 2217491)^201590 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (6 : ZMod 2217491)^116710 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1061 := Nat.prime_eq_prime_of_dvd_pow hq prime_1061 hd
            subst q
            change (6 : ZMod 2217491)^2090 ≠ 1
            reduce_mod_char
            decide

theorem prime_2254033 : Nat.Prime 2254033 := by
  apply lucas_primality 2254033 (7 : ZMod 2254033)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2254033 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((1423 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2254033)^1127016 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 2254033)^751344 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (7 : ZMod 2254033)^204912 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1423 := Nat.prime_eq_prime_of_dvd_pow hq prime_1423 hd
          subst q
          change (7 : ZMod 2254033)^1584 ≠ 1
          reduce_mod_char
          decide

theorem prime_2278141 : Nat.Prime 2278141 := by
  apply lucas_primality 2278141 (2 : ZMod 2278141)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2278141 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((43 : ℕ)^1 * ((883 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2278141)^1139070 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2278141)^759380 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 2278141)^455628 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (2 : ZMod 2278141)^52980 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 883 := Nat.prime_eq_prime_of_dvd_pow hq prime_883 hd
            subst q
            change (2 : ZMod 2278141)^2580 ≠ 1
            reduce_mod_char
            decide

theorem prime_2287171 : Nat.Prime 2287171 := by
  apply lucas_primality 2287171 (10 : ZMod 2287171)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2287171 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((43 : ℕ)^1 * ((197 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 2287171)^1143585 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 2287171)^762390 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 2287171)^457434 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (10 : ZMod 2287171)^53190 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
            subst q
            change (10 : ZMod 2287171)^11610 ≠ 1
            reduce_mod_char
            decide

theorem prime_2300267 : Nat.Prime 2300267 := by
  apply lucas_primality 2300267 (2 : ZMod 2300267)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2300267 - 1 = (2 : ℕ)^1 * ((281 : ℕ)^1 * ((4093 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2300267)^1150133 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 281 := Nat.prime_eq_prime_of_dvd_pow hq prime_281 hd
        subst q
        change (2 : ZMod 2300267)^8186 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4093 := Nat.prime_eq_prime_of_dvd_pow hq prime_4093 hd
        subst q
        change (2 : ZMod 2300267)^562 ≠ 1
        reduce_mod_char
        decide

theorem prime_2308297 : Nat.Prime 2308297 := by
  apply lucas_primality 2308297 (7 : ZMod 2308297)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2308297 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((96179 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2308297)^1154148 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 2308297)^769432 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 96179 := Nat.prime_eq_prime_of_dvd_pow hq prime_96179 hd
        subst q
        change (7 : ZMod 2308297)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_2311921 : Nat.Prime 2311921 := by
  apply lucas_primality 2311921 (11 : ZMod 2311921)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2311921 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((13 : ℕ)^2 * ((19 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 2311921)^1155960 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 2311921)^770640 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 2311921)^462384 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (11 : ZMod 2311921)^177840 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (11 : ZMod 2311921)^121680 ≠ 1
            reduce_mod_char
            decide

theorem prime_2312573 : Nat.Prime 2312573 := by
  apply lucas_primality 2312573 (2 : ZMod 2312573)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2312573 - 1 = (2 : ℕ)^2 * ((67 : ℕ)^1 * ((8629 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2312573)^1156286 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
        subst q
        change (2 : ZMod 2312573)^34516 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 8629 := Nat.prime_eq_prime_of_dvd_pow hq prime_8629 hd
        subst q
        change (2 : ZMod 2312573)^268 ≠ 1
        reduce_mod_char
        decide

theorem prime_2331587 : Nat.Prime 2331587 := by
  apply lucas_primality 2331587 (2 : ZMod 2331587)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2331587 - 1 = (2 : ℕ)^1 * ((139 : ℕ)^1 * ((8387 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2331587)^1165793 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
        subst q
        change (2 : ZMod 2331587)^16774 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 8387 := Nat.prime_eq_prime_of_dvd_pow hq prime_8387 hd
        subst q
        change (2 : ZMod 2331587)^278 ≠ 1
        reduce_mod_char
        decide

theorem prime_2334743 : Nat.Prime 2334743 := by
  apply lucas_primality 2334743 (5 : ZMod 2334743)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2334743 - 1 = (2 : ℕ)^1 * ((353 : ℕ)^1 * ((3307 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2334743)^1167371 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 353 := Nat.prime_eq_prime_of_dvd_pow hq prime_353 hd
        subst q
        change (5 : ZMod 2334743)^6614 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3307 := Nat.prime_eq_prime_of_dvd_pow hq prime_3307 hd
        subst q
        change (5 : ZMod 2334743)^706 ≠ 1
        reduce_mod_char
        decide

theorem prime_2340493 : Nat.Prime 2340493 := by
  apply lucas_primality 2340493 (2 : ZMod 2340493)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2340493 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((149 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2340493)^1170246 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2340493)^780164 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 2340493)^334356 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (2 : ZMod 2340493)^212772 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
              subst q
              change (2 : ZMod 2340493)^137676 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
              subst q
              change (2 : ZMod 2340493)^15708 ≠ 1
              reduce_mod_char
              decide

theorem prime_2342657 : Nat.Prime 2342657 := by
  apply lucas_primality 2342657 (3 : ZMod 2342657)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2342657 - 1 = (2 : ℕ)^8 * ((9151 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2342657)^1171328 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 9151 := Nat.prime_eq_prime_of_dvd_pow hq prime_9151 hd
      subst q
      change (3 : ZMod 2342657)^256 ≠ 1
      reduce_mod_char
      decide

theorem prime_2347727 : Nat.Prime 2347727 := by
  apply lucas_primality 2347727 (5 : ZMod 2347727)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2347727 - 1 = (2 : ℕ)^1 * ((433 : ℕ)^1 * ((2711 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2347727)^1173863 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 433 := Nat.prime_eq_prime_of_dvd_pow hq prime_433 hd
        subst q
        change (5 : ZMod 2347727)^5422 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2711 := Nat.prime_eq_prime_of_dvd_pow hq prime_2711 hd
        subst q
        change (5 : ZMod 2347727)^866 ≠ 1
        reduce_mod_char
        decide

theorem prime_2360459 : Nat.Prime 2360459 := by
  apply lucas_primality 2360459 (2 : ZMod 2360459)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2360459 - 1 = (2 : ℕ)^1 * ((89 : ℕ)^2 * ((149 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2360459)^1180229 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
        subst q
        change (2 : ZMod 2360459)^26522 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
        subst q
        change (2 : ZMod 2360459)^15842 ≠ 1
        reduce_mod_char
        decide

theorem prime_2361041 : Nat.Prime 2361041 := by
  apply lucas_primality 2361041 (13 : ZMod 2361041)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2361041 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((2683 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 2361041)^1180520 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (13 : ZMod 2361041)^472208 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (13 : ZMod 2361041)^214640 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2683 := Nat.prime_eq_prime_of_dvd_pow hq prime_2683 hd
          subst q
          change (13 : ZMod 2361041)^880 ≠ 1
          reduce_mod_char
          decide

theorem prime_2363177 : Nat.Prime 2363177 := by
  apply lucas_primality 2363177 (3 : ZMod 2363177)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2363177 - 1 = (2 : ℕ)^3 * ((83 : ℕ)^1 * ((3559 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2363177)^1181588 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
        subst q
        change (3 : ZMod 2363177)^28472 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3559 := Nat.prime_eq_prime_of_dvd_pow hq prime_3559 hd
        subst q
        change (3 : ZMod 2363177)^664 ≠ 1
        reduce_mod_char
        decide

theorem prime_2392619 : Nat.Prime 2392619 := by
  apply lucas_primality 2392619 (2 : ZMod 2392619)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2392619 - 1 = (2 : ℕ)^1 * ((1196309 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2392619)^1196309 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1196309 := Nat.prime_eq_prime_of_dvd_pow hq prime_1196309 hd
      subst q
      change (2 : ZMod 2392619)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_2417153 : Nat.Prime 2417153 := by
  apply lucas_primality 2417153 (3 : ZMod 2417153)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2417153 - 1 = (2 : ℕ)^9 * ((4721 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2417153)^1208576 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 4721 := Nat.prime_eq_prime_of_dvd_pow hq prime_4721 hd
      subst q
      change (3 : ZMod 2417153)^512 ≠ 1
      reduce_mod_char
      decide

theorem prime_2420611 : Nat.Prime 2420611 := by
  apply lucas_primality 2420611 (10 : ZMod 2420611)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2420611 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((80687 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 2420611)^1210305 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 2420611)^806870 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 2420611)^484122 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 80687 := Nat.prime_eq_prime_of_dvd_pow hq prime_80687 hd
          subst q
          change (10 : ZMod 2420611)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_2428997 : Nat.Prime 2428997 := by
  apply lucas_primality 2428997 (2 : ZMod 2428997)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2428997 - 1 = (2 : ℕ)^2 * ((607249 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2428997)^1214498 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 607249 := Nat.prime_eq_prime_of_dvd_pow hq prime_607249 hd
      subst q
      change (2 : ZMod 2428997)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_2452339 : Nat.Prime 2452339 := by
  apply lucas_primality 2452339 (2 : ZMod 2452339)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2452339 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((19463 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2452339)^1226169 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2452339)^817446 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 2452339)^350334 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 19463 := Nat.prime_eq_prime_of_dvd_pow hq prime_19463 hd
          subst q
          change (2 : ZMod 2452339)^126 ≠ 1
          reduce_mod_char
          decide

theorem prime_2483219 : Nat.Prime 2483219 := by
  apply lucas_primality 2483219 (2 : ZMod 2483219)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2483219 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((37 : ℕ)^1 * ((1459 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2483219)^1241609 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (2 : ZMod 2483219)^107966 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (2 : ZMod 2483219)^67114 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1459 := Nat.prime_eq_prime_of_dvd_pow hq prime_1459 hd
          subst q
          change (2 : ZMod 2483219)^1702 ≠ 1
          reduce_mod_char
          decide

theorem prime_2519423 : Nat.Prime 2519423 := by
  apply lucas_primality 2519423 (5 : ZMod 2519423)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2519423 - 1 = (2 : ℕ)^1 * ((61 : ℕ)^1 * ((107 : ℕ)^1 * ((193 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2519423)^1259711 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
        subst q
        change (5 : ZMod 2519423)^41302 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
          subst q
          change (5 : ZMod 2519423)^23546 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
          subst q
          change (5 : ZMod 2519423)^13054 ≠ 1
          reduce_mod_char
          decide

theorem prime_2523671 : Nat.Prime 2523671 := by
  apply lucas_primality 2523671 (13 : ZMod 2523671)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2523671 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((43 : ℕ)^1 * ((5869 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 2523671)^1261835 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (13 : ZMod 2523671)^504734 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (13 : ZMod 2523671)^58690 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 5869 := Nat.prime_eq_prime_of_dvd_pow hq prime_5869 hd
          subst q
          change (13 : ZMod 2523671)^430 ≠ 1
          reduce_mod_char
          decide

theorem prime_2529361 : Nat.Prime 2529361 := by
  apply lucas_primality 2529361 (11 : ZMod 2529361)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2529361 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((1171 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 2529361)^1264680 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 2529361)^843120 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 2529361)^505872 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1171 := Nat.prime_eq_prime_of_dvd_pow hq prime_1171 hd
          subst q
          change (11 : ZMod 2529361)^2160 ≠ 1
          reduce_mod_char
          decide

theorem prime_2546293 : Nat.Prime 2546293 := by
  apply lucas_primality 2546293 (15 : ZMod 2546293)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2546293 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((30313 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (15 : ZMod 2546293)^1273146 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (15 : ZMod 2546293)^848764 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (15 : ZMod 2546293)^363756 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 30313 := Nat.prime_eq_prime_of_dvd_pow hq prime_30313 hd
          subst q
          change (15 : ZMod 2546293)^84 ≠ 1
          reduce_mod_char
          decide

theorem prime_2552717 : Nat.Prime 2552717 := by
  apply lucas_primality 2552717 (2 : ZMod 2552717)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2552717 - 1 = (2 : ℕ)^2 * ((638179 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2552717)^1276358 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 638179 := Nat.prime_eq_prime_of_dvd_pow hq prime_638179 hd
      subst q
      change (2 : ZMod 2552717)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_2568361 : Nat.Prime 2568361 := by
  apply lucas_primality 2568361 (7 : ZMod 2568361)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2568361 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((1259 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2568361)^1284180 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 2568361)^856120 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 2568361)^513672 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (7 : ZMod 2568361)^151080 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1259 := Nat.prime_eq_prime_of_dvd_pow hq prime_1259 hd
            subst q
            change (7 : ZMod 2568361)^2040 ≠ 1
            reduce_mod_char
            decide

theorem prime_2570671 : Nat.Prime 2570671 := by
  apply lucas_primality 2570671 (6 : ZMod 2570671)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2570671 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((9521 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 2570671)^1285335 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 2570671)^856890 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 2570671)^514134 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 9521 := Nat.prime_eq_prime_of_dvd_pow hq prime_9521 hd
          subst q
          change (6 : ZMod 2570671)^270 ≠ 1
          reduce_mod_char
          decide

theorem prime_2572811 : Nat.Prime 2572811 := by
  apply lucas_primality 2572811 (6 : ZMod 2572811)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2572811 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((257281 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 2572811)^1286405 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 2572811)^514562 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 257281 := Nat.prime_eq_prime_of_dvd_pow hq prime_257281 hd
        subst q
        change (6 : ZMod 2572811)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_2584511 : Nat.Prime 2584511 := by
  apply lucas_primality 2584511 (13 : ZMod 2584511)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2584511 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((23 : ℕ)^1 * ((661 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 2584511)^1292255 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (13 : ZMod 2584511)^516902 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (13 : ZMod 2584511)^152030 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (13 : ZMod 2584511)^112370 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 661 := Nat.prime_eq_prime_of_dvd_pow hq prime_661 hd
            subst q
            change (13 : ZMod 2584511)^3910 ≠ 1
            reduce_mod_char
            decide

theorem prime_2586313 : Nat.Prime 2586313 := by
  apply lucas_primality 2586313 (10 : ZMod 2586313)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2586313 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((17 : ℕ)^1 * ((2113 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 2586313)^1293156 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 2586313)^862104 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (10 : ZMod 2586313)^152136 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2113 := Nat.prime_eq_prime_of_dvd_pow hq prime_2113 hd
          subst q
          change (10 : ZMod 2586313)^1224 ≠ 1
          reduce_mod_char
          decide

theorem prime_2608601 : Nat.Prime 2608601 := by
  apply lucas_primality 2608601 (11 : ZMod 2608601)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2608601 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^2 * ((13043 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 2608601)^1304300 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 2608601)^521720 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13043 := Nat.prime_eq_prime_of_dvd_pow hq prime_13043 hd
        subst q
        change (11 : ZMod 2608601)^200 ≠ 1
        reduce_mod_char
        decide

theorem prime_2622749 : Nat.Prime 2622749 := by
  apply lucas_primality 2622749 (2 : ZMod 2622749)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2622749 - 1 = (2 : ℕ)^2 * ((655687 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2622749)^1311374 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 655687 := Nat.prime_eq_prime_of_dvd_pow hq prime_655687 hd
      subst q
      change (2 : ZMod 2622749)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_2626753 : Nat.Prime 2626753 := by
  apply lucas_primality 2626753 (5 : ZMod 2626753)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2626753 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^1 * ((13681 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2626753)^1313376 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 2626753)^875584 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13681 := Nat.prime_eq_prime_of_dvd_pow hq prime_13681 hd
        subst q
        change (5 : ZMod 2626753)^192 ≠ 1
        reduce_mod_char
        decide

theorem prime_2633581 : Nat.Prime 2633581 := by
  apply lucas_primality 2633581 (2 : ZMod 2633581)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2633581 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((4877 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2633581)^1316790 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2633581)^877860 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 2633581)^526716 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4877 := Nat.prime_eq_prime_of_dvd_pow hq prime_4877 hd
          subst q
          change (2 : ZMod 2633581)^540 ≠ 1
          reduce_mod_char
          decide

theorem prime_2648383 : Nat.Prime 2648383 := by
  apply lucas_primality 2648383 (6 : ZMod 2648383)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2648383 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((40127 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 2648383)^1324191 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 2648383)^882794 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (6 : ZMod 2648383)^240762 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 40127 := Nat.prime_eq_prime_of_dvd_pow hq prime_40127 hd
          subst q
          change (6 : ZMod 2648383)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_2650663 : Nat.Prime 2650663 := by
  apply lucas_primality 2650663 (7 : ZMod 2650663)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2650663 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((109 : ℕ)^1 * ((193 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2650663)^1325331 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 2650663)^883554 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 2650663)^378666 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
            subst q
            change (7 : ZMod 2650663)^24318 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
            subst q
            change (7 : ZMod 2650663)^13734 ≠ 1
            reduce_mod_char
            decide

theorem prime_2660533 : Nat.Prime 2660533 := by
  apply lucas_primality 2660533 (11 : ZMod 2660533)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2660533 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((19 : ℕ)^1 * ((1667 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 2660533)^1330266 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 2660533)^886844 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (11 : ZMod 2660533)^380076 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (11 : ZMod 2660533)^140028 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1667 := Nat.prime_eq_prime_of_dvd_pow hq prime_1667 hd
            subst q
            change (11 : ZMod 2660533)^1596 ≠ 1
            reduce_mod_char
            decide

theorem prime_2673211 : Nat.Prime 2673211 := by
  apply lucas_primality 2673211 (2 : ZMod 2673211)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2673211 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((89107 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2673211)^1336605 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2673211)^891070 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 2673211)^534642 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 89107 := Nat.prime_eq_prime_of_dvd_pow hq prime_89107 hd
          subst q
          change (2 : ZMod 2673211)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_2685077 : Nat.Prime 2685077 := by
  apply lucas_primality 2685077 (2 : ZMod 2685077)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2685077 - 1 = (2 : ℕ)^2 * ((671269 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2685077)^1342538 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 671269 := Nat.prime_eq_prime_of_dvd_pow hq prime_671269 hd
      subst q
      change (2 : ZMod 2685077)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_2745929 : Nat.Prime 2745929 := by
  apply lucas_primality 2745929 (3 : ZMod 2745929)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2745929 - 1 = (2 : ℕ)^3 * ((47 : ℕ)^1 * ((67 : ℕ)^1 * ((109 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2745929)^1372964 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (3 : ZMod 2745929)^58424 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (3 : ZMod 2745929)^40984 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
          subst q
          change (3 : ZMod 2745929)^25192 ≠ 1
          reduce_mod_char
          decide

theorem prime_2779747 : Nat.Prime 2779747 := by
  apply lucas_primality 2779747 (2 : ZMod 2779747)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2779747 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((463291 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2779747)^1389873 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2779747)^926582 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 463291 := Nat.prime_eq_prime_of_dvd_pow hq prime_463291 hd
        subst q
        change (2 : ZMod 2779747)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_2786579 : Nat.Prime 2786579 := by
  apply lucas_primality 2786579 (2 : ZMod 2786579)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2786579 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((73331 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2786579)^1393289 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 2786579)^146662 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 73331 := Nat.prime_eq_prime_of_dvd_pow hq prime_73331 hd
        subst q
        change (2 : ZMod 2786579)^38 ≠ 1
        reduce_mod_char
        decide

theorem prime_2789627 : Nat.Prime 2789627 := by
  apply lucas_primality 2789627 (2 : ZMod 2789627)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2789627 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((29 : ℕ)^1 * ((6871 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2789627)^1394813 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 2789627)^398518 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (2 : ZMod 2789627)^96194 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 6871 := Nat.prime_eq_prime_of_dvd_pow hq prime_6871 hd
          subst q
          change (2 : ZMod 2789627)^406 ≠ 1
          reduce_mod_char
          decide

theorem prime_2811569 : Nat.Prime 2811569 := by
  apply lucas_primality 2811569 (3 : ZMod 2811569)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2811569 - 1 = (2 : ℕ)^4 * ((175723 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2811569)^1405784 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 175723 := Nat.prime_eq_prime_of_dvd_pow hq prime_175723 hd
      subst q
      change (3 : ZMod 2811569)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_2825491 : Nat.Prime 2825491 := by
  apply lucas_primality 2825491 (3 : ZMod 2825491)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2825491 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((19 : ℕ)^1 * ((4957 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2825491)^1412745 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 2825491)^941830 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 2825491)^565098 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (3 : ZMod 2825491)^148710 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 4957 := Nat.prime_eq_prime_of_dvd_pow hq prime_4957 hd
            subst q
            change (3 : ZMod 2825491)^570 ≠ 1
            reduce_mod_char
            decide

theorem prime_2834047 : Nat.Prime 2834047 := by
  apply lucas_primality 2834047 (13 : ZMod 2834047)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2834047 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((79 : ℕ)^1 * ((1993 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 2834047)^1417023 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 2834047)^944682 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (13 : ZMod 2834047)^35874 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1993 := Nat.prime_eq_prime_of_dvd_pow hq prime_1993 hd
          subst q
          change (13 : ZMod 2834047)^1422 ≠ 1
          reduce_mod_char
          decide

theorem prime_2835433 : Nat.Prime 2835433 := by
  apply lucas_primality 2835433 (5 : ZMod 2835433)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2835433 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((13127 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2835433)^1417716 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 2835433)^945144 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13127 := Nat.prime_eq_prime_of_dvd_pow hq prime_13127 hd
        subst q
        change (5 : ZMod 2835433)^216 ≠ 1
        reduce_mod_char
        decide

theorem prime_2838079 : Nat.Prime 2838079 := by
  apply lucas_primality 2838079 (6 : ZMod 2838079)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2838079 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((17519 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 2838079)^1419039 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 2838079)^946026 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 17519 := Nat.prime_eq_prime_of_dvd_pow hq prime_17519 hd
        subst q
        change (6 : ZMod 2838079)^162 ≠ 1
        reduce_mod_char
        decide

theorem prime_2875393 : Nat.Prime 2875393 := by
  apply lucas_primality 2875393 (5 : ZMod 2875393)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2875393 - 1 = (2 : ℕ)^13 * ((3 : ℕ)^3 * ((13 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2875393)^1437696 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 2875393)^958464 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (5 : ZMod 2875393)^221184 ≠ 1
        reduce_mod_char
        decide

theorem prime_2877463 : Nat.Prime 2877463 := by
  apply lucas_primality 2877463 (3 : ZMod 2877463)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2877463 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((41 : ℕ)^1 * ((557 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2877463)^1438731 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 2877463)^959154 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 2877463)^411066 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (3 : ZMod 2877463)^70182 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 557 := Nat.prime_eq_prime_of_dvd_pow hq prime_557 hd
            subst q
            change (3 : ZMod 2877463)^5166 ≠ 1
            reduce_mod_char
            decide

theorem prime_2879927 : Nat.Prime 2879927 := by
  apply lucas_primality 2879927 (5 : ZMod 2879927)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2879927 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^2 * ((29387 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2879927)^1439963 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 2879927)^411418 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 29387 := Nat.prime_eq_prime_of_dvd_pow hq prime_29387 hd
        subst q
        change (5 : ZMod 2879927)^98 ≠ 1
        reduce_mod_char
        decide

theorem prime_2896507 : Nat.Prime 2896507 := by
  apply lucas_primality 2896507 (5 : ZMod 2896507)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2896507 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((53639 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2896507)^1448253 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 2896507)^965502 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 53639 := Nat.prime_eq_prime_of_dvd_pow hq prime_53639 hd
        subst q
        change (5 : ZMod 2896507)^54 ≠ 1
        reduce_mod_char
        decide

theorem prime_2902931 : Nat.Prime 2902931 := by
  apply lucas_primality 2902931 (2 : ZMod 2902931)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2902931 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((43 : ℕ)^2 * ((157 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2902931)^1451465 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 2902931)^580586 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (2 : ZMod 2902931)^67510 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
          subst q
          change (2 : ZMod 2902931)^18490 ≠ 1
          reduce_mod_char
          decide

theorem prime_2918297 : Nat.Prime 2918297 := by
  apply lucas_primality 2918297 (3 : ZMod 2918297)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2918297 - 1 = (2 : ℕ)^3 * ((283 : ℕ)^1 * ((1289 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2918297)^1459148 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 283 := Nat.prime_eq_prime_of_dvd_pow hq prime_283 hd
        subst q
        change (3 : ZMod 2918297)^10312 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1289 := Nat.prime_eq_prime_of_dvd_pow hq prime_1289 hd
        subst q
        change (3 : ZMod 2918297)^2264 ≠ 1
        reduce_mod_char
        decide

theorem prime_2926181 : Nat.Prime 2926181 := by
  apply lucas_primality 2926181 (2 : ZMod 2926181)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2926181 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((146309 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2926181)^1463090 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 2926181)^585236 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 146309 := Nat.prime_eq_prime_of_dvd_pow hq prime_146309 hd
        subst q
        change (2 : ZMod 2926181)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_2936039 : Nat.Prime 2936039 := by
  apply lucas_primality 2936039 (7 : ZMod 2936039)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2936039 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((209717 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2936039)^1468019 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 2936039)^419434 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 209717 := Nat.prime_eq_prime_of_dvd_pow hq prime_209717 hd
        subst q
        change (7 : ZMod 2936039)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_2967607 : Nat.Prime 2967607 := by
  apply lucas_primality 2967607 (3 : ZMod 2967607)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2967607 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((113 : ℕ)^1 * ((1459 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2967607)^1483803 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 2967607)^989202 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
          subst q
          change (3 : ZMod 2967607)^26262 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1459 := Nat.prime_eq_prime_of_dvd_pow hq prime_1459 hd
          subst q
          change (3 : ZMod 2967607)^2034 ≠ 1
          reduce_mod_char
          decide

theorem prime_2972219 : Nat.Prime 2972219 := by
  apply lucas_primality 2972219 (2 : ZMod 2972219)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2972219 - 1 = (2 : ℕ)^1 * ((31 : ℕ)^1 * ((47939 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2972219)^1486109 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (2 : ZMod 2972219)^95878 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 47939 := Nat.prime_eq_prime_of_dvd_pow hq prime_47939 hd
        subst q
        change (2 : ZMod 2972219)^62 ≠ 1
        reduce_mod_char
        decide

theorem prime_2976671 : Nat.Prime 2976671 := by
  apply lucas_primality 2976671 (11 : ZMod 2976671)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2976671 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((197 : ℕ)^1 * ((1511 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 2976671)^1488335 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 2976671)^595334 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
          subst q
          change (11 : ZMod 2976671)^15110 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1511 := Nat.prime_eq_prime_of_dvd_pow hq prime_1511 hd
          subst q
          change (11 : ZMod 2976671)^1970 ≠ 1
          reduce_mod_char
          decide

theorem prime_2985991 : Nat.Prime 2985991 := by
  apply lucas_primality 2985991 (13 : ZMod 2985991)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2985991 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((59 : ℕ)^1 * ((241 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 2985991)^1492995 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 2985991)^995330 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 2985991)^597198 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (13 : ZMod 2985991)^426570 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
              subst q
              change (13 : ZMod 2985991)^50610 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 241 := Nat.prime_eq_prime_of_dvd_pow hq prime_241 hd
              subst q
              change (13 : ZMod 2985991)^12390 ≠ 1
              reduce_mod_char
              decide

theorem prime_2989309 : Nat.Prime 2989309 := by
  apply lucas_primality 2989309 (2 : ZMod 2989309)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2989309 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((19 : ℕ)^1 * ((1873 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2989309)^1494654 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2989309)^996436 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 2989309)^427044 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (2 : ZMod 2989309)^157332 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1873 := Nat.prime_eq_prime_of_dvd_pow hq prime_1873 hd
            subst q
            change (2 : ZMod 2989309)^1596 ≠ 1
            reduce_mod_char
            decide

theorem prime_2990513 : Nat.Prime 2990513 := by
  apply lucas_primality 2990513 (3 : ZMod 2990513)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2990513 - 1 = (2 : ℕ)^4 * ((7 : ℕ)^1 * ((26701 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2990513)^1495256 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 2990513)^427216 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 26701 := Nat.prime_eq_prime_of_dvd_pow hq prime_26701 hd
        subst q
        change (3 : ZMod 2990513)^112 ≠ 1
        reduce_mod_char
        decide

theorem prime_3001387 : Nat.Prime 3001387 := by
  apply lucas_primality 3001387 (3 : ZMod 3001387)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3001387 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((500231 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3001387)^1500693 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3001387)^1000462 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 500231 := Nat.prime_eq_prime_of_dvd_pow hq prime_500231 hd
        subst q
        change (3 : ZMod 3001387)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_3025331 : Nat.Prime 3025331 := by
  apply lucas_primality 3025331 (6 : ZMod 3025331)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3025331 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((3929 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 3025331)^1512665 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 3025331)^605066 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 3025331)^432190 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (6 : ZMod 3025331)^275030 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3929 := Nat.prime_eq_prime_of_dvd_pow hq prime_3929 hd
            subst q
            change (6 : ZMod 3025331)^770 ≠ 1
            reduce_mod_char
            decide

theorem prime_3033169 : Nat.Prime 3033169 := by
  apply lucas_primality 3033169 (7 : ZMod 3033169)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3033169 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((29 : ℕ)^1 * ((2179 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 3033169)^1516584 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 3033169)^1011056 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (7 : ZMod 3033169)^104592 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2179 := Nat.prime_eq_prime_of_dvd_pow hq prime_2179 hd
          subst q
          change (7 : ZMod 3033169)^1392 ≠ 1
          reduce_mod_char
          decide

theorem prime_3037583 : Nat.Prime 3037583 := by
  apply lucas_primality 3037583 (5 : ZMod 3037583)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3037583 - 1 = (2 : ℕ)^1 * ((277 : ℕ)^1 * ((5483 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3037583)^1518791 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 277 := Nat.prime_eq_prime_of_dvd_pow hq prime_277 hd
        subst q
        change (5 : ZMod 3037583)^10966 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5483 := Nat.prime_eq_prime_of_dvd_pow hq prime_5483 hd
        subst q
        change (5 : ZMod 3037583)^554 ≠ 1
        reduce_mod_char
        decide

theorem prime_3071317 : Nat.Prime 3071317 := by
  apply lucas_primality 3071317 (2 : ZMod 3071317)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3071317 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((211 : ℕ)^1 * ((1213 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3071317)^1535658 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3071317)^1023772 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 211 := Nat.prime_eq_prime_of_dvd_pow hq prime_211 hd
          subst q
          change (2 : ZMod 3071317)^14556 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1213 := Nat.prime_eq_prime_of_dvd_pow hq prime_1213 hd
          subst q
          change (2 : ZMod 3071317)^2532 ≠ 1
          reduce_mod_char
          decide

theorem prime_3072413 : Nat.Prime 3072413 := by
  apply lucas_primality 3072413 (5 : ZMod 3072413)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3072413 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((197 : ℕ)^1 * ((557 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3072413)^1536206 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 3072413)^438916 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
          subst q
          change (5 : ZMod 3072413)^15596 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 557 := Nat.prime_eq_prime_of_dvd_pow hq prime_557 hd
          subst q
          change (5 : ZMod 3072413)^5516 ≠ 1
          reduce_mod_char
          decide

theorem prime_3077621 : Nat.Prime 3077621 := by
  apply lucas_primality 3077621 (2 : ZMod 3077621)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3077621 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((19 : ℕ)^1 * ((89 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3077621)^1538810 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 3077621)^615524 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 3077621)^439660 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (2 : ZMod 3077621)^236740 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
              subst q
              change (2 : ZMod 3077621)^161980 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
              subst q
              change (2 : ZMod 3077621)^34580 ≠ 1
              reduce_mod_char
              decide

theorem prime_3080393 : Nat.Prime 3080393 := by
  apply lucas_primality 3080393 (3 : ZMod 3080393)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3080393 - 1 = (2 : ℕ)^3 * ((7 : ℕ)^1 * ((67 : ℕ)^1 * ((821 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3080393)^1540196 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 3080393)^440056 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (3 : ZMod 3080393)^45976 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 821 := Nat.prime_eq_prime_of_dvd_pow hq prime_821 hd
          subst q
          change (3 : ZMod 3080393)^3752 ≠ 1
          reduce_mod_char
          decide

theorem prime_3082771 : Nat.Prime 3082771 := by
  apply lucas_primality 3082771 (2 : ZMod 3082771)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3082771 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((34253 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3082771)^1541385 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3082771)^1027590 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 3082771)^616554 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 34253 := Nat.prime_eq_prime_of_dvd_pow hq prime_34253 hd
          subst q
          change (2 : ZMod 3082771)^90 ≠ 1
          reduce_mod_char
          decide

theorem prime_3082889 : Nat.Prime 3082889 := by
  apply lucas_primality 3082889 (3 : ZMod 3082889)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3082889 - 1 = (2 : ℕ)^3 * ((31 : ℕ)^2 * ((401 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3082889)^1541444 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (3 : ZMod 3082889)^99448 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 401 := Nat.prime_eq_prime_of_dvd_pow hq prime_401 hd
        subst q
        change (3 : ZMod 3082889)^7688 ≠ 1
        reduce_mod_char
        decide

theorem prime_3097123 : Nat.Prime 3097123 := by
  apply lucas_primality 3097123 (2 : ZMod 3097123)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3097123 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((37 : ℕ)^1 * ((1993 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3097123)^1548561 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3097123)^1032374 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 3097123)^442446 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
            subst q
            change (2 : ZMod 3097123)^83706 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1993 := Nat.prime_eq_prime_of_dvd_pow hq prime_1993 hd
            subst q
            change (2 : ZMod 3097123)^1554 ≠ 1
            reduce_mod_char
            decide

theorem prime_3152239 : Nat.Prime 3152239 := by
  apply lucas_primality 3152239 (3 : ZMod 3152239)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3152239 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((525373 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3152239)^1576119 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3152239)^1050746 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 525373 := Nat.prime_eq_prime_of_dvd_pow hq prime_525373 hd
        subst q
        change (3 : ZMod 3152239)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_3208889 : Nat.Prime 3208889 := by
  apply lucas_primality 3208889 (3 : ZMod 3208889)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3208889 - 1 = (2 : ℕ)^3 * ((211 : ℕ)^1 * ((1901 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3208889)^1604444 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 211 := Nat.prime_eq_prime_of_dvd_pow hq prime_211 hd
        subst q
        change (3 : ZMod 3208889)^15208 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1901 := Nat.prime_eq_prime_of_dvd_pow hq prime_1901 hd
        subst q
        change (3 : ZMod 3208889)^1688 ≠ 1
        reduce_mod_char
        decide

theorem prime_3209363 : Nat.Prime 3209363 := by
  apply lucas_primality 3209363 (2 : ZMod 3209363)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3209363 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((17 : ℕ)^1 * ((53 : ℕ)^1 * ((137 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3209363)^1604681 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 3209363)^246874 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 3209363)^188786 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
            subst q
            change (2 : ZMod 3209363)^60554 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
            subst q
            change (2 : ZMod 3209363)^23426 ≠ 1
            reduce_mod_char
            decide

theorem prime_3251749 : Nat.Prime 3251749 := by
  apply lucas_primality 3251749 (10 : ZMod 3251749)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3251749 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((233 : ℕ)^1 * ((1163 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 3251749)^1625874 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 3251749)^1083916 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
          subst q
          change (10 : ZMod 3251749)^13956 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1163 := Nat.prime_eq_prime_of_dvd_pow hq prime_1163 hd
          subst q
          change (10 : ZMod 3251749)^2796 ≠ 1
          reduce_mod_char
          decide

theorem prime_3295723 : Nat.Prime 3295723 := by
  apply lucas_primality 3295723 (2 : ZMod 3295723)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3295723 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((79 : ℕ)^1 * ((409 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3295723)^1647861 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3295723)^1098574 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 3295723)^193866 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
            subst q
            change (2 : ZMod 3295723)^41718 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 409 := Nat.prime_eq_prime_of_dvd_pow hq prime_409 hd
            subst q
            change (2 : ZMod 3295723)^8058 ≠ 1
            reduce_mod_char
            decide

theorem prime_3315031 : Nat.Prime 3315031 := by
  apply lucas_primality 3315031 (6 : ZMod 3315031)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3315031 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((110501 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 3315031)^1657515 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 3315031)^1105010 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 3315031)^663006 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 110501 := Nat.prime_eq_prime_of_dvd_pow hq prime_110501 hd
          subst q
          change (6 : ZMod 3315031)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_3319621 : Nat.Prime 3319621 := by
  apply lucas_primality 3319621 (10 : ZMod 3319621)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3319621 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((61 : ℕ)^1 * ((907 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 3319621)^1659810 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 3319621)^1106540 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 3319621)^663924 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
            subst q
            change (10 : ZMod 3319621)^54420 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 907 := Nat.prime_eq_prime_of_dvd_pow hq prime_907 hd
            subst q
            change (10 : ZMod 3319621)^3660 ≠ 1
            reduce_mod_char
            decide

theorem prime_3321917 : Nat.Prime 3321917 := by
  apply lucas_primality 3321917 (2 : ZMod 3321917)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3321917 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((193 : ℕ)^1 * ((331 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3321917)^1660958 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 3321917)^255532 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
          subst q
          change (2 : ZMod 3321917)^17212 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 331 := Nat.prime_eq_prime_of_dvd_pow hq prime_331 hd
          subst q
          change (2 : ZMod 3321917)^10036 ≠ 1
          reduce_mod_char
          decide

theorem prime_3334819 : Nat.Prime 3334819 := by
  apply lucas_primality 3334819 (3 : ZMod 3334819)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3334819 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((101 : ℕ)^1 * ((5503 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3334819)^1667409 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3334819)^1111606 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
          subst q
          change (3 : ZMod 3334819)^33018 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 5503 := Nat.prime_eq_prime_of_dvd_pow hq prime_5503 hd
          subst q
          change (3 : ZMod 3334819)^606 ≠ 1
          reduce_mod_char
          decide

theorem prime_3335273 : Nat.Prime 3335273 := by
  apply lucas_primality 3335273 (3 : ZMod 3335273)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3335273 - 1 = (2 : ℕ)^3 * ((83 : ℕ)^1 * ((5023 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3335273)^1667636 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
        subst q
        change (3 : ZMod 3335273)^40184 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5023 := Nat.prime_eq_prime_of_dvd_pow hq prime_5023 hd
        subst q
        change (3 : ZMod 3335273)^664 ≠ 1
        reduce_mod_char
        decide

theorem prime_3366917 : Nat.Prime 3366917 := by
  apply lucas_primality 3366917 (2 : ZMod 3366917)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3366917 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((120247 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3366917)^1683458 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 3366917)^480988 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 120247 := Nat.prime_eq_prime_of_dvd_pow hq prime_120247 hd
        subst q
        change (2 : ZMod 3366917)^28 ≠ 1
        reduce_mod_char
        decide

theorem prime_3377051 : Nat.Prime 3377051 := by
  apply lucas_primality 3377051 (2 : ZMod 3377051)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3377051 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((17 : ℕ)^1 * ((29 : ℕ)^1 * ((137 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3377051)^1688525 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 3377051)^675410 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 3377051)^198650 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (2 : ZMod 3377051)^116450 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
            subst q
            change (2 : ZMod 3377051)^24650 ≠ 1
            reduce_mod_char
            decide

theorem prime_3388087 : Nat.Prime 3388087 := by
  apply lucas_primality 3388087 (3 : ZMod 3388087)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3388087 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((13 : ℕ)^1 * ((14479 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3388087)^1694043 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3388087)^1129362 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 3388087)^260622 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 14479 := Nat.prime_eq_prime_of_dvd_pow hq prime_14479 hd
          subst q
          change (3 : ZMod 3388087)^234 ≠ 1
          reduce_mod_char
          decide

theorem prime_3394843 : Nat.Prime 3394843 := by
  apply lucas_primality 3394843 (2 : ZMod 3394843)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3394843 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((51437 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3394843)^1697421 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3394843)^1131614 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 3394843)^308622 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 51437 := Nat.prime_eq_prime_of_dvd_pow hq prime_51437 hd
          subst q
          change (2 : ZMod 3394843)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_3410369 : Nat.Prime 3410369 := by
  apply lucas_primality 3410369 (3 : ZMod 3410369)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3410369 - 1 = (2 : ℕ)^6 * ((13 : ℕ)^1 * ((4099 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3410369)^1705184 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 3410369)^262336 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4099 := Nat.prime_eq_prime_of_dvd_pow hq prime_4099 hd
        subst q
        change (3 : ZMod 3410369)^832 ≠ 1
        reduce_mod_char
        decide

theorem prime_3418049 : Nat.Prime 3418049 := by
  apply lucas_primality 3418049 (3 : ZMod 3418049)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3418049 - 1 = (2 : ℕ)^6 * ((53407 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3418049)^1709024 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 53407 := Nat.prime_eq_prime_of_dvd_pow hq prime_53407 hd
      subst q
      change (3 : ZMod 3418049)^64 ≠ 1
      reduce_mod_char
      decide

theorem prime_3420121 : Nat.Prime 3420121 := by
  apply lucas_primality 3420121 (7 : ZMod 3420121)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3420121 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((2591 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 3420121)^1710060 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 3420121)^1140040 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 3420121)^684024 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (7 : ZMod 3420121)^310920 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2591 := Nat.prime_eq_prime_of_dvd_pow hq prime_2591 hd
            subst q
            change (7 : ZMod 3420121)^1320 ≠ 1
            reduce_mod_char
            decide

theorem prime_3477137 : Nat.Prime 3477137 := by
  apply lucas_primality 3477137 (3 : ZMod 3477137)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3477137 - 1 = (2 : ℕ)^4 * ((13 : ℕ)^1 * ((73 : ℕ)^1 * ((229 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3477137)^1738568 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 3477137)^267472 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
          subst q
          change (3 : ZMod 3477137)^47632 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 229 := Nat.prime_eq_prime_of_dvd_pow hq prime_229 hd
          subst q
          change (3 : ZMod 3477137)^15184 ≠ 1
          reduce_mod_char
          decide

theorem prime_3487387 : Nat.Prime 3487387 := by
  apply lucas_primality 3487387 (2 : ZMod 3487387)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3487387 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((43 : ℕ)^1 * ((1931 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3487387)^1743693 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3487387)^1162462 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 3487387)^498198 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (2 : ZMod 3487387)^81102 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1931 := Nat.prime_eq_prime_of_dvd_pow hq prime_1931 hd
            subst q
            change (2 : ZMod 3487387)^1806 ≠ 1
            reduce_mod_char
            decide

theorem prime_3496579 : Nat.Prime 3496579 := by
  apply lucas_primality 3496579 (3 : ZMod 3496579)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3496579 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((582763 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3496579)^1748289 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3496579)^1165526 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 582763 := Nat.prime_eq_prime_of_dvd_pow hq prime_582763 hd
        subst q
        change (3 : ZMod 3496579)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_3498493 : Nat.Prime 3498493 := by
  apply lucas_primality 3498493 (2 : ZMod 3498493)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3498493 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((47 : ℕ)^1 * ((6203 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3498493)^1749246 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3498493)^1166164 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (2 : ZMod 3498493)^74436 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 6203 := Nat.prime_eq_prime_of_dvd_pow hq prime_6203 hd
          subst q
          change (2 : ZMod 3498493)^564 ≠ 1
          reduce_mod_char
          decide

theorem prime_3542323 : Nat.Prime 3542323 := by
  apply lucas_primality 3542323 (3 : ZMod 3542323)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3542323 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((19 : ℕ)^1 * ((23 : ℕ)^1 * ((193 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3542323)^1771161 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3542323)^1180774 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 3542323)^506046 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (3 : ZMod 3542323)^186438 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
              subst q
              change (3 : ZMod 3542323)^154014 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
              subst q
              change (3 : ZMod 3542323)^18354 ≠ 1
              reduce_mod_char
              decide

theorem prime_3575371 : Nat.Prime 3575371 := by
  apply lucas_primality 3575371 (3 : ZMod 3575371)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3575371 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((119179 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3575371)^1787685 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3575371)^1191790 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 3575371)^715074 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 119179 := Nat.prime_eq_prime_of_dvd_pow hq prime_119179 hd
          subst q
          change (3 : ZMod 3575371)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_3599083 : Nat.Prime 3599083 := by
  apply lucas_primality 3599083 (2 : ZMod 3599083)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3599083 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((79 : ℕ)^1 * ((2531 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3599083)^1799541 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3599083)^1199694 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (2 : ZMod 3599083)^45558 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2531 := Nat.prime_eq_prime_of_dvd_pow hq prime_2531 hd
          subst q
          change (2 : ZMod 3599083)^1422 ≠ 1
          reduce_mod_char
          decide

theorem prime_3614981 : Nat.Prime 3614981 := by
  apply lucas_primality 3614981 (2 : ZMod 3614981)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3614981 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((180749 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3614981)^1807490 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 3614981)^722996 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 180749 := Nat.prime_eq_prime_of_dvd_pow hq prime_180749 hd
        subst q
        change (2 : ZMod 3614981)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_3616637 : Nat.Prime 3616637 := by
  apply lucas_primality 3616637 (2 : ZMod 3616637)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3616637 - 1 = (2 : ℕ)^2 * ((577 : ℕ)^1 * ((1567 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3616637)^1808318 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 577 := Nat.prime_eq_prime_of_dvd_pow hq prime_577 hd
        subst q
        change (2 : ZMod 3616637)^6268 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1567 := Nat.prime_eq_prime_of_dvd_pow hq prime_1567 hd
        subst q
        change (2 : ZMod 3616637)^2308 ≠ 1
        reduce_mod_char
        decide

theorem prime_3617221 : Nat.Prime 3617221 := by
  apply lucas_primality 3617221 (2 : ZMod 3617221)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3617221 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((19 : ℕ)^2 * ((167 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3617221)^1808610 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3617221)^1205740 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 3617221)^723444 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (2 : ZMod 3617221)^190380 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
            subst q
            change (2 : ZMod 3617221)^21660 ≠ 1
            reduce_mod_char
            decide

theorem prime_3637801 : Nat.Prime 3637801 := by
  apply lucas_primality 3637801 (17 : ZMod 3637801)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3637801 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((5 : ℕ)^2 * ((43 : ℕ)^1 * ((47 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 3637801)^1818900 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 3637801)^1212600 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (17 : ZMod 3637801)^727560 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (17 : ZMod 3637801)^84600 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
            subst q
            change (17 : ZMod 3637801)^77400 ≠ 1
            reduce_mod_char
            decide

theorem prime_3658327 : Nat.Prime 3658327 := by
  apply lucas_primality 3658327 (3 : ZMod 3658327)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3658327 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((87103 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3658327)^1829163 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3658327)^1219442 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 3658327)^522618 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 87103 := Nat.prime_eq_prime_of_dvd_pow hq prime_87103 hd
          subst q
          change (3 : ZMod 3658327)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_3681023 : Nat.Prime 3681023 := by
  apply lucas_primality 3681023 (5 : ZMod 3681023)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3681023 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((157 : ℕ)^1 * ((617 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3681023)^1840511 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (5 : ZMod 3681023)^193738 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
          subst q
          change (5 : ZMod 3681023)^23446 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 617 := Nat.prime_eq_prime_of_dvd_pow hq prime_617 hd
          subst q
          change (5 : ZMod 3681023)^5966 ≠ 1
          reduce_mod_char
          decide

theorem prime_3685963 : Nat.Prime 3685963 := by
  apply lucas_primality 3685963 (2 : ZMod 3685963)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3685963 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((19 : ℕ)^1 * ((31 : ℕ)^1 * ((149 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3685963)^1842981 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3685963)^1228654 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 3685963)^526566 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (2 : ZMod 3685963)^193998 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
              subst q
              change (2 : ZMod 3685963)^118902 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
              subst q
              change (2 : ZMod 3685963)^24738 ≠ 1
              reduce_mod_char
              decide

theorem prime_3696821 : Nat.Prime 3696821 := by
  apply lucas_primality 3696821 (10 : ZMod 3696821)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3696821 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((83 : ℕ)^1 * ((131 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 3696821)^1848410 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (10 : ZMod 3696821)^739364 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (10 : ZMod 3696821)^217460 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
            subst q
            change (10 : ZMod 3696821)^44540 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
            subst q
            change (10 : ZMod 3696821)^28220 ≠ 1
            reduce_mod_char
            decide

theorem prime_3702893 : Nat.Prime 3702893 := by
  apply lucas_primality 3702893 (2 : ZMod 3702893)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3702893 - 1 = (2 : ℕ)^2 * ((173 : ℕ)^1 * ((5351 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3702893)^1851446 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
        subst q
        change (2 : ZMod 3702893)^21404 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5351 := Nat.prime_eq_prime_of_dvd_pow hq prime_5351 hd
        subst q
        change (2 : ZMod 3702893)^692 ≠ 1
        reduce_mod_char
        decide

theorem prime_3760147 : Nat.Prime 3760147 := by
  apply lucas_primality 3760147 (2 : ZMod 3760147)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3760147 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((13 : ℕ)^1 * ((16069 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3760147)^1880073 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3760147)^1253382 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 3760147)^289242 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 16069 := Nat.prime_eq_prime_of_dvd_pow hq prime_16069 hd
          subst q
          change (2 : ZMod 3760147)^234 ≠ 1
          reduce_mod_char
          decide

theorem prime_3783449 : Nat.Prime 3783449 := by
  apply lucas_primality 3783449 (3 : ZMod 3783449)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3783449 - 1 = (2 : ℕ)^3 * ((71 : ℕ)^1 * ((6661 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3783449)^1891724 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
        subst q
        change (3 : ZMod 3783449)^53288 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 6661 := Nat.prime_eq_prime_of_dvd_pow hq prime_6661 hd
        subst q
        change (3 : ZMod 3783449)^568 ≠ 1
        reduce_mod_char
        decide

theorem prime_3801953 : Nat.Prime 3801953 := by
  apply lucas_primality 3801953 (5 : ZMod 3801953)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3801953 - 1 = (2 : ℕ)^5 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((1543 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3801953)^1900976 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 3801953)^543136 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 3801953)^345632 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1543 := Nat.prime_eq_prime_of_dvd_pow hq prime_1543 hd
          subst q
          change (5 : ZMod 3801953)^2464 ≠ 1
          reduce_mod_char
          decide

theorem prime_3812623 : Nat.Prime 3812623 := by
  apply lucas_primality 3812623 (11 : ZMod 3812623)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3812623 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((61 : ℕ)^1 * ((947 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 3812623)^1906311 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 3812623)^1270874 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (11 : ZMod 3812623)^346602 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
            subst q
            change (11 : ZMod 3812623)^62502 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 947 := Nat.prime_eq_prime_of_dvd_pow hq prime_947 hd
            subst q
            change (11 : ZMod 3812623)^4026 ≠ 1
            reduce_mod_char
            decide

theorem prime_3815597 : Nat.Prime 3815597 := by
  apply lucas_primality 3815597 (2 : ZMod 3815597)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3815597 - 1 = (2 : ℕ)^2 * ((433 : ℕ)^1 * ((2203 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3815597)^1907798 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 433 := Nat.prime_eq_prime_of_dvd_pow hq prime_433 hd
        subst q
        change (2 : ZMod 3815597)^8812 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2203 := Nat.prime_eq_prime_of_dvd_pow hq prime_2203 hd
        subst q
        change (2 : ZMod 3815597)^1732 ≠ 1
        reduce_mod_char
        decide

theorem prime_3820853 : Nat.Prime 3820853 := by
  apply lucas_primality 3820853 (3 : ZMod 3820853)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3820853 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((17 : ℕ)^1 * ((23 : ℕ)^1 * ((349 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3820853)^1910426 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 3820853)^545836 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (3 : ZMod 3820853)^224756 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (3 : ZMod 3820853)^166124 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 349 := Nat.prime_eq_prime_of_dvd_pow hq prime_349 hd
            subst q
            change (3 : ZMod 3820853)^10948 ≠ 1
            reduce_mod_char
            decide

theorem prime_3824591 : Nat.Prime 3824591 := by
  apply lucas_primality 3824591 (7 : ZMod 3824591)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3824591 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((4967 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 3824591)^1912295 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 3824591)^764918 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 3824591)^546370 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (7 : ZMod 3824591)^347690 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 4967 := Nat.prime_eq_prime_of_dvd_pow hq prime_4967 hd
            subst q
            change (7 : ZMod 3824591)^770 ≠ 1
            reduce_mod_char
            decide

theorem prime_3840703 : Nat.Prime 3840703 := by
  apply lucas_primality 3840703 (3 : ZMod 3840703)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3840703 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((29 : ℕ)^1 * ((22073 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3840703)^1920351 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3840703)^1280234 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (3 : ZMod 3840703)^132438 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 22073 := Nat.prime_eq_prime_of_dvd_pow hq prime_22073 hd
          subst q
          change (3 : ZMod 3840703)^174 ≠ 1
          reduce_mod_char
          decide

theorem prime_3900931 : Nat.Prime 3900931 := by
  apply lucas_primality 3900931 (3 : ZMod 3900931)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3900931 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((11821 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3900931)^1950465 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3900931)^1300310 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 3900931)^780186 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (3 : ZMod 3900931)^354630 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 11821 := Nat.prime_eq_prime_of_dvd_pow hq prime_11821 hd
            subst q
            change (3 : ZMod 3900931)^330 ≠ 1
            reduce_mod_char
            decide

theorem prime_3924499 : Nat.Prime 3924499 := by
  apply lucas_primality 3924499 (2 : ZMod 3924499)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3924499 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((131 : ℕ)^1 * ((4993 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3924499)^1962249 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3924499)^1308166 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
          subst q
          change (2 : ZMod 3924499)^29958 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4993 := Nat.prime_eq_prime_of_dvd_pow hq prime_4993 hd
          subst q
          change (2 : ZMod 3924499)^786 ≠ 1
          reduce_mod_char
          decide

theorem prime_3941039 : Nat.Prime 3941039 := by
  apply lucas_primality 3941039 (7 : ZMod 3941039)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3941039 - 1 = (2 : ℕ)^1 * ((1970519 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 3941039)^1970519 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1970519 := Nat.prime_eq_prime_of_dvd_pow hq prime_1970519 hd
      subst q
      change (7 : ZMod 3941039)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_3943631 : Nat.Prime 3943631 := by
  apply lucas_primality 3943631 (17 : ZMod 3943631)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3943631 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((394363 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 3943631)^1971815 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (17 : ZMod 3943631)^788726 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 394363 := Nat.prime_eq_prime_of_dvd_pow hq prime_394363 hd
        subst q
        change (17 : ZMod 3943631)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_3994537 : Nat.Prime 3994537 := by
  apply lucas_primality 3994537 (11 : ZMod 3994537)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3994537 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((31 : ℕ)^1 * ((59 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 3994537)^1997268 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 3994537)^1331512 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (11 : ZMod 3994537)^570648 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (11 : ZMod 3994537)^307272 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
              subst q
              change (11 : ZMod 3994537)^128856 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
              subst q
              change (11 : ZMod 3994537)^67704 ≠ 1
              reduce_mod_char
              decide

theorem prime_4007671 : Nat.Prime 4007671 := by
  apply lucas_primality 4007671 (6 : ZMod 4007671)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4007671 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((19 : ℕ)^1 * ((79 : ℕ)^1 * ((89 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 4007671)^2003835 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 4007671)^1335890 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 4007671)^801534 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (6 : ZMod 4007671)^210930 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
              subst q
              change (6 : ZMod 4007671)^50730 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
              subst q
              change (6 : ZMod 4007671)^45030 ≠ 1
              reduce_mod_char
              decide

theorem prime_4015013 : Nat.Prime 4015013 := by
  apply lucas_primality 4015013 (2 : ZMod 4015013)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4015013 - 1 = (2 : ℕ)^2 * ((1003753 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4015013)^2007506 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1003753 := Nat.prime_eq_prime_of_dvd_pow hq prime_1003753 hd
      subst q
      change (2 : ZMod 4015013)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_4090519 : Nat.Prime 4090519 := by
  apply lucas_primality 4090519 (6 : ZMod 4090519)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4090519 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((227251 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 4090519)^2045259 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 4090519)^1363506 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 227251 := Nat.prime_eq_prime_of_dvd_pow hq prime_227251 hd
        subst q
        change (6 : ZMod 4090519)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_4095401 : Nat.Prime 4095401 := by
  apply lucas_primality 4095401 (3 : ZMod 4095401)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4095401 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^2 * ((20477 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4095401)^2047700 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 4095401)^819080 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 20477 := Nat.prime_eq_prime_of_dvd_pow hq prime_20477 hd
        subst q
        change (3 : ZMod 4095401)^200 ≠ 1
        reduce_mod_char
        decide

theorem prime_4109201 : Nat.Prime 4109201 := by
  apply lucas_primality 4109201 (3 : ZMod 4109201)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4109201 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^2 * ((10273 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4109201)^2054600 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 4109201)^821840 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 10273 := Nat.prime_eq_prime_of_dvd_pow hq prime_10273 hd
        subst q
        change (3 : ZMod 4109201)^400 ≠ 1
        reduce_mod_char
        decide

theorem prime_4146661 : Nat.Prime 4146661 := by
  apply lucas_primality 4146661 (6 : ZMod 4146661)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4146661 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((1097 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 4146661)^2073330 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 4146661)^1382220 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 4146661)^829332 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (6 : ZMod 4146661)^592380 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1097 := Nat.prime_eq_prime_of_dvd_pow hq prime_1097 hd
            subst q
            change (6 : ZMod 4146661)^3780 ≠ 1
            reduce_mod_char
            decide

theorem prime_4167433 : Nat.Prime 4167433 := by
  apply lucas_primality 4167433 (10 : ZMod 4167433)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4167433 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((57881 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 4167433)^2083716 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 4167433)^1389144 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 57881 := Nat.prime_eq_prime_of_dvd_pow hq prime_57881 hd
        subst q
        change (10 : ZMod 4167433)^72 ≠ 1
        reduce_mod_char
        decide

theorem prime_4168159 : Nat.Prime 4168159 := by
  apply lucas_primality 4168159 (6 : ZMod 4168159)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4168159 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((131 : ℕ)^1 * ((5303 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 4168159)^2084079 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 4168159)^1389386 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
          subst q
          change (6 : ZMod 4168159)^31818 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 5303 := Nat.prime_eq_prime_of_dvd_pow hq prime_5303 hd
          subst q
          change (6 : ZMod 4168159)^786 ≠ 1
          reduce_mod_char
          decide

theorem prime_4173769 : Nat.Prime 4173769 := by
  apply lucas_primality 4173769 (7 : ZMod 4173769)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4173769 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^5 * ((19 : ℕ)^1 * ((113 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 4173769)^2086884 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 4173769)^1391256 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (7 : ZMod 4173769)^219672 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
          subst q
          change (7 : ZMod 4173769)^36936 ≠ 1
          reduce_mod_char
          decide

theorem prime_4217903 : Nat.Prime 4217903 := by
  apply lucas_primality 4217903 (5 : ZMod 4217903)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4217903 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^2 * ((12479 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 4217903)^2108951 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (5 : ZMod 4217903)^324454 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 12479 := Nat.prime_eq_prime_of_dvd_pow hq prime_12479 hd
        subst q
        change (5 : ZMod 4217903)^338 ≠ 1
        reduce_mod_char
        decide

theorem prime_4371911 : Nat.Prime 4371911 := by
  apply lucas_primality 4371911 (11 : ZMod 4371911)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4371911 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((437191 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 4371911)^2185955 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 4371911)^874382 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 437191 := Nat.prime_eq_prime_of_dvd_pow hq prime_437191 hd
        subst q
        change (11 : ZMod 4371911)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_4373701 : Nat.Prime 4373701 := by
  apply lucas_primality 4373701 (6 : ZMod 4373701)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4373701 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((61 : ℕ)^1 * ((239 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 4373701)^2186850 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 4373701)^1457900 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 4373701)^874740 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
            subst q
            change (6 : ZMod 4373701)^71700 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 239 := Nat.prime_eq_prime_of_dvd_pow hq prime_239 hd
            subst q
            change (6 : ZMod 4373701)^18300 ≠ 1
            reduce_mod_char
            decide

theorem prime_4375429 : Nat.Prime 4375429 := by
  apply lucas_primality 4375429 (2 : ZMod 4375429)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4375429 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((83 : ℕ)^1 * ((191 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4375429)^2187714 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 4375429)^1458476 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 4375429)^190236 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
            subst q
            change (2 : ZMod 4375429)^52716 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
            subst q
            change (2 : ZMod 4375429)^22908 ≠ 1
            reduce_mod_char
            decide

theorem prime_4380113 : Nat.Prime 4380113 := by
  apply lucas_primality 4380113 (3 : ZMod 4380113)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4380113 - 1 = (2 : ℕ)^4 * ((11 : ℕ)^1 * ((41 : ℕ)^1 * ((607 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4380113)^2190056 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 4380113)^398192 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (3 : ZMod 4380113)^106832 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 607 := Nat.prime_eq_prime_of_dvd_pow hq prime_607 hd
          subst q
          change (3 : ZMod 4380113)^7216 ≠ 1
          reduce_mod_char
          decide

theorem prime_4415633 : Nat.Prime 4415633 := by
  apply lucas_primality 4415633 (3 : ZMod 4415633)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4415633 - 1 = (2 : ℕ)^4 * ((13 : ℕ)^2 * ((23 : ℕ)^1 * ((71 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4415633)^2207816 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 4415633)^339664 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (3 : ZMod 4415633)^191984 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
          subst q
          change (3 : ZMod 4415633)^62192 ≠ 1
          reduce_mod_char
          decide

theorem prime_4442413 : Nat.Prime 4442413 := by
  apply lucas_primality 4442413 (5 : ZMod 4442413)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4442413 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((28477 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 4442413)^2221206 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 4442413)^1480804 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (5 : ZMod 4442413)^341724 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 28477 := Nat.prime_eq_prime_of_dvd_pow hq prime_28477 hd
          subst q
          change (5 : ZMod 4442413)^156 ≠ 1
          reduce_mod_char
          decide

theorem prime_4453817 : Nat.Prime 4453817 := by
  apply lucas_primality 4453817 (3 : ZMod 4453817)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4453817 - 1 = (2 : ℕ)^3 * ((556727 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4453817)^2226908 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 556727 := Nat.prime_eq_prime_of_dvd_pow hq prime_556727 hd
      subst q
      change (3 : ZMod 4453817)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_4467511 : Nat.Prime 4467511 := by
  apply lucas_primality 4467511 (6 : ZMod 4467511)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4467511 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((49639 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 4467511)^2233755 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 4467511)^1489170 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 4467511)^893502 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 49639 := Nat.prime_eq_prime_of_dvd_pow hq prime_49639 hd
          subst q
          change (6 : ZMod 4467511)^90 ≠ 1
          reduce_mod_char
          decide

theorem prime_4494551 : Nat.Prime 4494551 := by
  apply lucas_primality 4494551 (17 : ZMod 4494551)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4494551 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((89891 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 4494551)^2247275 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (17 : ZMod 4494551)^898910 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 89891 := Nat.prime_eq_prime_of_dvd_pow hq prime_89891 hd
        subst q
        change (17 : ZMod 4494551)^50 ≠ 1
        reduce_mod_char
        decide

theorem prime_4516207 : Nat.Prime 4516207 := by
  apply lucas_primality 4516207 (3 : ZMod 4516207)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4516207 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((752701 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4516207)^2258103 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 4516207)^1505402 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 752701 := Nat.prime_eq_prime_of_dvd_pow hq prime_752701 hd
        subst q
        change (3 : ZMod 4516207)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_4536619 : Nat.Prime 4536619 := by
  apply lucas_primality 4536619 (10 : ZMod 4536619)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4536619 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((137 : ℕ)^1 * ((5519 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 4536619)^2268309 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 4536619)^1512206 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
          subst q
          change (10 : ZMod 4536619)^33114 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 5519 := Nat.prime_eq_prime_of_dvd_pow hq prime_5519 hd
          subst q
          change (10 : ZMod 4536619)^822 ≠ 1
          reduce_mod_char
          decide

theorem prime_4588271 : Nat.Prime 4588271 := by
  apply lucas_primality 4588271 (7 : ZMod 4588271)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4588271 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((23 : ℕ)^1 * ((19949 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 4588271)^2294135 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 4588271)^917654 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (7 : ZMod 4588271)^199490 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 19949 := Nat.prime_eq_prime_of_dvd_pow hq prime_19949 hd
          subst q
          change (7 : ZMod 4588271)^230 ≠ 1
          reduce_mod_char
          decide

theorem prime_4714417 : Nat.Prime 4714417 := by
  apply lucas_primality 4714417 (5 : ZMod 4714417)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4714417 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((1559 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 4714417)^2357208 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 4714417)^1571472 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 4714417)^673488 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1559 := Nat.prime_eq_prime_of_dvd_pow hq prime_1559 hd
          subst q
          change (5 : ZMod 4714417)^3024 ≠ 1
          reduce_mod_char
          decide

theorem prime_4766213 : Nat.Prime 4766213 := by
  apply lucas_primality 4766213 (2 : ZMod 4766213)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4766213 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((149 : ℕ)^1 * ((727 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4766213)^2383106 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 4766213)^433292 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
          subst q
          change (2 : ZMod 4766213)^31988 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 727 := Nat.prime_eq_prime_of_dvd_pow hq prime_727 hd
          subst q
          change (2 : ZMod 4766213)^6556 ≠ 1
          reduce_mod_char
          decide

theorem prime_4804889 : Nat.Prime 4804889 := by
  apply lucas_primality 4804889 (3 : ZMod 4804889)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4804889 - 1 = (2 : ℕ)^3 * ((11 : ℕ)^1 * ((54601 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4804889)^2402444 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 4804889)^436808 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 54601 := Nat.prime_eq_prime_of_dvd_pow hq prime_54601 hd
        subst q
        change (3 : ZMod 4804889)^88 ≠ 1
        reduce_mod_char
        decide

theorem prime_4822291 : Nat.Prime 4822291 := by
  apply lucas_primality 4822291 (2 : ZMod 4822291)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4822291 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((4871 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4822291)^2411145 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 4822291)^1607430 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 4822291)^964458 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (2 : ZMod 4822291)^438390 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 4871 := Nat.prime_eq_prime_of_dvd_pow hq prime_4871 hd
            subst q
            change (2 : ZMod 4822291)^990 ≠ 1
            reduce_mod_char
            decide

theorem prime_4826813 : Nat.Prime 4826813 := by
  apply lucas_primality 4826813 (2 : ZMod 4826813)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4826813 - 1 = (2 : ℕ)^2 * ((1206703 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4826813)^2413406 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1206703 := Nat.prime_eq_prime_of_dvd_pow hq prime_1206703 hd
      subst q
      change (2 : ZMod 4826813)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_4835179 : Nat.Prime 4835179 := by
  apply lucas_primality 4835179 (10 : ZMod 4835179)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4835179 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((43 : ℕ)^1 * ((6247 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 4835179)^2417589 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 4835179)^1611726 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (10 : ZMod 4835179)^112446 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 6247 := Nat.prime_eq_prime_of_dvd_pow hq prime_6247 hd
          subst q
          change (10 : ZMod 4835179)^774 ≠ 1
          reduce_mod_char
          decide

theorem prime_4837309 : Nat.Prime 4837309 := by
  apply lucas_primality 4837309 (2 : ZMod 4837309)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4837309 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((57587 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4837309)^2418654 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 4837309)^1612436 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 4837309)^691044 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 57587 := Nat.prime_eq_prime_of_dvd_pow hq prime_57587 hd
          subst q
          change (2 : ZMod 4837309)^84 ≠ 1
          reduce_mod_char
          decide

theorem prime_4846441 : Nat.Prime 4846441 := by
  apply lucas_primality 4846441 (11 : ZMod 4846441)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4846441 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((40387 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 4846441)^2423220 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 4846441)^1615480 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 4846441)^969288 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 40387 := Nat.prime_eq_prime_of_dvd_pow hq prime_40387 hd
          subst q
          change (11 : ZMod 4846441)^120 ≠ 1
          reduce_mod_char
          decide

theorem prime_4847573 : Nat.Prime 4847573 := by
  apply lucas_primality 4847573 (2 : ZMod 4847573)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4847573 - 1 = (2 : ℕ)^2 * ((23 : ℕ)^1 * ((52691 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4847573)^2423786 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (2 : ZMod 4847573)^210764 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 52691 := Nat.prime_eq_prime_of_dvd_pow hq prime_52691 hd
        subst q
        change (2 : ZMod 4847573)^92 ≠ 1
        reduce_mod_char
        decide

theorem prime_4853837 : Nat.Prime 4853837 := by
  apply lucas_primality 4853837 (2 : ZMod 4853837)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4853837 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((269 : ℕ)^1 * ((347 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4853837)^2426918 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 4853837)^373372 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
          subst q
          change (2 : ZMod 4853837)^18044 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 347 := Nat.prime_eq_prime_of_dvd_pow hq prime_347 hd
          subst q
          change (2 : ZMod 4853837)^13988 ≠ 1
          reduce_mod_char
          decide

theorem prime_4946393 : Nat.Prime 4946393 := by
  apply lucas_primality 4946393 (3 : ZMod 4946393)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4946393 - 1 = (2 : ℕ)^3 * ((11 : ℕ)^1 * ((56209 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4946393)^2473196 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 4946393)^449672 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 56209 := Nat.prime_eq_prime_of_dvd_pow hq prime_56209 hd
        subst q
        change (3 : ZMod 4946393)^88 ≠ 1
        reduce_mod_char
        decide

theorem prime_4961323 : Nat.Prime 4961323 := by
  apply lucas_primality 4961323 (2 : ZMod 4961323)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4961323 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((101 : ℕ)^1 * ((2729 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4961323)^2480661 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 4961323)^1653774 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
          subst q
          change (2 : ZMod 4961323)^49122 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2729 := Nat.prime_eq_prime_of_dvd_pow hq prime_2729 hd
          subst q
          change (2 : ZMod 4961323)^1818 ≠ 1
          reduce_mod_char
          decide

theorem prime_4976701 : Nat.Prime 4976701 := by
  apply lucas_primality 4976701 (6 : ZMod 4976701)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4976701 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((53 : ℕ)^1 * ((313 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 4976701)^2488350 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 4976701)^1658900 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 4976701)^995340 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
            subst q
            change (6 : ZMod 4976701)^93900 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 313 := Nat.prime_eq_prime_of_dvd_pow hq prime_313 hd
            subst q
            change (6 : ZMod 4976701)^15900 ≠ 1
            reduce_mod_char
            decide

theorem prime_4984037 : Nat.Prime 4984037 := by
  apply lucas_primality 4984037 (2 : ZMod 4984037)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4984037 - 1 = (2 : ℕ)^2 * ((557 : ℕ)^1 * ((2237 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4984037)^2492018 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 557 := Nat.prime_eq_prime_of_dvd_pow hq prime_557 hd
        subst q
        change (2 : ZMod 4984037)^8948 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2237 := Nat.prime_eq_prime_of_dvd_pow hq prime_2237 hd
        subst q
        change (2 : ZMod 4984037)^2228 ≠ 1
        reduce_mod_char
        decide

theorem prime_5050217 : Nat.Prime 5050217 := by
  apply lucas_primality 5050217 (3 : ZMod 5050217)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5050217 - 1 = (2 : ℕ)^3 * ((41 : ℕ)^1 * ((89 : ℕ)^1 * ((173 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 5050217)^2525108 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
        subst q
        change (3 : ZMod 5050217)^123176 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (3 : ZMod 5050217)^56744 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
          subst q
          change (3 : ZMod 5050217)^29192 ≠ 1
          reduce_mod_char
          decide

end LegendreK6.Pratt
