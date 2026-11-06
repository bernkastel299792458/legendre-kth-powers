import LegendreK6.Pratt.Block004

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LegendreK6.Pratt

theorem prime_15629 : Nat.Prime 15629 := by
  apply lucas_primality 15629 (2 : ZMod 15629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15629 - 1 = (2 : ℕ)^2 * ((3907 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 15629)^7814 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3907 := Nat.prime_eq_prime_of_dvd_pow hq prime_3907 hd
      subst q
      change (2 : ZMod 15629)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_15683 : Nat.Prime 15683 := by
  apply lucas_primality 15683 (2 : ZMod 15683)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15683 - 1 = (2 : ℕ)^1 * ((7841 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 15683)^7841 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 7841 := Nat.prime_eq_prime_of_dvd_pow hq prime_7841 hd
      subst q
      change (2 : ZMod 15683)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_15739 : Nat.Prime 15739 := by
  apply lucas_primality 15739 (2 : ZMod 15739)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15739 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((43 : ℕ)^1 * ((61 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 15739)^7869 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 15739)^5246 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (2 : ZMod 15739)^366 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (2 : ZMod 15739)^258 ≠ 1
          reduce_mod_char
          decide

theorem prime_15761 : Nat.Prime 15761 := by
  apply lucas_primality 15761 (3 : ZMod 15761)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15761 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((197 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 15761)^7880 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 15761)^3152 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
        subst q
        change (3 : ZMod 15761)^80 ≠ 1
        reduce_mod_char
        decide

theorem prime_15787 : Nat.Prime 15787 := by
  apply lucas_primality 15787 (2 : ZMod 15787)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15787 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((877 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 15787)^7893 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 15787)^5262 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 877 := Nat.prime_eq_prime_of_dvd_pow hq prime_877 hd
        subst q
        change (2 : ZMod 15787)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_15809 : Nat.Prime 15809 := by
  apply lucas_primality 15809 (3 : ZMod 15809)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15809 - 1 = (2 : ℕ)^6 * ((13 : ℕ)^1 * ((19 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 15809)^7904 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 15809)^1216 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (3 : ZMod 15809)^832 ≠ 1
        reduce_mod_char
        decide

theorem prime_15859 : Nat.Prime 15859 := by
  apply lucas_primality 15859 (2 : ZMod 15859)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15859 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((881 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 15859)^7929 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 15859)^5286 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 881 := Nat.prime_eq_prime_of_dvd_pow hq prime_881 hd
        subst q
        change (2 : ZMod 15859)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_15877 : Nat.Prime 15877 := by
  apply lucas_primality 15877 (5 : ZMod 15877)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15877 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^4 * ((7 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 15877)^7938 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 15877)^5292 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 15877)^2268 ≠ 1
        reduce_mod_char
        decide

theorem prime_15923 : Nat.Prime 15923 := by
  apply lucas_primality 15923 (2 : ZMod 15923)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15923 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((419 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 15923)^7961 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 15923)^838 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 419 := Nat.prime_eq_prime_of_dvd_pow hq prime_419 hd
        subst q
        change (2 : ZMod 15923)^38 ≠ 1
        reduce_mod_char
        decide

theorem prime_16069 : Nat.Prime 16069 := by
  apply lucas_primality 16069 (2 : ZMod 16069)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16069 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((103 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 16069)^8034 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 16069)^5356 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 16069)^1236 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
          subst q
          change (2 : ZMod 16069)^156 ≠ 1
          reduce_mod_char
          decide

theorem prime_16103 : Nat.Prime 16103 := by
  apply lucas_primality 16103 (5 : ZMod 16103)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16103 - 1 = (2 : ℕ)^1 * ((83 : ℕ)^1 * ((97 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 16103)^8051 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
        subst q
        change (5 : ZMod 16103)^194 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
        subst q
        change (5 : ZMod 16103)^166 ≠ 1
        reduce_mod_char
        decide

theorem prime_16189 : Nat.Prime 16189 := by
  apply lucas_primality 16189 (2 : ZMod 16189)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16189 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((71 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 16189)^8094 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 16189)^5396 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 16189)^852 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
          subst q
          change (2 : ZMod 16189)^228 ≠ 1
          reduce_mod_char
          decide

theorem prime_16223 : Nat.Prime 16223 := by
  apply lucas_primality 16223 (5 : ZMod 16223)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16223 - 1 = (2 : ℕ)^1 * ((8111 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 16223)^8111 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 8111 := Nat.prime_eq_prime_of_dvd_pow hq prime_8111 hd
      subst q
      change (5 : ZMod 16223)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_16231 : Nat.Prime 16231 := by
  apply lucas_primality 16231 (3 : ZMod 16231)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16231 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((541 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 16231)^8115 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 16231)^5410 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 16231)^3246 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 541 := Nat.prime_eq_prime_of_dvd_pow hq prime_541 hd
          subst q
          change (3 : ZMod 16231)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_16253 : Nat.Prime 16253 := by
  apply lucas_primality 16253 (2 : ZMod 16253)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16253 - 1 = (2 : ℕ)^2 * ((17 : ℕ)^1 * ((239 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 16253)^8126 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 16253)^956 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 239 := Nat.prime_eq_prime_of_dvd_pow hq prime_239 hd
        subst q
        change (2 : ZMod 16253)^68 ≠ 1
        reduce_mod_char
        decide

theorem prime_16301 : Nat.Prime 16301 := by
  apply lucas_primality 16301 (2 : ZMod 16301)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16301 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((163 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 16301)^8150 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 16301)^3260 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
        subst q
        change (2 : ZMod 16301)^100 ≠ 1
        reduce_mod_char
        decide

theorem prime_16361 : Nat.Prime 16361 := by
  apply lucas_primality 16361 (3 : ZMod 16361)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16361 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((409 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 16361)^8180 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 16361)^3272 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 409 := Nat.prime_eq_prime_of_dvd_pow hq prime_409 hd
        subst q
        change (3 : ZMod 16361)^40 ≠ 1
        reduce_mod_char
        decide

theorem prime_16363 : Nat.Prime 16363 := by
  apply lucas_primality 16363 (2 : ZMod 16363)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16363 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((101 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 16363)^8181 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 16363)^5454 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
        subst q
        change (2 : ZMod 16363)^162 ≠ 1
        reduce_mod_char
        decide

theorem prime_16417 : Nat.Prime 16417 := by
  apply lucas_primality 16417 (10 : ZMod 16417)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16417 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^3 * ((19 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 16417)^8208 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 16417)^5472 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (10 : ZMod 16417)^864 ≠ 1
        reduce_mod_char
        decide

theorem prime_16493 : Nat.Prime 16493 := by
  apply lucas_primality 16493 (2 : ZMod 16493)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16493 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((19 : ℕ)^1 * ((31 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 16493)^8246 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 16493)^2356 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 16493)^868 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (2 : ZMod 16493)^532 ≠ 1
          reduce_mod_char
          decide

theorem prime_16529 : Nat.Prime 16529 := by
  apply lucas_primality 16529 (3 : ZMod 16529)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16529 - 1 = (2 : ℕ)^4 * ((1033 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 16529)^8264 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1033 := Nat.prime_eq_prime_of_dvd_pow hq prime_1033 hd
      subst q
      change (3 : ZMod 16529)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_16561 : Nat.Prime 16561 := by
  apply lucas_primality 16561 (7 : ZMod 16561)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16561 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((23 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 16561)^8280 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 16561)^5520 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 16561)^3312 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (7 : ZMod 16561)^720 ≠ 1
          reduce_mod_char
          decide

theorem prime_16567 : Nat.Prime 16567 := by
  apply lucas_primality 16567 (3 : ZMod 16567)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16567 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((251 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 16567)^8283 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 16567)^5522 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 16567)^1506 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 251 := Nat.prime_eq_prime_of_dvd_pow hq prime_251 hd
          subst q
          change (3 : ZMod 16567)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_16649 : Nat.Prime 16649 := by
  apply lucas_primality 16649 (3 : ZMod 16649)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16649 - 1 = (2 : ℕ)^3 * ((2081 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 16649)^8324 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 2081 := Nat.prime_eq_prime_of_dvd_pow hq prime_2081 hd
      subst q
      change (3 : ZMod 16649)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_16657 : Nat.Prime 16657 := by
  apply lucas_primality 16657 (5 : ZMod 16657)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16657 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((347 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 16657)^8328 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 16657)^5552 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 347 := Nat.prime_eq_prime_of_dvd_pow hq prime_347 hd
        subst q
        change (5 : ZMod 16657)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_16729 : Nat.Prime 16729 := by
  apply lucas_primality 16729 (13 : ZMod 16729)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16729 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((41 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 16729)^8364 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 16729)^5576 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (13 : ZMod 16729)^984 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (13 : ZMod 16729)^408 ≠ 1
          reduce_mod_char
          decide

theorem prime_16747 : Nat.Prime 16747 := by
  apply lucas_primality 16747 (2 : ZMod 16747)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16747 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((2791 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 16747)^8373 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 16747)^5582 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2791 := Nat.prime_eq_prime_of_dvd_pow hq prime_2791 hd
        subst q
        change (2 : ZMod 16747)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_16811 : Nat.Prime 16811 := by
  apply lucas_primality 16811 (7 : ZMod 16811)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16811 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((41 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 16811)^8405 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 16811)^3362 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
        subst q
        change (7 : ZMod 16811)^410 ≠ 1
        reduce_mod_char
        decide

theorem prime_16921 : Nat.Prime 16921 := by
  apply lucas_primality 16921 (17 : ZMod 16921)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16921 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((47 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 16921)^8460 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 16921)^5640 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (17 : ZMod 16921)^3384 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (17 : ZMod 16921)^360 ≠ 1
          reduce_mod_char
          decide

theorem prime_17029 : Nat.Prime 17029 := by
  apply lucas_primality 17029 (10 : ZMod 17029)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17029 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((43 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 17029)^8514 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 17029)^5676 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (10 : ZMod 17029)^1548 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (10 : ZMod 17029)^396 ≠ 1
          reduce_mod_char
          decide

theorem prime_17033 : Nat.Prime 17033 := by
  apply lucas_primality 17033 (3 : ZMod 17033)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17033 - 1 = (2 : ℕ)^3 * ((2129 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 17033)^8516 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 2129 := Nat.prime_eq_prime_of_dvd_pow hq prime_2129 hd
      subst q
      change (3 : ZMod 17033)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_17107 : Nat.Prime 17107 := by
  apply lucas_primality 17107 (3 : ZMod 17107)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17107 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((2851 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 17107)^8553 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 17107)^5702 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2851 := Nat.prime_eq_prime_of_dvd_pow hq prime_2851 hd
        subst q
        change (3 : ZMod 17107)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_17123 : Nat.Prime 17123 := by
  apply lucas_primality 17123 (2 : ZMod 17123)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17123 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((1223 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 17123)^8561 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 17123)^2446 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1223 := Nat.prime_eq_prime_of_dvd_pow hq prime_1223 hd
        subst q
        change (2 : ZMod 17123)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_17137 : Nat.Prime 17137 := by
  apply lucas_primality 17137 (5 : ZMod 17137)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17137 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((17 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 17137)^8568 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 17137)^5712 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 17137)^2448 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (5 : ZMod 17137)^1008 ≠ 1
          reduce_mod_char
          decide

theorem prime_17159 : Nat.Prime 17159 := by
  apply lucas_primality 17159 (7 : ZMod 17159)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17159 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((373 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 17159)^8579 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (7 : ZMod 17159)^746 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 373 := Nat.prime_eq_prime_of_dvd_pow hq prime_373 hd
        subst q
        change (7 : ZMod 17159)^46 ≠ 1
        reduce_mod_char
        decide

theorem prime_17293 : Nat.Prime 17293 := by
  apply lucas_primality 17293 (7 : ZMod 17293)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17293 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((131 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 17293)^8646 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 17293)^5764 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (7 : ZMod 17293)^1572 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
          subst q
          change (7 : ZMod 17293)^132 ≠ 1
          reduce_mod_char
          decide

theorem prime_17317 : Nat.Prime 17317 := by
  apply lucas_primality 17317 (2 : ZMod 17317)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17317 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((13 : ℕ)^1 * ((37 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 17317)^8658 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 17317)^5772 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 17317)^1332 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (2 : ZMod 17317)^468 ≠ 1
          reduce_mod_char
          decide

theorem prime_17351 : Nat.Prime 17351 := by
  apply lucas_primality 17351 (11 : ZMod 17351)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17351 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((347 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 17351)^8675 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 17351)^3470 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 347 := Nat.prime_eq_prime_of_dvd_pow hq prime_347 hd
        subst q
        change (11 : ZMod 17351)^50 ≠ 1
        reduce_mod_char
        decide

theorem prime_17389 : Nat.Prime 17389 := by
  apply lucas_primality 17389 (2 : ZMod 17389)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17389 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((23 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 17389)^8694 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 17389)^5796 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 17389)^2484 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 17389)^756 ≠ 1
          reduce_mod_char
          decide

theorem prime_17443 : Nat.Prime 17443 := by
  apply lucas_primality 17443 (2 : ZMod 17443)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17443 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((17 : ℕ)^1 * ((19 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 17443)^8721 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 17443)^5814 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 17443)^1026 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 17443)^918 ≠ 1
          reduce_mod_char
          decide

theorem prime_17471 : Nat.Prime 17471 := by
  apply lucas_primality 17471 (11 : ZMod 17471)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17471 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((1747 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 17471)^8735 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 17471)^3494 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1747 := Nat.prime_eq_prime_of_dvd_pow hq prime_1747 hd
        subst q
        change (11 : ZMod 17471)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_17477 : Nat.Prime 17477 := by
  apply lucas_primality 17477 (2 : ZMod 17477)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17477 - 1 = (2 : ℕ)^2 * ((17 : ℕ)^1 * ((257 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 17477)^8738 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 17477)^1028 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 257 := Nat.prime_eq_prime_of_dvd_pow hq prime_257 hd
        subst q
        change (2 : ZMod 17477)^68 ≠ 1
        reduce_mod_char
        decide

theorem prime_17483 : Nat.Prime 17483 := by
  apply lucas_primality 17483 (2 : ZMod 17483)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17483 - 1 = (2 : ℕ)^1 * ((8741 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 17483)^8741 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 8741 := Nat.prime_eq_prime_of_dvd_pow hq prime_8741 hd
      subst q
      change (2 : ZMod 17483)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_17519 : Nat.Prime 17519 := by
  apply lucas_primality 17519 (13 : ZMod 17519)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17519 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((461 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 17519)^8759 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (13 : ZMod 17519)^922 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 461 := Nat.prime_eq_prime_of_dvd_pow hq prime_461 hd
        subst q
        change (13 : ZMod 17519)^38 ≠ 1
        reduce_mod_char
        decide

theorem prime_17569 : Nat.Prime 17569 := by
  apply lucas_primality 17569 (11 : ZMod 17569)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17569 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^2 * ((61 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 17569)^8784 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 17569)^5856 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
        subst q
        change (11 : ZMod 17569)^288 ≠ 1
        reduce_mod_char
        decide

theorem prime_17783 : Nat.Prime 17783 := by
  apply lucas_primality 17783 (5 : ZMod 17783)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17783 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((523 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 17783)^8891 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (5 : ZMod 17783)^1046 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 523 := Nat.prime_eq_prime_of_dvd_pow hq prime_523 hd
        subst q
        change (5 : ZMod 17783)^34 ≠ 1
        reduce_mod_char
        decide

theorem prime_17881 : Nat.Prime 17881 := by
  apply lucas_primality 17881 (7 : ZMod 17881)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17881 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((149 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 17881)^8940 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 17881)^5960 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 17881)^3576 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
          subst q
          change (7 : ZMod 17881)^120 ≠ 1
          reduce_mod_char
          decide

theorem prime_17923 : Nat.Prime 17923 := by
  apply lucas_primality 17923 (2 : ZMod 17923)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17923 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((29 : ℕ)^1 * ((103 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 17923)^8961 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 17923)^5974 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (2 : ZMod 17923)^618 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
          subst q
          change (2 : ZMod 17923)^174 ≠ 1
          reduce_mod_char
          decide

theorem prime_17929 : Nat.Prime 17929 := by
  apply lucas_primality 17929 (11 : ZMod 17929)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17929 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((83 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 17929)^8964 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 17929)^5976 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
        subst q
        change (11 : ZMod 17929)^216 ≠ 1
        reduce_mod_char
        decide

theorem prime_17971 : Nat.Prime 17971 := by
  apply lucas_primality 17971 (3 : ZMod 17971)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17971 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((599 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 17971)^8985 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 17971)^5990 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 17971)^3594 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 599 := Nat.prime_eq_prime_of_dvd_pow hq prime_599 hd
          subst q
          change (3 : ZMod 17971)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_17987 : Nat.Prime 17987 := by
  apply lucas_primality 17987 (5 : ZMod 17987)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17987 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((23 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 17987)^8993 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (5 : ZMod 17987)^1058 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (5 : ZMod 17987)^782 ≠ 1
        reduce_mod_char
        decide

theorem prime_18013 : Nat.Prime 18013 := by
  apply lucas_primality 18013 (2 : ZMod 18013)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18013 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((79 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 18013)^9006 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 18013)^6004 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 18013)^948 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (2 : ZMod 18013)^228 ≠ 1
          reduce_mod_char
          decide

theorem prime_18119 : Nat.Prime 18119 := by
  apply lucas_primality 18119 (17 : ZMod 18119)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18119 - 1 = (2 : ℕ)^1 * ((9059 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 18119)^9059 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 9059 := Nat.prime_eq_prime_of_dvd_pow hq prime_9059 hd
      subst q
      change (17 : ZMod 18119)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_18133 : Nat.Prime 18133 := by
  apply lucas_primality 18133 (5 : ZMod 18133)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18133 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((1511 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 18133)^9066 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 18133)^6044 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1511 := Nat.prime_eq_prime_of_dvd_pow hq prime_1511 hd
        subst q
        change (5 : ZMod 18133)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_18199 : Nat.Prime 18199 := by
  apply lucas_primality 18199 (11 : ZMod 18199)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18199 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((337 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 18199)^9099 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 18199)^6066 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 337 := Nat.prime_eq_prime_of_dvd_pow hq prime_337 hd
        subst q
        change (11 : ZMod 18199)^54 ≠ 1
        reduce_mod_char
        decide

theorem prime_18253 : Nat.Prime 18253 := by
  apply lucas_primality 18253 (5 : ZMod 18253)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18253 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((13 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 18253)^9126 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 18253)^6084 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (5 : ZMod 18253)^1404 ≠ 1
        reduce_mod_char
        decide

theorem prime_18269 : Nat.Prime 18269 := by
  apply lucas_primality 18269 (2 : ZMod 18269)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18269 - 1 = (2 : ℕ)^2 * ((4567 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 18269)^9134 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 4567 := Nat.prime_eq_prime_of_dvd_pow hq prime_4567 hd
      subst q
      change (2 : ZMod 18269)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_18307 : Nat.Prime 18307 := by
  apply lucas_primality 18307 (11 : ZMod 18307)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18307 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((113 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 18307)^9153 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 18307)^6102 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
        subst q
        change (11 : ZMod 18307)^162 ≠ 1
        reduce_mod_char
        decide

theorem prime_18371 : Nat.Prime 18371 := by
  apply lucas_primality 18371 (11 : ZMod 18371)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18371 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((167 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 18371)^9185 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 18371)^3674 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (11 : ZMod 18371)^1670 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
          subst q
          change (11 : ZMod 18371)^110 ≠ 1
          reduce_mod_char
          decide

theorem prime_18379 : Nat.Prime 18379 := by
  apply lucas_primality 18379 (3 : ZMod 18379)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18379 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((1021 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 18379)^9189 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 18379)^6126 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1021 := Nat.prime_eq_prime_of_dvd_pow hq prime_1021 hd
        subst q
        change (3 : ZMod 18379)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_18397 : Nat.Prime 18397 := by
  apply lucas_primality 18397 (6 : ZMod 18397)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18397 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((73 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 18397)^9198 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 18397)^6132 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 18397)^2628 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
          subst q
          change (6 : ZMod 18397)^252 ≠ 1
          reduce_mod_char
          decide

theorem prime_18401 : Nat.Prime 18401 := by
  apply lucas_primality 18401 (3 : ZMod 18401)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18401 - 1 = (2 : ℕ)^5 * ((5 : ℕ)^2 * ((23 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 18401)^9200 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 18401)^3680 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (3 : ZMod 18401)^800 ≠ 1
        reduce_mod_char
        decide

theorem prime_18427 : Nat.Prime 18427 := by
  apply lucas_primality 18427 (2 : ZMod 18427)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18427 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((37 : ℕ)^1 * ((83 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 18427)^9213 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 18427)^6142 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (2 : ZMod 18427)^498 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
          subst q
          change (2 : ZMod 18427)^222 ≠ 1
          reduce_mod_char
          decide

theorem prime_18433 : Nat.Prime 18433 := by
  apply lucas_primality 18433 (5 : ZMod 18433)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18433 - 1 = (2 : ℕ)^11 * ((3 : ℕ)^2) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 18433)^9216 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
      subst q
      change (5 : ZMod 18433)^6144 ≠ 1
      reduce_mod_char
      decide

theorem prime_18443 : Nat.Prime 18443 := by
  apply lucas_primality 18443 (2 : ZMod 18443)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18443 - 1 = (2 : ℕ)^1 * ((9221 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 18443)^9221 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 9221 := Nat.prime_eq_prime_of_dvd_pow hq prime_9221 hd
      subst q
      change (2 : ZMod 18443)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_18493 : Nat.Prime 18493 := by
  apply lucas_primality 18493 (2 : ZMod 18493)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18493 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((67 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 18493)^9246 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 18493)^6164 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 18493)^804 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (2 : ZMod 18493)^276 ≠ 1
          reduce_mod_char
          decide

theorem prime_18517 : Nat.Prime 18517 := by
  apply lucas_primality 18517 (6 : ZMod 18517)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18517 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((1543 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 18517)^9258 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 18517)^6172 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1543 := Nat.prime_eq_prime_of_dvd_pow hq prime_1543 hd
        subst q
        change (6 : ZMod 18517)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_18521 : Nat.Prime 18521 := by
  apply lucas_primality 18521 (3 : ZMod 18521)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18521 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((463 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 18521)^9260 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 18521)^3704 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 463 := Nat.prime_eq_prime_of_dvd_pow hq prime_463 hd
        subst q
        change (3 : ZMod 18521)^40 ≠ 1
        reduce_mod_char
        decide

theorem prime_18523 : Nat.Prime 18523 := by
  apply lucas_primality 18523 (3 : ZMod 18523)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18523 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((7 : ℕ)^3)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 18523)^9261 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 18523)^6174 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 18523)^2646 ≠ 1
        reduce_mod_char
        decide

theorem prime_18679 : Nat.Prime 18679 := by
  apply lucas_primality 18679 (6 : ZMod 18679)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18679 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((283 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 18679)^9339 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 18679)^6226 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (6 : ZMod 18679)^1698 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 283 := Nat.prime_eq_prime_of_dvd_pow hq prime_283 hd
          subst q
          change (6 : ZMod 18679)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_18757 : Nat.Prime 18757 := by
  apply lucas_primality 18757 (2 : ZMod 18757)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18757 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((521 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 18757)^9378 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 18757)^6252 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 521 := Nat.prime_eq_prime_of_dvd_pow hq prime_521 hd
        subst q
        change (2 : ZMod 18757)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_18787 : Nat.Prime 18787 := by
  apply lucas_primality 18787 (2 : ZMod 18787)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18787 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((31 : ℕ)^1 * ((101 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 18787)^9393 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 18787)^6262 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (2 : ZMod 18787)^606 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
          subst q
          change (2 : ZMod 18787)^186 ≠ 1
          reduce_mod_char
          decide

theorem prime_18911 : Nat.Prime 18911 := by
  apply lucas_primality 18911 (14 : ZMod 18911)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18911 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((31 : ℕ)^1 * ((61 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 18911)^9455 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (14 : ZMod 18911)^3782 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (14 : ZMod 18911)^610 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (14 : ZMod 18911)^310 ≠ 1
          reduce_mod_char
          decide

theorem prime_18973 : Nat.Prime 18973 := by
  apply lucas_primality 18973 (2 : ZMod 18973)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18973 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((17 : ℕ)^1 * ((31 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 18973)^9486 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 18973)^6324 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 18973)^1116 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (2 : ZMod 18973)^612 ≠ 1
          reduce_mod_char
          decide

theorem prime_19013 : Nat.Prime 19013 := by
  apply lucas_primality 19013 (2 : ZMod 19013)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19013 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^2 * ((97 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 19013)^9506 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 19013)^2716 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
        subst q
        change (2 : ZMod 19013)^196 ≠ 1
        reduce_mod_char
        decide

theorem prime_19079 : Nat.Prime 19079 := by
  apply lucas_primality 19079 (7 : ZMod 19079)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19079 - 1 = (2 : ℕ)^1 * ((9539 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 19079)^9539 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 9539 := Nat.prime_eq_prime_of_dvd_pow hq prime_9539 hd
      subst q
      change (7 : ZMod 19079)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_19141 : Nat.Prime 19141 := by
  apply lucas_primality 19141 (2 : ZMod 19141)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19141 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((29 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 19141)^9570 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 19141)^6380 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 19141)^3828 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (2 : ZMod 19141)^1740 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (2 : ZMod 19141)^660 ≠ 1
            reduce_mod_char
            decide

theorem prime_19163 : Nat.Prime 19163 := by
  apply lucas_primality 19163 (2 : ZMod 19163)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19163 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((67 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 19163)^9581 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 19163)^1742 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 19163)^1474 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (2 : ZMod 19163)^286 ≠ 1
          reduce_mod_char
          decide

theorem prime_19183 : Nat.Prime 19183 := by
  apply lucas_primality 19183 (3 : ZMod 19183)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19183 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((139 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 19183)^9591 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 19183)^6394 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (3 : ZMod 19183)^834 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
          subst q
          change (3 : ZMod 19183)^138 ≠ 1
          reduce_mod_char
          decide

theorem prime_19237 : Nat.Prime 19237 := by
  apply lucas_primality 19237 (2 : ZMod 19237)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19237 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((229 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 19237)^9618 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 19237)^6412 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 19237)^2748 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 229 := Nat.prime_eq_prime_of_dvd_pow hq prime_229 hd
          subst q
          change (2 : ZMod 19237)^84 ≠ 1
          reduce_mod_char
          decide

theorem prime_19267 : Nat.Prime 19267 := by
  apply lucas_primality 19267 (3 : ZMod 19267)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19267 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^2 * ((19 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 19267)^9633 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 19267)^6422 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 19267)^1482 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (3 : ZMod 19267)^1014 ≠ 1
          reduce_mod_char
          decide

theorem prime_19333 : Nat.Prime 19333 := by
  apply lucas_primality 19333 (2 : ZMod 19333)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19333 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((179 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 19333)^9666 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 19333)^6444 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 179 := Nat.prime_eq_prime_of_dvd_pow hq prime_179 hd
        subst q
        change (2 : ZMod 19333)^108 ≠ 1
        reduce_mod_char
        decide

theorem prime_19373 : Nat.Prime 19373 := by
  apply lucas_primality 19373 (2 : ZMod 19373)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19373 - 1 = (2 : ℕ)^2 * ((29 : ℕ)^1 * ((167 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 19373)^9686 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (2 : ZMod 19373)^668 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
        subst q
        change (2 : ZMod 19373)^116 ≠ 1
        reduce_mod_char
        decide

theorem prime_19403 : Nat.Prime 19403 := by
  apply lucas_primality 19403 (2 : ZMod 19403)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19403 - 1 = (2 : ℕ)^1 * ((89 : ℕ)^1 * ((109 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 19403)^9701 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
        subst q
        change (2 : ZMod 19403)^218 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
        subst q
        change (2 : ZMod 19403)^178 ≠ 1
        reduce_mod_char
        decide

theorem prime_19429 : Nat.Prime 19429 := by
  apply lucas_primality 19429 (6 : ZMod 19429)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19429 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((1619 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 19429)^9714 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 19429)^6476 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1619 := Nat.prime_eq_prime_of_dvd_pow hq prime_1619 hd
        subst q
        change (6 : ZMod 19429)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_19441 : Nat.Prime 19441 := by
  apply lucas_primality 19441 (13 : ZMod 19441)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19441 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^5 * ((5 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 19441)^9720 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 19441)^6480 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (13 : ZMod 19441)^3888 ≠ 1
        reduce_mod_char
        decide

theorem prime_19463 : Nat.Prime 19463 := by
  apply lucas_primality 19463 (5 : ZMod 19463)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19463 - 1 = (2 : ℕ)^1 * ((37 : ℕ)^1 * ((263 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 19463)^9731 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (5 : ZMod 19463)^526 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 263 := Nat.prime_eq_prime_of_dvd_pow hq prime_263 hd
        subst q
        change (5 : ZMod 19463)^74 ≠ 1
        reduce_mod_char
        decide

theorem prime_19489 : Nat.Prime 19489 := by
  apply lucas_primality 19489 (19 : ZMod 19489)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19489 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((29 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 19489)^9744 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 19489)^6496 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (19 : ZMod 19489)^2784 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (19 : ZMod 19489)^672 ≠ 1
          reduce_mod_char
          decide

theorem prime_19531 : Nat.Prime 19531 := by
  apply lucas_primality 19531 (13 : ZMod 19531)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19531 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((31 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 19531)^9765 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 19531)^6510 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 19531)^3906 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (13 : ZMod 19531)^2790 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (13 : ZMod 19531)^630 ≠ 1
            reduce_mod_char
            decide

theorem prime_19553 : Nat.Prime 19553 := by
  apply lucas_primality 19553 (3 : ZMod 19553)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19553 - 1 = (2 : ℕ)^5 * ((13 : ℕ)^1 * ((47 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 19553)^9776 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 19553)^1504 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (3 : ZMod 19553)^416 ≠ 1
        reduce_mod_char
        decide

theorem prime_19709 : Nat.Prime 19709 := by
  apply lucas_primality 19709 (2 : ZMod 19709)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19709 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((379 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 19709)^9854 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 19709)^1516 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 379 := Nat.prime_eq_prime_of_dvd_pow hq prime_379 hd
        subst q
        change (2 : ZMod 19709)^52 ≠ 1
        reduce_mod_char
        decide

theorem prime_19759 : Nat.Prime 19759 := by
  apply lucas_primality 19759 (3 : ZMod 19759)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19759 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((37 : ℕ)^1 * ((89 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 19759)^9879 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 19759)^6586 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (3 : ZMod 19759)^534 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (3 : ZMod 19759)^222 ≠ 1
          reduce_mod_char
          decide

theorem prime_19763 : Nat.Prime 19763 := by
  apply lucas_primality 19763 (2 : ZMod 19763)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19763 - 1 = (2 : ℕ)^1 * ((41 : ℕ)^1 * ((241 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 19763)^9881 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
        subst q
        change (2 : ZMod 19763)^482 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 241 := Nat.prime_eq_prime_of_dvd_pow hq prime_241 hd
        subst q
        change (2 : ZMod 19763)^82 ≠ 1
        reduce_mod_char
        decide

theorem prime_19801 : Nat.Prime 19801 := by
  apply lucas_primality 19801 (13 : ZMod 19801)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19801 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((5 : ℕ)^2 * ((11 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 19801)^9900 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 19801)^6600 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 19801)^3960 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (13 : ZMod 19801)^1800 ≠ 1
          reduce_mod_char
          decide

theorem prime_19813 : Nat.Prime 19813 := by
  apply lucas_primality 19813 (2 : ZMod 19813)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19813 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((127 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 19813)^9906 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 19813)^6604 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 19813)^1524 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
          subst q
          change (2 : ZMod 19813)^156 ≠ 1
          reduce_mod_char
          decide

theorem prime_19819 : Nat.Prime 19819 := by
  apply lucas_primality 19819 (3 : ZMod 19819)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19819 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((367 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 19819)^9909 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 19819)^6606 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 367 := Nat.prime_eq_prime_of_dvd_pow hq prime_367 hd
        subst q
        change (3 : ZMod 19819)^54 ≠ 1
        reduce_mod_char
        decide

theorem prime_19841 : Nat.Prime 19841 := by
  apply lucas_primality 19841 (3 : ZMod 19841)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19841 - 1 = (2 : ℕ)^7 * ((5 : ℕ)^1 * ((31 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 19841)^9920 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 19841)^3968 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (3 : ZMod 19841)^640 ≠ 1
        reduce_mod_char
        decide

theorem prime_19843 : Nat.Prime 19843 := by
  apply lucas_primality 19843 (19 : ZMod 19843)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19843 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((3307 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 19843)^9921 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 19843)^6614 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3307 := Nat.prime_eq_prime_of_dvd_pow hq prime_3307 hd
        subst q
        change (19 : ZMod 19843)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_19867 : Nat.Prime 19867 := by
  apply lucas_primality 19867 (2 : ZMod 19867)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19867 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((43 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 19867)^9933 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 19867)^6622 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 19867)^2838 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (2 : ZMod 19867)^1806 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (2 : ZMod 19867)^462 ≠ 1
            reduce_mod_char
            decide

theorem prime_19889 : Nat.Prime 19889 := by
  apply lucas_primality 19889 (3 : ZMod 19889)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19889 - 1 = (2 : ℕ)^4 * ((11 : ℕ)^1 * ((113 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 19889)^9944 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 19889)^1808 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
        subst q
        change (3 : ZMod 19889)^176 ≠ 1
        reduce_mod_char
        decide

theorem prime_19949 : Nat.Prime 19949 := by
  apply lucas_primality 19949 (2 : ZMod 19949)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19949 - 1 = (2 : ℕ)^2 * ((4987 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 19949)^9974 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 4987 := Nat.prime_eq_prime_of_dvd_pow hq prime_4987 hd
      subst q
      change (2 : ZMod 19949)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_19961 : Nat.Prime 19961 := by
  apply lucas_primality 19961 (6 : ZMod 19961)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19961 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((499 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 19961)^9980 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 19961)^3992 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 499 := Nat.prime_eq_prime_of_dvd_pow hq prime_499 hd
        subst q
        change (6 : ZMod 19961)^40 ≠ 1
        reduce_mod_char
        decide

theorem prime_20023 : Nat.Prime 20023 := by
  apply lucas_primality 20023 (3 : ZMod 20023)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20023 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((47 : ℕ)^1 * ((71 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 20023)^10011 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 20023)^6674 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (3 : ZMod 20023)^426 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
          subst q
          change (3 : ZMod 20023)^282 ≠ 1
          reduce_mod_char
          decide

theorem prime_20063 : Nat.Prime 20063 := by
  apply lucas_primality 20063 (5 : ZMod 20063)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20063 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((1433 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 20063)^10031 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 20063)^2866 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1433 := Nat.prime_eq_prime_of_dvd_pow hq prime_1433 hd
        subst q
        change (5 : ZMod 20063)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_20101 : Nat.Prime 20101 := by
  apply lucas_primality 20101 (6 : ZMod 20101)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20101 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((67 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 20101)^10050 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 20101)^6700 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 20101)^4020 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (6 : ZMod 20101)^300 ≠ 1
          reduce_mod_char
          decide

theorem prime_20143 : Nat.Prime 20143 := by
  apply lucas_primality 20143 (5 : ZMod 20143)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20143 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((373 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 20143)^10071 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 20143)^6714 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 373 := Nat.prime_eq_prime_of_dvd_pow hq prime_373 hd
        subst q
        change (5 : ZMod 20143)^54 ≠ 1
        reduce_mod_char
        decide

theorem prime_20147 : Nat.Prime 20147 := by
  apply lucas_primality 20147 (6 : ZMod 20147)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20147 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((1439 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 20147)^10073 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (6 : ZMod 20147)^2878 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1439 := Nat.prime_eq_prime_of_dvd_pow hq prime_1439 hd
        subst q
        change (6 : ZMod 20147)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_20249 : Nat.Prime 20249 := by
  apply lucas_primality 20249 (3 : ZMod 20249)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20249 - 1 = (2 : ℕ)^3 * ((2531 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 20249)^10124 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 2531 := Nat.prime_eq_prime_of_dvd_pow hq prime_2531 hd
      subst q
      change (3 : ZMod 20249)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_20269 : Nat.Prime 20269 := by
  apply lucas_primality 20269 (2 : ZMod 20269)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20269 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((563 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 20269)^10134 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 20269)^6756 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 563 := Nat.prime_eq_prime_of_dvd_pow hq prime_563 hd
        subst q
        change (2 : ZMod 20269)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_20323 : Nat.Prime 20323 := by
  apply lucas_primality 20323 (2 : ZMod 20323)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20323 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((1129 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 20323)^10161 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 20323)^6774 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1129 := Nat.prime_eq_prime_of_dvd_pow hq prime_1129 hd
        subst q
        change (2 : ZMod 20323)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_20353 : Nat.Prime 20353 := by
  apply lucas_primality 20353 (5 : ZMod 20353)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20353 - 1 = (2 : ℕ)^7 * ((3 : ℕ)^1 * ((53 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 20353)^10176 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 20353)^6784 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
        subst q
        change (5 : ZMod 20353)^384 ≠ 1
        reduce_mod_char
        decide

theorem prime_20477 : Nat.Prime 20477 := by
  apply lucas_primality 20477 (2 : ZMod 20477)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20477 - 1 = (2 : ℕ)^2 * ((5119 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 20477)^10238 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 5119 := Nat.prime_eq_prime_of_dvd_pow hq prime_5119 hd
      subst q
      change (2 : ZMod 20477)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_20479 : Nat.Prime 20479 := by
  apply lucas_primality 20479 (3 : ZMod 20479)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20479 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((3413 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 20479)^10239 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 20479)^6826 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3413 := Nat.prime_eq_prime_of_dvd_pow hq prime_3413 hd
        subst q
        change (3 : ZMod 20479)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_20483 : Nat.Prime 20483 := by
  apply lucas_primality 20483 (5 : ZMod 20483)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20483 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^2 * ((11 : ℕ)^1 * ((19 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 20483)^10241 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 20483)^2926 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 20483)^1862 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (5 : ZMod 20483)^1078 ≠ 1
          reduce_mod_char
          decide

theorem prime_20521 : Nat.Prime 20521 := by
  apply lucas_primality 20521 (11 : ZMod 20521)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20521 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((19 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 20521)^10260 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 20521)^6840 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 20521)^4104 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (11 : ZMod 20521)^1080 ≠ 1
          reduce_mod_char
          decide

theorem prime_20641 : Nat.Prime 20641 := by
  apply lucas_primality 20641 (7 : ZMod 20641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20641 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((43 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 20641)^10320 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 20641)^6880 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 20641)^4128 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (7 : ZMod 20641)^480 ≠ 1
          reduce_mod_char
          decide

theorem prime_20731 : Nat.Prime 20731 := by
  apply lucas_primality 20731 (2 : ZMod 20731)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20731 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((691 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 20731)^10365 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 20731)^6910 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 20731)^4146 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 691 := Nat.prime_eq_prime_of_dvd_pow hq prime_691 hd
          subst q
          change (2 : ZMod 20731)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_20759 : Nat.Prime 20759 := by
  apply lucas_primality 20759 (7 : ZMod 20759)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20759 - 1 = (2 : ℕ)^1 * ((97 : ℕ)^1 * ((107 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 20759)^10379 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
        subst q
        change (7 : ZMod 20759)^214 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
        subst q
        change (7 : ZMod 20759)^194 ≠ 1
        reduce_mod_char
        decide

theorem prime_20939 : Nat.Prime 20939 := by
  apply lucas_primality 20939 (2 : ZMod 20939)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20939 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^2 * ((29 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 20939)^10469 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 20939)^1102 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (2 : ZMod 20939)^722 ≠ 1
        reduce_mod_char
        decide

theorem prime_21121 : Nat.Prime 21121 := by
  apply lucas_primality 21121 (19 : ZMod 21121)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21121 - 1 = (2 : ℕ)^7 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 21121)^10560 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 21121)^7040 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (19 : ZMod 21121)^4224 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (19 : ZMod 21121)^1920 ≠ 1
          reduce_mod_char
          decide

theorem prime_21149 : Nat.Prime 21149 := by
  apply lucas_primality 21149 (3 : ZMod 21149)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21149 - 1 = (2 : ℕ)^2 * ((17 : ℕ)^1 * ((311 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 21149)^10574 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (3 : ZMod 21149)^1244 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 311 := Nat.prime_eq_prime_of_dvd_pow hq prime_311 hd
        subst q
        change (3 : ZMod 21149)^68 ≠ 1
        reduce_mod_char
        decide

theorem prime_21157 : Nat.Prime 21157 := by
  apply lucas_primality 21157 (2 : ZMod 21157)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21157 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((41 : ℕ)^1 * ((43 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 21157)^10578 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 21157)^7052 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (2 : ZMod 21157)^516 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (2 : ZMod 21157)^492 ≠ 1
          reduce_mod_char
          decide

theorem prime_21191 : Nat.Prime 21191 := by
  apply lucas_primality 21191 (7 : ZMod 21191)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21191 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((163 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 21191)^10595 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 21191)^4238 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (7 : ZMod 21191)^1630 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
          subst q
          change (7 : ZMod 21191)^130 ≠ 1
          reduce_mod_char
          decide

theorem prime_21277 : Nat.Prime 21277 := by
  apply lucas_primality 21277 (6 : ZMod 21277)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21277 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((197 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 21277)^10638 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 21277)^7092 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
        subst q
        change (6 : ZMod 21277)^108 ≠ 1
        reduce_mod_char
        decide

theorem prime_21283 : Nat.Prime 21283 := by
  apply lucas_primality 21283 (11 : ZMod 21283)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21283 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((3547 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 21283)^10641 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 21283)^7094 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3547 := Nat.prime_eq_prime_of_dvd_pow hq prime_3547 hd
        subst q
        change (11 : ZMod 21283)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_21379 : Nat.Prime 21379 := by
  apply lucas_primality 21379 (2 : ZMod 21379)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21379 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((509 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 21379)^10689 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 21379)^7126 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 21379)^3054 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 509 := Nat.prime_eq_prime_of_dvd_pow hq prime_509 hd
          subst q
          change (2 : ZMod 21379)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_21397 : Nat.Prime 21397 := by
  apply lucas_primality 21397 (2 : ZMod 21397)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21397 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((1783 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 21397)^10698 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 21397)^7132 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1783 := Nat.prime_eq_prime_of_dvd_pow hq prime_1783 hd
        subst q
        change (2 : ZMod 21397)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_21407 : Nat.Prime 21407 := by
  apply lucas_primality 21407 (5 : ZMod 21407)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21407 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((139 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 21407)^10703 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 21407)^3058 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 21407)^1946 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
          subst q
          change (5 : ZMod 21407)^154 ≠ 1
          reduce_mod_char
          decide

theorem prime_21433 : Nat.Prime 21433 := by
  apply lucas_primality 21433 (5 : ZMod 21433)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21433 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((47 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 21433)^10716 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 21433)^7144 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (5 : ZMod 21433)^1128 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (5 : ZMod 21433)^456 ≠ 1
          reduce_mod_char
          decide

theorem prime_21487 : Nat.Prime 21487 := by
  apply lucas_primality 21487 (3 : ZMod 21487)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21487 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((3581 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 21487)^10743 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 21487)^7162 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3581 := Nat.prime_eq_prime_of_dvd_pow hq prime_3581 hd
        subst q
        change (3 : ZMod 21487)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_21523 : Nat.Prime 21523 := by
  apply lucas_primality 21523 (2 : ZMod 21523)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21523 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((211 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 21523)^10761 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 21523)^7174 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 21523)^1266 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 211 := Nat.prime_eq_prime_of_dvd_pow hq prime_211 hd
          subst q
          change (2 : ZMod 21523)^102 ≠ 1
          reduce_mod_char
          decide

theorem prime_21529 : Nat.Prime 21529 := by
  apply lucas_primality 21529 (11 : ZMod 21529)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21529 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((13 : ℕ)^1 * ((23 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 21529)^10764 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 21529)^7176 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (11 : ZMod 21529)^1656 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (11 : ZMod 21529)^936 ≠ 1
          reduce_mod_char
          decide

theorem prime_21563 : Nat.Prime 21563 := by
  apply lucas_primality 21563 (2 : ZMod 21563)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21563 - 1 = (2 : ℕ)^1 * ((10781 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 21563)^10781 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 10781 := Nat.prime_eq_prime_of_dvd_pow hq prime_10781 hd
      subst q
      change (2 : ZMod 21563)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_21599 : Nat.Prime 21599 := by
  apply lucas_primality 21599 (7 : ZMod 21599)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21599 - 1 = (2 : ℕ)^1 * ((10799 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 21599)^10799 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 10799 := Nat.prime_eq_prime_of_dvd_pow hq prime_10799 hd
      subst q
      change (7 : ZMod 21599)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_21649 : Nat.Prime 21649 := by
  apply lucas_primality 21649 (14 : ZMod 21649)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21649 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((41 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 21649)^10824 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 21649)^7216 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (14 : ZMod 21649)^1968 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (14 : ZMod 21649)^528 ≠ 1
          reduce_mod_char
          decide

theorem prime_21859 : Nat.Prime 21859 := by
  apply lucas_primality 21859 (2 : ZMod 21859)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21859 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((3643 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 21859)^10929 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 21859)^7286 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3643 := Nat.prime_eq_prime_of_dvd_pow hq prime_3643 hd
        subst q
        change (2 : ZMod 21859)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_21911 : Nat.Prime 21911 := by
  apply lucas_primality 21911 (13 : ZMod 21911)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21911 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((313 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 21911)^10955 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (13 : ZMod 21911)^4382 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (13 : ZMod 21911)^3130 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 313 := Nat.prime_eq_prime_of_dvd_pow hq prime_313 hd
          subst q
          change (13 : ZMod 21911)^70 ≠ 1
          reduce_mod_char
          decide

theorem prime_21961 : Nat.Prime 21961 := by
  apply lucas_primality 21961 (17 : ZMod 21961)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21961 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((61 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 21961)^10980 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 21961)^7320 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (17 : ZMod 21961)^4392 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (17 : ZMod 21961)^360 ≠ 1
          reduce_mod_char
          decide

theorem prime_22013 : Nat.Prime 22013 := by
  apply lucas_primality 22013 (2 : ZMod 22013)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22013 - 1 = (2 : ℕ)^2 * ((5503 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 22013)^11006 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 5503 := Nat.prime_eq_prime_of_dvd_pow hq prime_5503 hd
      subst q
      change (2 : ZMod 22013)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_22037 : Nat.Prime 22037 := by
  apply lucas_primality 22037 (2 : ZMod 22037)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22037 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((787 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 22037)^11018 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 22037)^3148 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 787 := Nat.prime_eq_prime_of_dvd_pow hq prime_787 hd
        subst q
        change (2 : ZMod 22037)^28 ≠ 1
        reduce_mod_char
        decide

theorem prime_22039 : Nat.Prime 22039 := by
  apply lucas_primality 22039 (6 : ZMod 22039)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22039 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((3673 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 22039)^11019 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 22039)^7346 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3673 := Nat.prime_eq_prime_of_dvd_pow hq prime_3673 hd
        subst q
        change (6 : ZMod 22039)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_22067 : Nat.Prime 22067 := by
  apply lucas_primality 22067 (2 : ZMod 22067)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22067 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((59 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 22067)^11033 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 22067)^2006 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 22067)^1298 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (2 : ZMod 22067)^374 ≠ 1
          reduce_mod_char
          decide

theorem prime_22073 : Nat.Prime 22073 := by
  apply lucas_primality 22073 (3 : ZMod 22073)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22073 - 1 = (2 : ℕ)^3 * ((31 : ℕ)^1 * ((89 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 22073)^11036 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (3 : ZMod 22073)^712 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
        subst q
        change (3 : ZMod 22073)^248 ≠ 1
        reduce_mod_char
        decide

theorem prime_22091 : Nat.Prime 22091 := by
  apply lucas_primality 22091 (2 : ZMod 22091)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22091 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((47 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 22091)^11045 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 22091)^4418 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (2 : ZMod 22091)^470 ≠ 1
        reduce_mod_char
        decide

theorem prime_22093 : Nat.Prime 22093 := by
  apply lucas_primality 22093 (6 : ZMod 22093)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22093 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((263 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 22093)^11046 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 22093)^7364 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 22093)^3156 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 263 := Nat.prime_eq_prime_of_dvd_pow hq prime_263 hd
          subst q
          change (6 : ZMod 22093)^84 ≠ 1
          reduce_mod_char
          decide

theorem prime_22129 : Nat.Prime 22129 := by
  apply lucas_primality 22129 (19 : ZMod 22129)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22129 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((461 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 22129)^11064 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 22129)^7376 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 461 := Nat.prime_eq_prime_of_dvd_pow hq prime_461 hd
        subst q
        change (19 : ZMod 22129)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_22189 : Nat.Prime 22189 := by
  apply lucas_primality 22189 (2 : ZMod 22189)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22189 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((43 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 22189)^11094 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 22189)^7396 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
        subst q
        change (2 : ZMod 22189)^516 ≠ 1
        reduce_mod_char
        decide

theorem prime_22273 : Nat.Prime 22273 := by
  apply lucas_primality 22273 (5 : ZMod 22273)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22273 - 1 = (2 : ℕ)^8 * ((3 : ℕ)^1 * ((29 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 22273)^11136 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 22273)^7424 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (5 : ZMod 22273)^768 ≠ 1
        reduce_mod_char
        decide

theorem prime_22303 : Nat.Prime 22303 := by
  apply lucas_primality 22303 (6 : ZMod 22303)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22303 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((59 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 22303)^11151 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 22303)^7434 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 22303)^3186 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (6 : ZMod 22303)^378 ≠ 1
          reduce_mod_char
          decide

theorem prime_22381 : Nat.Prime 22381 := by
  apply lucas_primality 22381 (10 : ZMod 22381)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22381 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((373 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 22381)^11190 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 22381)^7460 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 22381)^4476 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 373 := Nat.prime_eq_prime_of_dvd_pow hq prime_373 hd
          subst q
          change (10 : ZMod 22381)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_22441 : Nat.Prime 22441 := by
  apply lucas_primality 22441 (14 : ZMod 22441)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22441 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((17 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 22441)^11220 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 22441)^7480 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (14 : ZMod 22441)^4488 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (14 : ZMod 22441)^2040 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (14 : ZMod 22441)^1320 ≠ 1
            reduce_mod_char
            decide

theorem prime_22447 : Nat.Prime 22447 := by
  apply lucas_primality 22447 (3 : ZMod 22447)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22447 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((29 : ℕ)^1 * ((43 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 22447)^11223 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 22447)^7482 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (3 : ZMod 22447)^774 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (3 : ZMod 22447)^522 ≠ 1
          reduce_mod_char
          decide

theorem prime_22543 : Nat.Prime 22543 := by
  apply lucas_primality 22543 (3 : ZMod 22543)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22543 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((17 : ℕ)^2))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 22543)^11271 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 22543)^7514 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 22543)^1734 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (3 : ZMod 22543)^1326 ≠ 1
          reduce_mod_char
          decide

theorem prime_22549 : Nat.Prime 22549 := by
  apply lucas_primality 22549 (2 : ZMod 22549)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22549 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((1879 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 22549)^11274 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 22549)^7516 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1879 := Nat.prime_eq_prime_of_dvd_pow hq prime_1879 hd
        subst q
        change (2 : ZMod 22549)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_22571 : Nat.Prime 22571 := by
  apply lucas_primality 22571 (6 : ZMod 22571)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22571 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((37 : ℕ)^1 * ((61 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 22571)^11285 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 22571)^4514 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (6 : ZMod 22571)^610 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (6 : ZMod 22571)^370 ≠ 1
          reduce_mod_char
          decide

theorem prime_22783 : Nat.Prime 22783 := by
  apply lucas_primality 22783 (3 : ZMod 22783)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22783 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((3797 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 22783)^11391 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 22783)^7594 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3797 := Nat.prime_eq_prime_of_dvd_pow hq prime_3797 hd
        subst q
        change (3 : ZMod 22783)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_22811 : Nat.Prime 22811 := by
  apply lucas_primality 22811 (6 : ZMod 22811)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22811 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((2281 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 22811)^11405 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 22811)^4562 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2281 := Nat.prime_eq_prime_of_dvd_pow hq prime_2281 hd
        subst q
        change (6 : ZMod 22811)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_22937 : Nat.Prime 22937 := by
  apply lucas_primality 22937 (3 : ZMod 22937)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22937 - 1 = (2 : ℕ)^3 * ((47 : ℕ)^1 * ((61 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 22937)^11468 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (3 : ZMod 22937)^488 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
        subst q
        change (3 : ZMod 22937)^376 ≠ 1
        reduce_mod_char
        decide

theorem prime_22943 : Nat.Prime 22943 := by
  apply lucas_primality 22943 (5 : ZMod 22943)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22943 - 1 = (2 : ℕ)^1 * ((11471 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 22943)^11471 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 11471 := Nat.prime_eq_prime_of_dvd_pow hq prime_11471 hd
      subst q
      change (5 : ZMod 22943)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_23039 : Nat.Prime 23039 := by
  apply lucas_primality 23039 (7 : ZMod 23039)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23039 - 1 = (2 : ℕ)^1 * ((11519 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 23039)^11519 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 11519 := Nat.prime_eq_prime_of_dvd_pow hq prime_11519 hd
      subst q
      change (7 : ZMod 23039)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_23081 : Nat.Prime 23081 := by
  apply lucas_primality 23081 (3 : ZMod 23081)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23081 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((577 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 23081)^11540 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 23081)^4616 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 577 := Nat.prime_eq_prime_of_dvd_pow hq prime_577 hd
        subst q
        change (3 : ZMod 23081)^40 ≠ 1
        reduce_mod_char
        decide

theorem prime_23159 : Nat.Prime 23159 := by
  apply lucas_primality 23159 (11 : ZMod 23159)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23159 - 1 = (2 : ℕ)^1 * ((11579 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 23159)^11579 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 11579 := Nat.prime_eq_prime_of_dvd_pow hq prime_11579 hd
      subst q
      change (11 : ZMod 23159)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_23167 : Nat.Prime 23167 := by
  apply lucas_primality 23167 (3 : ZMod 23167)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23167 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((11 : ℕ)^1 * ((13 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 23167)^11583 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 23167)^7722 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 23167)^2106 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 23167)^1782 ≠ 1
          reduce_mod_char
          decide

theorem prime_23189 : Nat.Prime 23189 := by
  apply lucas_primality 23189 (2 : ZMod 23189)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23189 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((31 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 23189)^11594 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 23189)^2108 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 23189)^1364 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (2 : ZMod 23189)^748 ≠ 1
          reduce_mod_char
          decide

theorem prime_23251 : Nat.Prime 23251 := by
  apply lucas_primality 23251 (2 : ZMod 23251)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23251 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^3 * ((31 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 23251)^11625 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 23251)^7750 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 23251)^4650 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (2 : ZMod 23251)^750 ≠ 1
          reduce_mod_char
          decide

theorem prime_23297 : Nat.Prime 23297 := by
  apply lucas_primality 23297 (3 : ZMod 23297)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23297 - 1 = (2 : ℕ)^8 * ((7 : ℕ)^1 * ((13 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 23297)^11648 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 23297)^3328 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 23297)^1792 ≠ 1
        reduce_mod_char
        decide

theorem prime_23311 : Nat.Prime 23311 := by
  apply lucas_primality 23311 (3 : ZMod 23311)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23311 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((37 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 23311)^11655 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 23311)^7770 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 23311)^4662 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (3 : ZMod 23311)^3330 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
            subst q
            change (3 : ZMod 23311)^630 ≠ 1
            reduce_mod_char
            decide

theorem prime_23321 : Nat.Prime 23321 := by
  apply lucas_primality 23321 (3 : ZMod 23321)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23321 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((53 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 23321)^11660 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 23321)^4664 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 23321)^2120 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (3 : ZMod 23321)^440 ≠ 1
          reduce_mod_char
          decide

theorem prime_23327 : Nat.Prime 23327 := by
  apply lucas_primality 23327 (5 : ZMod 23327)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23327 - 1 = (2 : ℕ)^1 * ((107 : ℕ)^1 * ((109 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 23327)^11663 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
        subst q
        change (5 : ZMod 23327)^218 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
        subst q
        change (5 : ZMod 23327)^214 ≠ 1
        reduce_mod_char
        decide

theorem prime_23447 : Nat.Prime 23447 := by
  apply lucas_primality 23447 (5 : ZMod 23447)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23447 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((617 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 23447)^11723 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (5 : ZMod 23447)^1234 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 617 := Nat.prime_eq_prime_of_dvd_pow hq prime_617 hd
        subst q
        change (5 : ZMod 23447)^38 ≠ 1
        reduce_mod_char
        decide

theorem prime_23537 : Nat.Prime 23537 := by
  apply lucas_primality 23537 (3 : ZMod 23537)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23537 - 1 = (2 : ℕ)^4 * ((1471 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 23537)^11768 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1471 := Nat.prime_eq_prime_of_dvd_pow hq prime_1471 hd
      subst q
      change (3 : ZMod 23537)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_23603 : Nat.Prime 23603 := by
  apply lucas_primality 23603 (2 : ZMod 23603)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23603 - 1 = (2 : ℕ)^1 * ((11801 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 23603)^11801 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 11801 := Nat.prime_eq_prime_of_dvd_pow hq prime_11801 hd
      subst q
      change (2 : ZMod 23603)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_23629 : Nat.Prime 23629 := by
  apply lucas_primality 23629 (2 : ZMod 23629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23629 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((179 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 23629)^11814 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 23629)^7876 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 23629)^2148 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 179 := Nat.prime_eq_prime_of_dvd_pow hq prime_179 hd
          subst q
          change (2 : ZMod 23629)^132 ≠ 1
          reduce_mod_char
          decide

theorem prime_23929 : Nat.Prime 23929 := by
  apply lucas_primality 23929 (7 : ZMod 23929)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23929 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((997 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 23929)^11964 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 23929)^7976 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 997 := Nat.prime_eq_prime_of_dvd_pow hq prime_997 hd
        subst q
        change (7 : ZMod 23929)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_23957 : Nat.Prime 23957 := by
  apply lucas_primality 23957 (2 : ZMod 23957)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23957 - 1 = (2 : ℕ)^2 * ((53 : ℕ)^1 * ((113 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 23957)^11978 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
        subst q
        change (2 : ZMod 23957)^452 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
        subst q
        change (2 : ZMod 23957)^212 ≠ 1
        reduce_mod_char
        decide

theorem prime_23981 : Nat.Prime 23981 := by
  apply lucas_primality 23981 (3 : ZMod 23981)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23981 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((109 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 23981)^11990 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 23981)^4796 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 23981)^2180 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
          subst q
          change (3 : ZMod 23981)^220 ≠ 1
          reduce_mod_char
          decide

theorem prime_24001 : Nat.Prime 24001 := by
  apply lucas_primality 24001 (14 : ZMod 24001)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24001 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^1 * ((5 : ℕ)^3)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 24001)^12000 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 24001)^8000 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (14 : ZMod 24001)^4800 ≠ 1
        reduce_mod_char
        decide

theorem prime_24029 : Nat.Prime 24029 := by
  apply lucas_primality 24029 (2 : ZMod 24029)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24029 - 1 = (2 : ℕ)^2 * ((6007 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 24029)^12014 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 6007 := Nat.prime_eq_prime_of_dvd_pow hq prime_6007 hd
      subst q
      change (2 : ZMod 24029)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_24097 : Nat.Prime 24097 := by
  apply lucas_primality 24097 (5 : ZMod 24097)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24097 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((251 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 24097)^12048 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 24097)^8032 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 251 := Nat.prime_eq_prime_of_dvd_pow hq prime_251 hd
        subst q
        change (5 : ZMod 24097)^96 ≠ 1
        reduce_mod_char
        decide

theorem prime_24197 : Nat.Prime 24197 := by
  apply lucas_primality 24197 (2 : ZMod 24197)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24197 - 1 = (2 : ℕ)^2 * ((23 : ℕ)^1 * ((263 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 24197)^12098 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (2 : ZMod 24197)^1052 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 263 := Nat.prime_eq_prime_of_dvd_pow hq prime_263 hd
        subst q
        change (2 : ZMod 24197)^92 ≠ 1
        reduce_mod_char
        decide

theorem prime_24203 : Nat.Prime 24203 := by
  apply lucas_primality 24203 (2 : ZMod 24203)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24203 - 1 = (2 : ℕ)^1 * ((12101 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 24203)^12101 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 12101 := Nat.prime_eq_prime_of_dvd_pow hq prime_12101 hd
      subst q
      change (2 : ZMod 24203)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_24229 : Nat.Prime 24229 := by
  apply lucas_primality 24229 (2 : ZMod 24229)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24229 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((673 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 24229)^12114 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 24229)^8076 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 673 := Nat.prime_eq_prime_of_dvd_pow hq prime_673 hd
        subst q
        change (2 : ZMod 24229)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_24281 : Nat.Prime 24281 := by
  apply lucas_primality 24281 (3 : ZMod 24281)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24281 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((607 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 24281)^12140 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 24281)^4856 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 607 := Nat.prime_eq_prime_of_dvd_pow hq prime_607 hd
        subst q
        change (3 : ZMod 24281)^40 ≠ 1
        reduce_mod_char
        decide

theorem prime_24337 : Nat.Prime 24337 := by
  apply lucas_primality 24337 (5 : ZMod 24337)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24337 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((13 : ℕ)^2)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 24337)^12168 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 24337)^8112 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (5 : ZMod 24337)^1872 ≠ 1
        reduce_mod_char
        decide

theorem prime_24379 : Nat.Prime 24379 := by
  apply lucas_primality 24379 (2 : ZMod 24379)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24379 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((239 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 24379)^12189 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 24379)^8126 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 24379)^1434 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 239 := Nat.prime_eq_prime_of_dvd_pow hq prime_239 hd
          subst q
          change (2 : ZMod 24379)^102 ≠ 1
          reduce_mod_char
          decide

theorem prime_24439 : Nat.Prime 24439 := by
  apply lucas_primality 24439 (6 : ZMod 24439)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24439 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((4073 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 24439)^12219 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 24439)^8146 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4073 := Nat.prime_eq_prime_of_dvd_pow hq prime_4073 hd
        subst q
        change (6 : ZMod 24439)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_24533 : Nat.Prime 24533 := by
  apply lucas_primality 24533 (2 : ZMod 24533)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24533 - 1 = (2 : ℕ)^2 * ((6133 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 24533)^12266 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 6133 := Nat.prime_eq_prime_of_dvd_pow hq prime_6133 hd
      subst q
      change (2 : ZMod 24533)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_24611 : Nat.Prime 24611 := by
  apply lucas_primality 24611 (13 : ZMod 24611)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24611 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((23 : ℕ)^1 * ((107 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 24611)^12305 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (13 : ZMod 24611)^4922 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (13 : ZMod 24611)^1070 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
          subst q
          change (13 : ZMod 24611)^230 ≠ 1
          reduce_mod_char
          decide

theorem prime_24749 : Nat.Prime 24749 := by
  apply lucas_primality 24749 (2 : ZMod 24749)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24749 - 1 = (2 : ℕ)^2 * ((23 : ℕ)^1 * ((269 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 24749)^12374 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (2 : ZMod 24749)^1076 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
        subst q
        change (2 : ZMod 24749)^92 ≠ 1
        reduce_mod_char
        decide

theorem prime_24809 : Nat.Prime 24809 := by
  apply lucas_primality 24809 (6 : ZMod 24809)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24809 - 1 = (2 : ℕ)^3 * ((7 : ℕ)^1 * ((443 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 24809)^12404 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (6 : ZMod 24809)^3544 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 443 := Nat.prime_eq_prime_of_dvd_pow hq prime_443 hd
        subst q
        change (6 : ZMod 24809)^56 ≠ 1
        reduce_mod_char
        decide

theorem prime_24907 : Nat.Prime 24907 := by
  apply lucas_primality 24907 (2 : ZMod 24907)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24907 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((593 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 24907)^12453 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 24907)^8302 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 24907)^3558 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 593 := Nat.prime_eq_prime_of_dvd_pow hq prime_593 hd
          subst q
          change (2 : ZMod 24907)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_24917 : Nat.Prime 24917 := by
  apply lucas_primality 24917 (2 : ZMod 24917)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24917 - 1 = (2 : ℕ)^2 * ((6229 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 24917)^12458 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 6229 := Nat.prime_eq_prime_of_dvd_pow hq prime_6229 hd
      subst q
      change (2 : ZMod 24917)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_24923 : Nat.Prime 24923 := by
  apply lucas_primality 24923 (2 : ZMod 24923)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24923 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((733 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 24923)^12461 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 24923)^1466 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 733 := Nat.prime_eq_prime_of_dvd_pow hq prime_733 hd
        subst q
        change (2 : ZMod 24923)^34 ≠ 1
        reduce_mod_char
        decide

theorem prime_24953 : Nat.Prime 24953 := by
  apply lucas_primality 24953 (3 : ZMod 24953)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24953 - 1 = (2 : ℕ)^3 * ((3119 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 24953)^12476 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3119 := Nat.prime_eq_prime_of_dvd_pow hq prime_3119 hd
      subst q
      change (3 : ZMod 24953)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_25073 : Nat.Prime 25073 := by
  apply lucas_primality 25073 (3 : ZMod 25073)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 25073 - 1 = (2 : ℕ)^4 * ((1567 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 25073)^12536 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1567 := Nat.prime_eq_prime_of_dvd_pow hq prime_1567 hd
      subst q
      change (3 : ZMod 25073)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_25121 : Nat.Prime 25121 := by
  apply lucas_primality 25121 (3 : ZMod 25121)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 25121 - 1 = (2 : ℕ)^5 * ((5 : ℕ)^1 * ((157 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 25121)^12560 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 25121)^5024 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
        subst q
        change (3 : ZMod 25121)^160 ≠ 1
        reduce_mod_char
        decide

theorem prime_25169 : Nat.Prime 25169 := by
  apply lucas_primality 25169 (3 : ZMod 25169)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 25169 - 1 = (2 : ℕ)^4 * ((11 : ℕ)^2 * ((13 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 25169)^12584 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 25169)^2288 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 25169)^1936 ≠ 1
        reduce_mod_char
        decide

theorem prime_25219 : Nat.Prime 25219 := by
  apply lucas_primality 25219 (2 : ZMod 25219)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 25219 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((467 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 25219)^12609 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 25219)^8406 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 467 := Nat.prime_eq_prime_of_dvd_pow hq prime_467 hd
        subst q
        change (2 : ZMod 25219)^54 ≠ 1
        reduce_mod_char
        decide

theorem prime_25367 : Nat.Prime 25367 := by
  apply lucas_primality 25367 (5 : ZMod 25367)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 25367 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((1153 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 25367)^12683 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 25367)^2306 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1153 := Nat.prime_eq_prime_of_dvd_pow hq prime_1153 hd
        subst q
        change (5 : ZMod 25367)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_25523 : Nat.Prime 25523 := by
  apply lucas_primality 25523 (2 : ZMod 25523)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 25523 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((1823 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 25523)^12761 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 25523)^3646 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1823 := Nat.prime_eq_prime_of_dvd_pow hq prime_1823 hd
        subst q
        change (2 : ZMod 25523)^14 ≠ 1
        reduce_mod_char
        decide

end LegendreK6.Pratt
