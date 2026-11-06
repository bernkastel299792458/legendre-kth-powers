import LegendreK6.Pratt.Block015

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LegendreK6.Pratt

theorem prime_530356027 : Nat.Prime 530356027 := by
  apply lucas_primality 530356027 (11 : ZMod 530356027)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 530356027 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((409 : ℕ)^1 * ((216119 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 530356027)^265178013 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 530356027)^176785342 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 409 := Nat.prime_eq_prime_of_dvd_pow hq prime_409 hd
          subst q
          change (11 : ZMod 530356027)^1296714 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 216119 := Nat.prime_eq_prime_of_dvd_pow hq prime_216119 hd
          subst q
          change (11 : ZMod 530356027)^2454 ≠ 1
          reduce_mod_char
          decide

theorem prime_551730913 : Nat.Prime 551730913 := by
  apply lucas_primality 551730913 (5 : ZMod 551730913)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 551730913 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((1471 : ℕ)^1 * ((3907 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 551730913)^275865456 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 551730913)^183910304 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1471 := Nat.prime_eq_prime_of_dvd_pow hq prime_1471 hd
          subst q
          change (5 : ZMod 551730913)^375072 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3907 := Nat.prime_eq_prime_of_dvd_pow hq prime_3907 hd
          subst q
          change (5 : ZMod 551730913)^141216 ≠ 1
          reduce_mod_char
          decide

theorem prime_561482087 : Nat.Prime 561482087 := by
  apply lucas_primality 561482087 (5 : ZMod 561482087)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 561482087 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((269 : ℕ)^1 * ((5581 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 561482087)^280741043 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 561482087)^51043826 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (5 : ZMod 561482087)^33028358 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
            subst q
            change (5 : ZMod 561482087)^2087294 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 5581 := Nat.prime_eq_prime_of_dvd_pow hq prime_5581 hd
            subst q
            change (5 : ZMod 561482087)^100606 ≠ 1
            reduce_mod_char
            decide

theorem prime_571661777 : Nat.Prime 571661777 := by
  apply lucas_primality 571661777 (3 : ZMod 571661777)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 571661777 - 1 = (2 : ℕ)^4 * ((7 : ℕ)^1 * ((5104123 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 571661777)^285830888 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 571661777)^81665968 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5104123 := Nat.prime_eq_prime_of_dvd_pow hq prime_5104123 hd
        subst q
        change (3 : ZMod 571661777)^112 ≠ 1
        reduce_mod_char
        decide

theorem prime_575774209 : Nat.Prime 575774209 := by
  apply lucas_primality 575774209 (14 : ZMod 575774209)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 575774209 - 1 = (2 : ℕ)^9 * ((3 : ℕ)^2 * ((124951 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 575774209)^287887104 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 575774209)^191924736 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 124951 := Nat.prime_eq_prime_of_dvd_pow hq prime_124951 hd
        subst q
        change (14 : ZMod 575774209)^4608 ≠ 1
        reduce_mod_char
        decide

theorem prime_581619673 : Nat.Prime 581619673 := by
  apply lucas_primality 581619673 (5 : ZMod 581619673)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 581619673 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((8078051 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 581619673)^290809836 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 581619673)^193873224 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 8078051 := Nat.prime_eq_prime_of_dvd_pow hq prime_8078051 hd
        subst q
        change (5 : ZMod 581619673)^72 ≠ 1
        reduce_mod_char
        decide

theorem prime_593702821 : Nat.Prime 593702821 := by
  apply lucas_primality 593702821 (7 : ZMod 593702821)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 593702821 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((53 : ℕ)^1 * ((62233 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 593702821)^296851410 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 593702821)^197900940 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 593702821)^118740564 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
            subst q
            change (7 : ZMod 593702821)^11201940 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 62233 := Nat.prime_eq_prime_of_dvd_pow hq prime_62233 hd
            subst q
            change (7 : ZMod 593702821)^9540 ≠ 1
            reduce_mod_char
            decide

theorem prime_593796613 : Nat.Prime 593796613 := by
  apply lucas_primality 593796613 (5 : ZMod 593796613)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 593796613 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((67 : ℕ)^1 * ((163 : ℕ)^1 * ((197 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 593796613)^296898306 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 593796613)^197932204 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (5 : ZMod 593796613)^25817244 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
            subst q
            change (5 : ZMod 593796613)^8862636 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
              subst q
              change (5 : ZMod 593796613)^3642924 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
              subst q
              change (5 : ZMod 593796613)^3014196 ≠ 1
              reduce_mod_char
              decide

theorem prime_594823337 : Nat.Prime 594823337 := by
  apply lucas_primality 594823337 (3 : ZMod 594823337)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 594823337 - 1 = (2 : ℕ)^3 * ((17 : ℕ)^1 * ((4373701 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 594823337)^297411668 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (3 : ZMod 594823337)^34989608 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4373701 := Nat.prime_eq_prime_of_dvd_pow hq prime_4373701 hd
        subst q
        change (3 : ZMod 594823337)^136 ≠ 1
        reduce_mod_char
        decide

theorem prime_600143977 : Nat.Prime 600143977 := by
  apply lucas_primality 600143977 (7 : ZMod 600143977)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 600143977 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((827 : ℕ)^1 * ((10079 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 600143977)^300071988 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 600143977)^200047992 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 827 := Nat.prime_eq_prime_of_dvd_pow hq prime_827 hd
          subst q
          change (7 : ZMod 600143977)^725688 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 10079 := Nat.prime_eq_prime_of_dvd_pow hq prime_10079 hd
          subst q
          change (7 : ZMod 600143977)^59544 ≠ 1
          reduce_mod_char
          decide

theorem prime_604351537 : Nat.Prime 604351537 := by
  apply lucas_primality 604351537 (5 : ZMod 604351537)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 604351537 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((337 : ℕ)^1 * ((37361 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 604351537)^302175768 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 604351537)^201450512 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 337 := Nat.prime_eq_prime_of_dvd_pow hq prime_337 hd
          subst q
          change (5 : ZMod 604351537)^1793328 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 37361 := Nat.prime_eq_prime_of_dvd_pow hq prime_37361 hd
          subst q
          change (5 : ZMod 604351537)^16176 ≠ 1
          reduce_mod_char
          decide

theorem prime_604529771 : Nat.Prime 604529771 := by
  apply lucas_primality 604529771 (2 : ZMod 604529771)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 604529771 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((211 : ℕ)^1 * ((22039 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 604529771)^302264885 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 604529771)^120905954 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 604529771)^46502290 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 211 := Nat.prime_eq_prime_of_dvd_pow hq prime_211 hd
            subst q
            change (2 : ZMod 604529771)^2865070 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 22039 := Nat.prime_eq_prime_of_dvd_pow hq prime_22039 hd
            subst q
            change (2 : ZMod 604529771)^27430 ≠ 1
            reduce_mod_char
            decide

theorem prime_622011029 : Nat.Prime 622011029 := by
  apply lucas_primality 622011029 (2 : ZMod 622011029)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 622011029 - 1 = (2 : ℕ)^2 * ((17 : ℕ)^1 * ((587 : ℕ)^1 * ((15583 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 622011029)^311005514 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 622011029)^36588884 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 587 := Nat.prime_eq_prime_of_dvd_pow hq prime_587 hd
          subst q
          change (2 : ZMod 622011029)^1059644 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 15583 := Nat.prime_eq_prime_of_dvd_pow hq prime_15583 hd
          subst q
          change (2 : ZMod 622011029)^39916 ≠ 1
          reduce_mod_char
          decide

theorem prime_623096989 : Nat.Prime 623096989 := by
  apply lucas_primality 623096989 (2 : ZMod 623096989)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 623096989 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((233 : ℕ)^1 * ((13109 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 623096989)^311548494 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 623096989)^207698996 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 623096989)^36652764 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
            subst q
            change (2 : ZMod 623096989)^2674236 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 13109 := Nat.prime_eq_prime_of_dvd_pow hq prime_13109 hd
            subst q
            change (2 : ZMod 623096989)^47532 ≠ 1
            reduce_mod_char
            decide

theorem prime_635215247 : Nat.Prime 635215247 := by
  apply lucas_primality 635215247 (7 : ZMod 635215247)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 635215247 - 1 = (2 : ℕ)^1 * ((29 : ℕ)^1 * ((47 : ℕ)^1 * ((233021 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 635215247)^317607623 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (7 : ZMod 635215247)^21903974 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (7 : ZMod 635215247)^13515218 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 233021 := Nat.prime_eq_prime_of_dvd_pow hq prime_233021 hd
          subst q
          change (7 : ZMod 635215247)^2726 ≠ 1
          reduce_mod_char
          decide

theorem prime_641020297 : Nat.Prime 641020297 := by
  apply lucas_primality 641020297 (5 : ZMod 641020297)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 641020297 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((3815597 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 641020297)^320510148 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 641020297)^213673432 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 641020297)^91574328 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3815597 := Nat.prime_eq_prime_of_dvd_pow hq prime_3815597 hd
          subst q
          change (5 : ZMod 641020297)^168 ≠ 1
          reduce_mod_char
          decide

theorem prime_642898339 : Nat.Prime 642898339 := by
  apply lucas_primality 642898339 (2 : ZMod 642898339)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 642898339 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((59 : ℕ)^1 * ((683 : ℕ)^1 * ((2659 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 642898339)^321449169 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 642898339)^214299446 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (2 : ZMod 642898339)^10896582 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 683 := Nat.prime_eq_prime_of_dvd_pow hq prime_683 hd
            subst q
            change (2 : ZMod 642898339)^941286 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2659 := Nat.prime_eq_prime_of_dvd_pow hq prime_2659 hd
            subst q
            change (2 : ZMod 642898339)^241782 ≠ 1
            reduce_mod_char
            decide

theorem prime_644711869 : Nat.Prime 644711869 := by
  apply lucas_primality 644711869 (6 : ZMod 644711869)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 644711869 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((193 : ℕ)^1 * ((92791 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 644711869)^322355934 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 644711869)^214903956 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
          subst q
          change (6 : ZMod 644711869)^3340476 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 92791 := Nat.prime_eq_prime_of_dvd_pow hq prime_92791 hd
          subst q
          change (6 : ZMod 644711869)^6948 ≠ 1
          reduce_mod_char
          decide

theorem prime_645734003 : Nat.Prime 645734003 := by
  apply lucas_primality 645734003 (2 : ZMod 645734003)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 645734003 - 1 = (2 : ℕ)^1 * ((2909 : ℕ)^1 * ((110989 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 645734003)^322867001 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 2909 := Nat.prime_eq_prime_of_dvd_pow hq prime_2909 hd
        subst q
        change (2 : ZMod 645734003)^221978 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 110989 := Nat.prime_eq_prime_of_dvd_pow hq prime_110989 hd
        subst q
        change (2 : ZMod 645734003)^5818 ≠ 1
        reduce_mod_char
        decide

theorem prime_645978919 : Nat.Prime 645978919 := by
  apply lucas_primality 645978919 (6 : ZMod 645978919)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 645978919 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((1091 : ℕ)^1 * ((7591 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 645978919)^322989459 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 645978919)^215326306 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (6 : ZMod 645978919)^49690686 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1091 := Nat.prime_eq_prime_of_dvd_pow hq prime_1091 hd
            subst q
            change (6 : ZMod 645978919)^592098 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 7591 := Nat.prime_eq_prime_of_dvd_pow hq prime_7591 hd
            subst q
            change (6 : ZMod 645978919)^85098 ≠ 1
            reduce_mod_char
            decide

theorem prime_646971131 : Nat.Prime 646971131 := by
  apply lucas_primality 646971131 (6 : ZMod 646971131)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 646971131 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((4976701 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 646971131)^323485565 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 646971131)^129394226 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (6 : ZMod 646971131)^49767010 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4976701 := Nat.prime_eq_prime_of_dvd_pow hq prime_4976701 hd
          subst q
          change (6 : ZMod 646971131)^130 ≠ 1
          reduce_mod_char
          decide

theorem prime_653784553 : Nat.Prime 653784553 := by
  apply lucas_primality 653784553 (10 : ZMod 653784553)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 653784553 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((107 : ℕ)^1 * ((113 : ℕ)^1 * ((751 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 653784553)^326892276 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 653784553)^217928184 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
          subst q
          change (10 : ZMod 653784553)^6110136 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
            subst q
            change (10 : ZMod 653784553)^5785704 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 751 := Nat.prime_eq_prime_of_dvd_pow hq prime_751 hd
            subst q
            change (10 : ZMod 653784553)^870552 ≠ 1
            reduce_mod_char
            decide

theorem prime_654701809 : Nat.Prime 654701809 := by
  apply lucas_primality 654701809 (7 : ZMod 654701809)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 654701809 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((179 : ℕ)^1 * ((3313 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 654701809)^327350904 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 654701809)^218233936 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (7 : ZMod 654701809)^28465296 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 179 := Nat.prime_eq_prime_of_dvd_pow hq prime_179 hd
            subst q
            change (7 : ZMod 654701809)^3657552 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3313 := Nat.prime_eq_prime_of_dvd_pow hq prime_3313 hd
            subst q
            change (7 : ZMod 654701809)^197616 ≠ 1
            reduce_mod_char
            decide

theorem prime_683517739 : Nat.Prime 683517739 := by
  apply lucas_primality 683517739 (3 : ZMod 683517739)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 683517739 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((8803 : ℕ)^1 * ((12941 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 683517739)^341758869 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 683517739)^227839246 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 8803 := Nat.prime_eq_prime_of_dvd_pow hq prime_8803 hd
          subst q
          change (3 : ZMod 683517739)^77646 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 12941 := Nat.prime_eq_prime_of_dvd_pow hq prime_12941 hd
          subst q
          change (3 : ZMod 683517739)^52818 ≠ 1
          reduce_mod_char
          decide

theorem prime_685115671 : Nat.Prime 685115671 := by
  apply lucas_primality 685115671 (11 : ZMod 685115671)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 685115671 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((59 : ℕ)^1 * ((387071 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 685115671)^342557835 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 685115671)^228371890 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 685115671)^137023134 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
            subst q
            change (11 : ZMod 685115671)^11612130 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 387071 := Nat.prime_eq_prime_of_dvd_pow hq prime_387071 hd
            subst q
            change (11 : ZMod 685115671)^1770 ≠ 1
            reduce_mod_char
            decide

theorem prime_687411259 : Nat.Prime 687411259 := by
  apply lucas_primality 687411259 (3 : ZMod 687411259)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 687411259 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((89 : ℕ)^1 * ((97 : ℕ)^1 * ((577 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 687411259)^343705629 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 687411259)^229137086 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (3 : ZMod 687411259)^29887446 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
            subst q
            change (3 : ZMod 687411259)^7723722 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
              subst q
              change (3 : ZMod 687411259)^7086714 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 577 := Nat.prime_eq_prime_of_dvd_pow hq prime_577 hd
              subst q
              change (3 : ZMod 687411259)^1191354 ≠ 1
              reduce_mod_char
              decide

theorem prime_688246079 : Nat.Prime 688246079 := by
  apply lucas_primality 688246079 (11 : ZMod 688246079)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 688246079 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^2 * ((89 : ℕ)^1 * ((137 : ℕ)^1 * ((167 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 688246079)^344123039 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (11 : ZMod 688246079)^52942006 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (11 : ZMod 688246079)^7733102 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
            subst q
            change (11 : ZMod 688246079)^5023694 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
            subst q
            change (11 : ZMod 688246079)^4121234 ≠ 1
            reduce_mod_char
            decide

theorem prime_694807831 : Nat.Prime 694807831 := by
  apply lucas_primality 694807831 (6 : ZMod 694807831)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 694807831 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((37 : ℕ)^1 * ((137 : ℕ)^1 * ((1523 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 694807831)^347403915 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 694807831)^231602610 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 694807831)^138961566 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
            subst q
            change (6 : ZMod 694807831)^18778590 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
              subst q
              change (6 : ZMod 694807831)^5071590 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1523 := Nat.prime_eq_prime_of_dvd_pow hq prime_1523 hd
              subst q
              change (6 : ZMod 694807831)^456210 ≠ 1
              reduce_mod_char
              decide

theorem prime_708648979 : Nat.Prime 708648979 := by
  apply lucas_primality 708648979 (3 : ZMod 708648979)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 708648979 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((6947539 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 708648979)^354324489 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 708648979)^236216326 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (3 : ZMod 708648979)^41685234 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 6947539 := Nat.prime_eq_prime_of_dvd_pow hq prime_6947539 hd
          subst q
          change (3 : ZMod 708648979)^102 ≠ 1
          reduce_mod_char
          decide

theorem prime_709737871 : Nat.Prime 709737871 := by
  apply lucas_primality 709737871 (15 : ZMod 709737871)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 709737871 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((31 : ℕ)^1 * ((763159 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (15 : ZMod 709737871)^354868935 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (15 : ZMod 709737871)^236579290 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (15 : ZMod 709737871)^141947574 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (15 : ZMod 709737871)^22894770 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 763159 := Nat.prime_eq_prime_of_dvd_pow hq prime_763159 hd
            subst q
            change (15 : ZMod 709737871)^930 ≠ 1
            reduce_mod_char
            decide

theorem prime_725596351 : Nat.Prime 725596351 := by
  apply lucas_primality 725596351 (7 : ZMod 725596351)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 725596351 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((4837309 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 725596351)^362798175 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 725596351)^241865450 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 725596351)^145119270 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4837309 := Nat.prime_eq_prime_of_dvd_pow hq prime_4837309 hd
          subst q
          change (7 : ZMod 725596351)^150 ≠ 1
          reduce_mod_char
          decide

theorem prime_729000007 : Nat.Prime 729000007 := by
  apply lucas_primality 729000007 (3 : ZMod 729000007)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 729000007 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((17357143 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 729000007)^364500003 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 729000007)^243000002 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 729000007)^104142858 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17357143 := Nat.prime_eq_prime_of_dvd_pow hq prime_17357143 hd
          subst q
          change (3 : ZMod 729000007)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_732897577 : Nat.Prime 732897577 := by
  apply lucas_primality 732897577 (5 : ZMod 732897577)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 732897577 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((23 : ℕ)^1 * ((442571 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 732897577)^366448788 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 732897577)^244299192 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (5 : ZMod 732897577)^31865112 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 442571 := Nat.prime_eq_prime_of_dvd_pow hq prime_442571 hd
          subst q
          change (5 : ZMod 732897577)^1656 ≠ 1
          reduce_mod_char
          decide

theorem prime_762759197 : Nat.Prime 762759197 := by
  apply lucas_primality 762759197 (2 : ZMod 762759197)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 762759197 - 1 = (2 : ℕ)^2 * ((17 : ℕ)^1 * ((11217047 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 762759197)^381379598 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 762759197)^44868188 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 11217047 := Nat.prime_eq_prime_of_dvd_pow hq prime_11217047 hd
        subst q
        change (2 : ZMod 762759197)^68 ≠ 1
        reduce_mod_char
        decide

theorem prime_768974749 : Nat.Prime 768974749 := by
  apply lucas_primality 768974749 (6 : ZMod 768974749)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 768974749 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((83 : ℕ)^1 * ((151 : ℕ)^1 * ((5113 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 768974749)^384487374 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 768974749)^256324916 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
          subst q
          change (6 : ZMod 768974749)^9264756 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
            subst q
            change (6 : ZMod 768974749)^5092548 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 5113 := Nat.prime_eq_prime_of_dvd_pow hq prime_5113 hd
            subst q
            change (6 : ZMod 768974749)^150396 ≠ 1
            reduce_mod_char
            decide

theorem prime_775294577 : Nat.Prime 775294577 := by
  apply lucas_primality 775294577 (3 : ZMod 775294577)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 775294577 - 1 = (2 : ℕ)^4 * ((7 : ℕ)^1 * ((6922273 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 775294577)^387647288 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 775294577)^110756368 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 6922273 := Nat.prime_eq_prime_of_dvd_pow hq prime_6922273 hd
        subst q
        change (3 : ZMod 775294577)^112 ≠ 1
        reduce_mod_char
        decide

theorem prime_795044027 : Nat.Prime 795044027 := by
  apply lucas_primality 795044027 (2 : ZMod 795044027)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 795044027 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((107 : ℕ)^1 * ((269 : ℕ)^1 * ((1973 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 795044027)^397522013 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 795044027)^113577718 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
          subst q
          change (2 : ZMod 795044027)^7430318 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
            subst q
            change (2 : ZMod 795044027)^2955554 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1973 := Nat.prime_eq_prime_of_dvd_pow hq prime_1973 hd
            subst q
            change (2 : ZMod 795044027)^402962 ≠ 1
            reduce_mod_char
            decide

theorem prime_796969477 : Nat.Prime 796969477 := by
  apply lucas_primality 796969477 (5 : ZMod 796969477)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 796969477 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((7379347 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 796969477)^398484738 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 796969477)^265656492 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7379347 := Nat.prime_eq_prime_of_dvd_pow hq prime_7379347 hd
        subst q
        change (5 : ZMod 796969477)^108 ≠ 1
        reduce_mod_char
        decide

theorem prime_817217273 : Nat.Prime 817217273 := by
  apply lucas_primality 817217273 (3 : ZMod 817217273)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 817217273 - 1 = (2 : ℕ)^3 * ((613 : ℕ)^1 * ((166643 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 817217273)^408608636 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 613 := Nat.prime_eq_prime_of_dvd_pow hq prime_613 hd
        subst q
        change (3 : ZMod 817217273)^1333144 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 166643 := Nat.prime_eq_prime_of_dvd_pow hq prime_166643 hd
        subst q
        change (3 : ZMod 817217273)^4904 ≠ 1
        reduce_mod_char
        decide

theorem prime_827011193 : Nat.Prime 827011193 := by
  apply lucas_primality 827011193 (5 : ZMod 827011193)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 827011193 - 1 = (2 : ℕ)^3 * ((7 : ℕ)^1 * ((937 : ℕ)^1 * ((15761 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 827011193)^413505596 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 827011193)^118144456 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 937 := Nat.prime_eq_prime_of_dvd_pow hq prime_937 hd
          subst q
          change (5 : ZMod 827011193)^882616 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 15761 := Nat.prime_eq_prime_of_dvd_pow hq prime_15761 hd
          subst q
          change (5 : ZMod 827011193)^52472 ≠ 1
          reduce_mod_char
          decide

theorem prime_831055721 : Nat.Prime 831055721 := by
  apply lucas_primality 831055721 (3 : ZMod 831055721)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 831055721 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((1888763 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 831055721)^415527860 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 831055721)^166211144 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 831055721)^75550520 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1888763 := Nat.prime_eq_prime_of_dvd_pow hq prime_1888763 hd
          subst q
          change (3 : ZMod 831055721)^440 ≠ 1
          reduce_mod_char
          decide

theorem prime_834027217 : Nat.Prime 834027217 := by
  apply lucas_primality 834027217 (5 : ZMod 834027217)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 834027217 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((1579597 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 834027217)^417013608 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 834027217)^278009072 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 834027217)^75820656 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1579597 := Nat.prime_eq_prime_of_dvd_pow hq prime_1579597 hd
          subst q
          change (5 : ZMod 834027217)^528 ≠ 1
          reduce_mod_char
          decide

theorem prime_835611407 : Nat.Prime 835611407 := by
  apply lucas_primality 835611407 (5 : ZMod 835611407)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 835611407 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^2 * ((41 : ℕ)^1 * ((207967 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 835611407)^417805703 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 835611407)^119373058 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (5 : ZMod 835611407)^20380766 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 207967 := Nat.prime_eq_prime_of_dvd_pow hq prime_207967 hd
          subst q
          change (5 : ZMod 835611407)^4018 ≠ 1
          reduce_mod_char
          decide

theorem prime_845108141 : Nat.Prime 845108141 := by
  apply lucas_primality 845108141 (2 : ZMod 845108141)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 845108141 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((29 : ℕ)^1 * ((1457083 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 845108141)^422554070 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 845108141)^169021628 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (2 : ZMod 845108141)^29141660 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1457083 := Nat.prime_eq_prime_of_dvd_pow hq prime_1457083 hd
          subst q
          change (2 : ZMod 845108141)^580 ≠ 1
          reduce_mod_char
          decide

theorem prime_861971633 : Nat.Prime 861971633 := by
  apply lucas_primality 861971633 (3 : ZMod 861971633)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 861971633 - 1 = (2 : ℕ)^4 * ((19 : ℕ)^1 * ((2835433 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 861971633)^430985816 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (3 : ZMod 861971633)^45366928 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2835433 := Nat.prime_eq_prime_of_dvd_pow hq prime_2835433 hd
        subst q
        change (3 : ZMod 861971633)^304 ≠ 1
        reduce_mod_char
        decide

theorem prime_876566389 : Nat.Prime 876566389 := by
  apply lucas_primality 876566389 (2 : ZMod 876566389)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 876566389 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((41 : ℕ)^1 * ((997 : ℕ)^1 * ((1787 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 876566389)^438283194 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 876566389)^292188796 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (2 : ZMod 876566389)^21379668 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 997 := Nat.prime_eq_prime_of_dvd_pow hq prime_997 hd
            subst q
            change (2 : ZMod 876566389)^879204 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1787 := Nat.prime_eq_prime_of_dvd_pow hq prime_1787 hd
            subst q
            change (2 : ZMod 876566389)^490524 ≠ 1
            reduce_mod_char
            decide

theorem prime_887503693 : Nat.Prime 887503693 := by
  apply lucas_primality 887503693 (2 : ZMod 887503693)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 887503693 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((71 : ℕ)^1 * ((1041671 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 887503693)^443751846 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 887503693)^295834564 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
          subst q
          change (2 : ZMod 887503693)^12500052 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1041671 := Nat.prime_eq_prime_of_dvd_pow hq prime_1041671 hd
          subst q
          change (2 : ZMod 887503693)^852 ≠ 1
          reduce_mod_char
          decide

theorem prime_888415607 : Nat.Prime 888415607 := by
  apply lucas_primality 888415607 (7 : ZMod 888415607)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 888415607 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((34169831 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 888415607)^444207803 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (7 : ZMod 888415607)^68339662 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 34169831 := Nat.prime_eq_prime_of_dvd_pow hq prime_34169831 hd
        subst q
        change (7 : ZMod 888415607)^26 ≠ 1
        reduce_mod_char
        decide

theorem prime_890028547 : Nat.Prime 890028547 := by
  apply lucas_primality 890028547 (3 : ZMod 890028547)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 890028547 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((13485281 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 890028547)^445014273 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 890028547)^296676182 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 890028547)^80911686 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13485281 := Nat.prime_eq_prime_of_dvd_pow hq prime_13485281 hd
          subst q
          change (3 : ZMod 890028547)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_893596031 : Nat.Prime 893596031 := by
  apply lucas_primality 893596031 (17 : ZMod 893596031)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 893596031 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((19 : ℕ)^1 * ((1879 : ℕ)^1 * ((2503 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 893596031)^446798015 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (17 : ZMod 893596031)^178719206 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (17 : ZMod 893596031)^47031370 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1879 := Nat.prime_eq_prime_of_dvd_pow hq prime_1879 hd
            subst q
            change (17 : ZMod 893596031)^475570 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2503 := Nat.prime_eq_prime_of_dvd_pow hq prime_2503 hd
            subst q
            change (17 : ZMod 893596031)^357010 ≠ 1
            reduce_mod_char
            decide

theorem prime_895269241 : Nat.Prime 895269241 := by
  apply lucas_primality 895269241 (7 : ZMod 895269241)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 895269241 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((828953 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 895269241)^447634620 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 895269241)^298423080 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 895269241)^179053848 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 828953 := Nat.prime_eq_prime_of_dvd_pow hq prime_828953 hd
          subst q
          change (7 : ZMod 895269241)^1080 ≠ 1
          reduce_mod_char
          decide

theorem prime_902410417 : Nat.Prime 902410417 := by
  apply lucas_primality 902410417 (5 : ZMod 902410417)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 902410417 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^3 * ((2088913 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 902410417)^451205208 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 902410417)^300803472 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2088913 := Nat.prime_eq_prime_of_dvd_pow hq prime_2088913 hd
        subst q
        change (5 : ZMod 902410417)^432 ≠ 1
        reduce_mod_char
        decide

theorem prime_913777933 : Nat.Prime 913777933 := by
  apply lucas_primality 913777933 (2 : ZMod 913777933)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 913777933 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((727 : ℕ)^1 * ((104743 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 913777933)^456888966 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 913777933)^304592644 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 727 := Nat.prime_eq_prime_of_dvd_pow hq prime_727 hd
          subst q
          change (2 : ZMod 913777933)^1256916 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 104743 := Nat.prime_eq_prime_of_dvd_pow hq prime_104743 hd
          subst q
          change (2 : ZMod 913777933)^8724 ≠ 1
          reduce_mod_char
          decide

theorem prime_924264469 : Nat.Prime 924264469 := by
  apply lucas_primality 924264469 (6 : ZMod 924264469)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 924264469 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((25674013 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 924264469)^462132234 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 924264469)^308088156 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 25674013 := Nat.prime_eq_prime_of_dvd_pow hq prime_25674013 hd
        subst q
        change (6 : ZMod 924264469)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_936064513 : Nat.Prime 936064513 := by
  apply lucas_primality 936064513 (5 : ZMod 936064513)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 936064513 - 1 = (2 : ℕ)^9 * ((3 : ℕ)^4 * ((22571 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 936064513)^468032256 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 936064513)^312021504 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 22571 := Nat.prime_eq_prime_of_dvd_pow hq prime_22571 hd
        subst q
        change (5 : ZMod 936064513)^41472 ≠ 1
        reduce_mod_char
        decide

theorem prime_940865587 : Nat.Prime 940865587 := by
  apply lucas_primality 940865587 (3 : ZMod 940865587)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 940865587 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((61 : ℕ)^1 * ((2570671 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 940865587)^470432793 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 940865587)^313621862 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (3 : ZMod 940865587)^15424026 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2570671 := Nat.prime_eq_prime_of_dvd_pow hq prime_2570671 hd
          subst q
          change (3 : ZMod 940865587)^366 ≠ 1
          reduce_mod_char
          decide

theorem prime_960460733 : Nat.Prime 960460733 := by
  apply lucas_primality 960460733 (2 : ZMod 960460733)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 960460733 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((11 : ℕ)^2 * ((283489 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 960460733)^480230366 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 960460733)^137208676 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 960460733)^87314612 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 283489 := Nat.prime_eq_prime_of_dvd_pow hq prime_283489 hd
          subst q
          change (2 : ZMod 960460733)^3388 ≠ 1
          reduce_mod_char
          decide

theorem prime_982301321 : Nat.Prime 982301321 := by
  apply lucas_primality 982301321 (6 : ZMod 982301321)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 982301321 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((24533 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 982301321)^491150660 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 982301321)^196460264 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 982301321)^140328760 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (6 : ZMod 982301321)^89300120 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
              subst q
              change (6 : ZMod 982301321)^75561640 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 24533 := Nat.prime_eq_prime_of_dvd_pow hq prime_24533 hd
              subst q
              change (6 : ZMod 982301321)^40040 ≠ 1
              reduce_mod_char
              decide

theorem prime_988295141 : Nat.Prime 988295141 := by
  apply lucas_primality 988295141 (2 : ZMod 988295141)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 988295141 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((7059251 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 988295141)^494147570 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 988295141)^197659028 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 988295141)^141185020 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7059251 := Nat.prime_eq_prime_of_dvd_pow hq prime_7059251 hd
          subst q
          change (2 : ZMod 988295141)^140 ≠ 1
          reduce_mod_char
          decide

theorem prime_999081053 : Nat.Prime 999081053 := by
  apply lucas_primality 999081053 (2 : ZMod 999081053)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 999081053 - 1 = (2 : ℕ)^2 * ((249770263 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 999081053)^499540526 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 249770263 := Nat.prime_eq_prime_of_dvd_pow hq prime_249770263 hd
      subst q
      change (2 : ZMod 999081053)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_1010591669 : Nat.Prime 1010591669 := by
  apply lucas_primality 1010591669 (2 : ZMod 1010591669)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1010591669 - 1 = (2 : ℕ)^2 * ((252647917 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1010591669)^505295834 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 252647917 := Nat.prime_eq_prime_of_dvd_pow hq prime_252647917 hd
      subst q
      change (2 : ZMod 1010591669)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_1032506597 : Nat.Prime 1032506597 := by
  apply lucas_primality 1032506597 (2 : ZMod 1032506597)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1032506597 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((23466059 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1032506597)^516253298 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 1032506597)^93864236 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 23466059 := Nat.prime_eq_prime_of_dvd_pow hq prime_23466059 hd
        subst q
        change (2 : ZMod 1032506597)^44 ≠ 1
        reduce_mod_char
        decide

theorem prime_1073741827 : Nat.Prime 1073741827 := by
  apply lucas_primality 1073741827 (2 : ZMod 1073741827)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1073741827 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((59 : ℕ)^1 * ((3033169 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1073741827)^536870913 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1073741827)^357913942 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (2 : ZMod 1073741827)^18199014 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3033169 := Nat.prime_eq_prime_of_dvd_pow hq prime_3033169 hd
          subst q
          change (2 : ZMod 1073741827)^354 ≠ 1
          reduce_mod_char
          decide

theorem prime_1087036829 : Nat.Prime 1087036829 := by
  apply lucas_primality 1087036829 (2 : ZMod 1087036829)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1087036829 - 1 = (2 : ℕ)^2 * ((4481 : ℕ)^1 * ((60647 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1087036829)^543518414 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 4481 := Nat.prime_eq_prime_of_dvd_pow hq prime_4481 hd
        subst q
        change (2 : ZMod 1087036829)^242588 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 60647 := Nat.prime_eq_prime_of_dvd_pow hq prime_60647 hd
        subst q
        change (2 : ZMod 1087036829)^17924 ≠ 1
        reduce_mod_char
        decide

theorem prime_1091077159 : Nat.Prime 1091077159 := by
  apply lucas_primality 1091077159 (3 : ZMod 1091077159)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1091077159 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((41 : ℕ)^1 * ((521 : ℕ)^1 * ((8513 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1091077159)^545538579 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1091077159)^363692386 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (3 : ZMod 1091077159)^26611638 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 521 := Nat.prime_eq_prime_of_dvd_pow hq prime_521 hd
            subst q
            change (3 : ZMod 1091077159)^2094198 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 8513 := Nat.prime_eq_prime_of_dvd_pow hq prime_8513 hd
            subst q
            change (3 : ZMod 1091077159)^128166 ≠ 1
            reduce_mod_char
            decide

theorem prime_1094410337 : Nat.Prime 1094410337 := by
  apply lucas_primality 1094410337 (3 : ZMod 1094410337)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1094410337 - 1 = (2 : ℕ)^5 * ((19 : ℕ)^1 * ((1800017 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1094410337)^547205168 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (3 : ZMod 1094410337)^57600544 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1800017 := Nat.prime_eq_prime_of_dvd_pow hq prime_1800017 hd
        subst q
        change (3 : ZMod 1094410337)^608 ≠ 1
        reduce_mod_char
        decide

theorem prime_1109338801 : Nat.Prime 1109338801 := by
  apply lucas_primality 1109338801 (11 : ZMod 1109338801)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1109338801 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((571 : ℕ)^1 * ((1619 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 1109338801)^554669400 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 1109338801)^369779600 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 1109338801)^221867760 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 571 := Nat.prime_eq_prime_of_dvd_pow hq prime_571 hd
            subst q
            change (11 : ZMod 1109338801)^1942800 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1619 := Nat.prime_eq_prime_of_dvd_pow hq prime_1619 hd
            subst q
            change (11 : ZMod 1109338801)^685200 ≠ 1
            reduce_mod_char
            decide

theorem prime_1118068711 : Nat.Prime 1118068711 := by
  apply lucas_primality 1118068711 (11 : ZMod 1118068711)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1118068711 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((3388087 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 1118068711)^559034355 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 1118068711)^372689570 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 1118068711)^223613742 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (11 : ZMod 1118068711)^101642610 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3388087 := Nat.prime_eq_prime_of_dvd_pow hq prime_3388087 hd
            subst q
            change (11 : ZMod 1118068711)^330 ≠ 1
            reduce_mod_char
            decide

theorem prime_1124995957 : Nat.Prime 1124995957 := by
  apply lucas_primality 1124995957 (5 : ZMod 1124995957)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1124995957 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((29 : ℕ)^1 * ((89 : ℕ)^1 * ((5189 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1124995957)^562497978 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1124995957)^374998652 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 1124995957)^160713708 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (5 : ZMod 1124995957)^38792964 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
              subst q
              change (5 : ZMod 1124995957)^12640404 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 5189 := Nat.prime_eq_prime_of_dvd_pow hq prime_5189 hd
              subst q
              change (5 : ZMod 1124995957)^216804 ≠ 1
              reduce_mod_char
              decide

theorem prime_1175951729 : Nat.Prime 1175951729 := by
  apply lucas_primality 1175951729 (3 : ZMod 1175951729)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1175951729 - 1 = (2 : ℕ)^4 * ((7 : ℕ)^1 * ((23 : ℕ)^1 * ((456503 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1175951729)^587975864 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 1175951729)^167993104 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (3 : ZMod 1175951729)^51128336 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 456503 := Nat.prime_eq_prime_of_dvd_pow hq prime_456503 hd
          subst q
          change (3 : ZMod 1175951729)^2576 ≠ 1
          reduce_mod_char
          decide

theorem prime_1188995261 : Nat.Prime 1188995261 := by
  apply lucas_primality 1188995261 (2 : ZMod 1188995261)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1188995261 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((59449763 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1188995261)^594497630 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 1188995261)^237799052 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 59449763 := Nat.prime_eq_prime_of_dvd_pow hq prime_59449763 hd
        subst q
        change (2 : ZMod 1188995261)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_1190038711 : Nat.Prime 1190038711 := by
  apply lucas_primality 1190038711 (12 : ZMod 1190038711)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1190038711 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((683 : ℕ)^1 * ((8297 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (12 : ZMod 1190038711)^595019355 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (12 : ZMod 1190038711)^396679570 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (12 : ZMod 1190038711)^238007742 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (12 : ZMod 1190038711)^170005530 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 683 := Nat.prime_eq_prime_of_dvd_pow hq prime_683 hd
              subst q
              change (12 : ZMod 1190038711)^1742370 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 8297 := Nat.prime_eq_prime_of_dvd_pow hq prime_8297 hd
              subst q
              change (12 : ZMod 1190038711)^143430 ≠ 1
              reduce_mod_char
              decide

theorem prime_1200917467 : Nat.Prime 1200917467 := by
  apply lucas_primality 1200917467 (2 : ZMod 1200917467)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1200917467 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((139 : ℕ)^1 * ((191 : ℕ)^1 * ((359 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1200917467)^600458733 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1200917467)^400305822 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 1200917467)^171559638 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
            subst q
            change (2 : ZMod 1200917467)^8639694 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
              subst q
              change (2 : ZMod 1200917467)^6287526 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 359 := Nat.prime_eq_prime_of_dvd_pow hq prime_359 hd
              subst q
              change (2 : ZMod 1200917467)^3345174 ≠ 1
              reduce_mod_char
              decide

theorem prime_1232514757 : Nat.Prime 1232514757 := by
  apply lucas_primality 1232514757 (2 : ZMod 1232514757)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1232514757 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((223 : ℕ)^1 * ((821 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1232514757)^616257378 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1232514757)^410838252 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 1232514757)^112046796 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (2 : ZMod 1232514757)^72500868 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 223 := Nat.prime_eq_prime_of_dvd_pow hq prime_223 hd
              subst q
              change (2 : ZMod 1232514757)^5526972 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 821 := Nat.prime_eq_prime_of_dvd_pow hq prime_821 hd
              subst q
              change (2 : ZMod 1232514757)^1501236 ≠ 1
              reduce_mod_char
              decide

theorem prime_1255332151 : Nat.Prime 1255332151 := by
  apply lucas_primality 1255332151 (3 : ZMod 1255332151)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1255332151 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^2 * ((2789627 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1255332151)^627666075 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1255332151)^418444050 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 1255332151)^251066430 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2789627 := Nat.prime_eq_prime_of_dvd_pow hq prime_2789627 hd
          subst q
          change (3 : ZMod 1255332151)^450 ≠ 1
          reduce_mod_char
          decide

theorem prime_1256096507 : Nat.Prime 1256096507 := by
  apply lucas_primality 1256096507 (5 : ZMod 1256096507)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1256096507 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((61 : ℕ)^1 * ((1470839 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1256096507)^628048253 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 1256096507)^179442358 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (5 : ZMod 1256096507)^20591746 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1470839 := Nat.prime_eq_prime_of_dvd_pow hq prime_1470839 hd
          subst q
          change (5 : ZMod 1256096507)^854 ≠ 1
          reduce_mod_char
          decide

theorem prime_1275628147 : Nat.Prime 1275628147 := by
  apply lucas_primality 1275628147 (5 : ZMod 1275628147)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1275628147 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((1613 : ℕ)^1 * ((10139 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1275628147)^637814073 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1275628147)^425209382 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (5 : ZMod 1275628147)^98125242 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1613 := Nat.prime_eq_prime_of_dvd_pow hq prime_1613 hd
            subst q
            change (5 : ZMod 1275628147)^790842 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 10139 := Nat.prime_eq_prime_of_dvd_pow hq prime_10139 hd
            subst q
            change (5 : ZMod 1275628147)^125814 ≠ 1
            reduce_mod_char
            decide

theorem prime_1291468007 : Nat.Prime 1291468007 := by
  apply lucas_primality 1291468007 (5 : ZMod 1291468007)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1291468007 - 1 = (2 : ℕ)^1 * ((645734003 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1291468007)^645734003 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 645734003 := Nat.prime_eq_prime_of_dvd_pow hq prime_645734003 hd
      subst q
      change (5 : ZMod 1291468007)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_1310645353 : Nat.Prime 1310645353 := by
  apply lucas_primality 1310645353 (5 : ZMod 1310645353)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1310645353 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((59 : ℕ)^1 * ((925597 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1310645353)^655322676 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1310645353)^436881784 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (5 : ZMod 1310645353)^22214328 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 925597 := Nat.prime_eq_prime_of_dvd_pow hq prime_925597 hd
          subst q
          change (5 : ZMod 1310645353)^1416 ≠ 1
          reduce_mod_char
          decide

theorem prime_1316004097 : Nat.Prime 1316004097 := by
  apply lucas_primality 1316004097 (5 : ZMod 1316004097)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1316004097 - 1 = (2 : ℕ)^8 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((155777 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1316004097)^658002048 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1316004097)^438668032 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 1316004097)^119636736 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 155777 := Nat.prime_eq_prime_of_dvd_pow hq prime_155777 hd
          subst q
          change (5 : ZMod 1316004097)^8448 ≠ 1
          reduce_mod_char
          decide

theorem prime_1335657949 : Nat.Prime 1335657949 := by
  apply lucas_primality 1335657949 (6 : ZMod 1335657949)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1335657949 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((111304829 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 1335657949)^667828974 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 1335657949)^445219316 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 111304829 := Nat.prime_eq_prime_of_dvd_pow hq prime_111304829 hd
        subst q
        change (6 : ZMod 1335657949)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_1345011841 : Nat.Prime 1345011841 := by
  apply lucas_primality 1345011841 (14 : ZMod 1345011841)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1345011841 - 1 = (2 : ℕ)^7 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((233509 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 1345011841)^672505920 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 1345011841)^448337280 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (14 : ZMod 1345011841)^269002368 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 233509 := Nat.prime_eq_prime_of_dvd_pow hq prime_233509 hd
          subst q
          change (14 : ZMod 1345011841)^5760 ≠ 1
          reduce_mod_char
          decide

theorem prime_1347401917 : Nat.Prime 1347401917 := by
  apply lucas_primality 1347401917 (2 : ZMod 1347401917)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1347401917 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((23 : ℕ)^1 * ((37 : ℕ)^1 * ((61 : ℕ)^1 * ((103 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1347401917)^673700958 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1347401917)^449133972 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 1347401917)^192485988 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (2 : ZMod 1347401917)^58582692 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
              subst q
              change (2 : ZMod 1347401917)^36416268 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
                subst q
                change (2 : ZMod 1347401917)^22088556 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
                subst q
                change (2 : ZMod 1347401917)^13081572 ≠ 1
                reduce_mod_char
                decide

theorem prime_1349422093 : Nat.Prime 1349422093 := by
  apply lucas_primality 1349422093 (2 : ZMod 1349422093)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1349422093 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^4 * ((131 : ℕ)^1 * ((31793 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1349422093)^674711046 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1349422093)^449807364 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
          subst q
          change (2 : ZMod 1349422093)^10300932 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 31793 := Nat.prime_eq_prime_of_dvd_pow hq prime_31793 hd
          subst q
          change (2 : ZMod 1349422093)^42444 ≠ 1
          reduce_mod_char
          decide

theorem prime_1350035803 : Nat.Prime 1350035803 := by
  apply lucas_primality 1350035803 (2 : ZMod 1350035803)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1350035803 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((31 : ℕ)^1 * ((47 : ℕ)^1 * ((17159 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1350035803)^675017901 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1350035803)^450011934 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (2 : ZMod 1350035803)^43549542 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
            subst q
            change (2 : ZMod 1350035803)^28724166 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 17159 := Nat.prime_eq_prime_of_dvd_pow hq prime_17159 hd
            subst q
            change (2 : ZMod 1350035803)^78678 ≠ 1
            reduce_mod_char
            decide

theorem prime_1352563687 : Nat.Prime 1352563687 := by
  apply lucas_primality 1352563687 (3 : ZMod 1352563687)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1352563687 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((139 : ℕ)^1 * ((193 : ℕ)^1 * ((2801 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1352563687)^676281843 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1352563687)^450854562 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
          subst q
          change (3 : ZMod 1352563687)^9730674 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
            subst q
            change (3 : ZMod 1352563687)^7008102 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2801 := Nat.prime_eq_prime_of_dvd_pow hq prime_2801 hd
            subst q
            change (3 : ZMod 1352563687)^482886 ≠ 1
            reduce_mod_char
            decide

theorem prime_1356390019 : Nat.Prime 1356390019 := by
  apply lucas_primality 1356390019 (3 : ZMod 1356390019)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1356390019 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((6163 : ℕ)^1 * ((12227 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1356390019)^678195009 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1356390019)^452130006 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 6163 := Nat.prime_eq_prime_of_dvd_pow hq prime_6163 hd
          subst q
          change (3 : ZMod 1356390019)^220086 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 12227 := Nat.prime_eq_prime_of_dvd_pow hq prime_12227 hd
          subst q
          change (3 : ZMod 1356390019)^110934 ≠ 1
          reduce_mod_char
          decide

theorem prime_1364031287 : Nat.Prime 1364031287 := by
  apply lucas_primality 1364031287 (5 : ZMod 1364031287)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1364031287 - 1 = (2 : ℕ)^1 * ((10433 : ℕ)^1 * ((65371 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1364031287)^682015643 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 10433 := Nat.prime_eq_prime_of_dvd_pow hq prime_10433 hd
        subst q
        change (5 : ZMod 1364031287)^130742 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 65371 := Nat.prime_eq_prime_of_dvd_pow hq prime_65371 hd
        subst q
        change (5 : ZMod 1364031287)^20866 ≠ 1
        reduce_mod_char
        decide

theorem prime_1367139931 : Nat.Prime 1367139931 := by
  apply lucas_primality 1367139931 (3 : ZMod 1367139931)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1367139931 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((61 : ℕ)^1 * ((57467 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1367139931)^683569965 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1367139931)^455713310 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 1367139931)^273427986 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (3 : ZMod 1367139931)^105164610 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
              subst q
              change (3 : ZMod 1367139931)^22412130 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 57467 := Nat.prime_eq_prime_of_dvd_pow hq prime_57467 hd
              subst q
              change (3 : ZMod 1367139931)^23790 ≠ 1
              reduce_mod_char
              decide

theorem prime_1388355169 : Nat.Prime 1388355169 := by
  apply lucas_primality 1388355169 (13 : ZMod 1388355169)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1388355169 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((167 : ℕ)^1 * ((86599 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 1388355169)^694177584 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 1388355169)^462785056 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
          subst q
          change (13 : ZMod 1388355169)^8313504 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 86599 := Nat.prime_eq_prime_of_dvd_pow hq prime_86599 hd
          subst q
          change (13 : ZMod 1388355169)^16032 ≠ 1
          reduce_mod_char
          decide

theorem prime_1399075823 : Nat.Prime 1399075823 := by
  apply lucas_primality 1399075823 (5 : ZMod 1399075823)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1399075823 - 1 = (2 : ℕ)^1 * ((109 : ℕ)^1 * ((6417779 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1399075823)^699537911 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
        subst q
        change (5 : ZMod 1399075823)^12835558 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 6417779 := Nat.prime_eq_prime_of_dvd_pow hq prime_6417779 hd
        subst q
        change (5 : ZMod 1399075823)^218 ≠ 1
        reduce_mod_char
        decide

theorem prime_1417722491 : Nat.Prime 1417722491 := by
  apply lucas_primality 1417722491 (2 : ZMod 1417722491)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1417722491 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((141772249 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1417722491)^708861245 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 1417722491)^283544498 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 141772249 := Nat.prime_eq_prime_of_dvd_pow hq prime_141772249 hd
        subst q
        change (2 : ZMod 1417722491)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_1439489473 : Nat.Prime 1439489473 := by
  apply lucas_primality 1439489473 (13 : ZMod 1439489473)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1439489473 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^1 * ((29 : ℕ)^1 * ((263 : ℕ)^1 * ((983 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 1439489473)^719744736 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 1439489473)^479829824 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (13 : ZMod 1439489473)^49637568 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 263 := Nat.prime_eq_prime_of_dvd_pow hq prime_263 hd
            subst q
            change (13 : ZMod 1439489473)^5473344 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 983 := Nat.prime_eq_prime_of_dvd_pow hq prime_983 hd
            subst q
            change (13 : ZMod 1439489473)^1464384 ≠ 1
            reduce_mod_char
            decide

theorem prime_1507173457 : Nat.Prime 1507173457 := by
  apply lucas_primality 1507173457 (7 : ZMod 1507173457)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1507173457 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((103 : ℕ)^1 * ((304849 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1507173457)^753586728 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 1507173457)^502391152 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
          subst q
          change (7 : ZMod 1507173457)^14632752 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 304849 := Nat.prime_eq_prime_of_dvd_pow hq prime_304849 hd
          subst q
          change (7 : ZMod 1507173457)^4944 ≠ 1
          reduce_mod_char
          decide

theorem prime_1531663597 : Nat.Prime 1531663597 := by
  apply lucas_primality 1531663597 (2 : ZMod 1531663597)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1531663597 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((42546211 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1531663597)^765831798 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1531663597)^510554532 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 42546211 := Nat.prime_eq_prime_of_dvd_pow hq prime_42546211 hd
        subst q
        change (2 : ZMod 1531663597)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_1543841659 : Nat.Prime 1543841659 := by
  apply lucas_primality 1543841659 (2 : ZMod 1543841659)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1543841659 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5189 : ℕ)^1 * ((16529 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1543841659)^771920829 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1543841659)^514613886 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5189 := Nat.prime_eq_prime_of_dvd_pow hq prime_5189 hd
          subst q
          change (2 : ZMod 1543841659)^297522 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 16529 := Nat.prime_eq_prime_of_dvd_pow hq prime_16529 hd
          subst q
          change (2 : ZMod 1543841659)^93402 ≠ 1
          reduce_mod_char
          decide

theorem prime_1544804447 : Nat.Prime 1544804447 := by
  apply lucas_primality 1544804447 (5 : ZMod 1544804447)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1544804447 - 1 = (2 : ℕ)^1 * ((233 : ℕ)^1 * ((3315031 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1544804447)^772402223 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
        subst q
        change (5 : ZMod 1544804447)^6630062 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3315031 := Nat.prime_eq_prime_of_dvd_pow hq prime_3315031 hd
        subst q
        change (5 : ZMod 1544804447)^466 ≠ 1
        reduce_mod_char
        decide

theorem prime_1549795019 : Nat.Prime 1549795019 := by
  apply lucas_primality 1549795019 (2 : ZMod 1549795019)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1549795019 - 1 = (2 : ℕ)^1 * ((193 : ℕ)^1 * ((4015013 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1549795019)^774897509 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
        subst q
        change (2 : ZMod 1549795019)^8030026 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4015013 := Nat.prime_eq_prime_of_dvd_pow hq prime_4015013 hd
        subst q
        change (2 : ZMod 1549795019)^386 ≠ 1
        reduce_mod_char
        decide

theorem prime_1589190653 : Nat.Prime 1589190653 := by
  apply lucas_primality 1589190653 (2 : ZMod 1589190653)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1589190653 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((877 : ℕ)^1 * ((64717 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1589190653)^794595326 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 1589190653)^227027236 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 877 := Nat.prime_eq_prime_of_dvd_pow hq prime_877 hd
          subst q
          change (2 : ZMod 1589190653)^1812076 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 64717 := Nat.prime_eq_prime_of_dvd_pow hq prime_64717 hd
          subst q
          change (2 : ZMod 1589190653)^24556 ≠ 1
          reduce_mod_char
          decide

theorem prime_1589414311 : Nat.Prime 1589414311 := by
  apply lucas_primality 1589414311 (3 : ZMod 1589414311)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1589414311 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((23 : ℕ)^1 * ((29 : ℕ)^2 * ((83 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1589414311)^794707155 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1589414311)^529804770 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 1589414311)^317882862 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (3 : ZMod 1589414311)^144492210 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
              subst q
              change (3 : ZMod 1589414311)^69104970 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
                subst q
                change (3 : ZMod 1589414311)^54807390 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
                subst q
                change (3 : ZMod 1589414311)^19149570 ≠ 1
                reduce_mod_char
                decide

theorem prime_1589829869 : Nat.Prime 1589829869 := by
  apply lucas_primality 1589829869 (2 : ZMod 1589829869)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1589829869 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((67 : ℕ)^1 * ((31723 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1589829869)^794914934 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 1589829869)^144529988 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 1589829869)^93519404 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
            subst q
            change (2 : ZMod 1589829869)^23728804 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 31723 := Nat.prime_eq_prime_of_dvd_pow hq prime_31723 hd
            subst q
            change (2 : ZMod 1589829869)^50116 ≠ 1
            reduce_mod_char
            decide

theorem prime_1604483761 : Nat.Prime 1604483761 := by
  apply lucas_primality 1604483761 (19 : ZMod 1604483761)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1604483761 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((59 : ℕ)^1 * ((10301 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 1604483761)^802241880 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 1604483761)^534827920 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (19 : ZMod 1604483761)^320896752 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (19 : ZMod 1604483761)^145862160 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
              subst q
              change (19 : ZMod 1604483761)^27194640 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 10301 := Nat.prime_eq_prime_of_dvd_pow hq prime_10301 hd
              subst q
              change (19 : ZMod 1604483761)^155760 ≠ 1
              reduce_mod_char
              decide

theorem prime_1613266843 : Nat.Prime 1613266843 := by
  apply lucas_primality 1613266843 (13 : ZMod 1613266843)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1613266843 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((24443437 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 1613266843)^806633421 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 1613266843)^537755614 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (13 : ZMod 1613266843)^146660622 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 24443437 := Nat.prime_eq_prime_of_dvd_pow hq prime_24443437 hd
          subst q
          change (13 : ZMod 1613266843)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_1625003209 : Nat.Prime 1625003209 := by
  apply lucas_primality 1625003209 (26 : ZMod 1625003209)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1625003209 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^5 * ((17 : ℕ)^1 * ((49171 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (26 : ZMod 1625003209)^812501604 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (26 : ZMod 1625003209)^541667736 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (26 : ZMod 1625003209)^95588424 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 49171 := Nat.prime_eq_prime_of_dvd_pow hq prime_49171 hd
          subst q
          change (26 : ZMod 1625003209)^33048 ≠ 1
          reduce_mod_char
          decide

theorem prime_1631083313 : Nat.Prime 1631083313 := by
  apply lucas_primality 1631083313 (3 : ZMod 1631083313)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1631083313 - 1 = (2 : ℕ)^4 * ((101942707 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1631083313)^815541656 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 101942707 := Nat.prime_eq_prime_of_dvd_pow hq prime_101942707 hd
      subst q
      change (3 : ZMod 1631083313)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_1638509767 : Nat.Prime 1638509767 := by
  apply lucas_primality 1638509767 (3 : ZMod 1638509767)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1638509767 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((273084961 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1638509767)^819254883 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1638509767)^546169922 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 273084961 := Nat.prime_eq_prime_of_dvd_pow hq prime_273084961 hd
        subst q
        change (3 : ZMod 1638509767)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_1666265941 : Nat.Prime 1666265941 := by
  apply lucas_primality 1666265941 (6 : ZMod 1666265941)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1666265941 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((53 : ℕ)^1 * ((389 : ℕ)^1 * ((449 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 1666265941)^833132970 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 1666265941)^555421980 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 1666265941)^333253188 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
            subst q
            change (6 : ZMod 1666265941)^31438980 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 389 := Nat.prime_eq_prime_of_dvd_pow hq prime_389 hd
              subst q
              change (6 : ZMod 1666265941)^4283460 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 449 := Nat.prime_eq_prime_of_dvd_pow hq prime_449 hd
              subst q
              change (6 : ZMod 1666265941)^3711060 ≠ 1
              reduce_mod_char
              decide

theorem prime_1691837689 : Nat.Prime 1691837689 := by
  apply lucas_primality 1691837689 (29 : ZMod 1691837689)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1691837689 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((4146661 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (29 : ZMod 1691837689)^845918844 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (29 : ZMod 1691837689)^563945896 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (29 : ZMod 1691837689)^99519864 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4146661 := Nat.prime_eq_prime_of_dvd_pow hq prime_4146661 hd
          subst q
          change (29 : ZMod 1691837689)^408 ≠ 1
          reduce_mod_char
          decide

theorem prime_1694349109 : Nat.Prime 1694349109 := by
  apply lucas_primality 1694349109 (2 : ZMod 1694349109)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1694349109 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((41 : ℕ)^1 * ((727 : ℕ)^1 * ((1579 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1694349109)^847174554 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1694349109)^564783036 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (2 : ZMod 1694349109)^41325588 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 727 := Nat.prime_eq_prime_of_dvd_pow hq prime_727 hd
            subst q
            change (2 : ZMod 1694349109)^2330604 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1579 := Nat.prime_eq_prime_of_dvd_pow hq prime_1579 hd
            subst q
            change (2 : ZMod 1694349109)^1073052 ≠ 1
            reduce_mod_char
            decide

theorem prime_1713799777 : Nat.Prime 1713799777 := by
  apply lucas_primality 1713799777 (5 : ZMod 1713799777)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1713799777 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((29 : ℕ)^1 * ((47353 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1713799777)^856899888 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1713799777)^571266592 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (5 : ZMod 1713799777)^131830752 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (5 : ZMod 1713799777)^59096544 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 47353 := Nat.prime_eq_prime_of_dvd_pow hq prime_47353 hd
            subst q
            change (5 : ZMod 1713799777)^36192 ≠ 1
            reduce_mod_char
            decide

theorem prime_1725827533 : Nat.Prime 1725827533 := by
  apply lucas_primality 1725827533 (6 : ZMod 1725827533)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1725827533 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((19 : ℕ)^1 * ((43 : ℕ)^1 * ((1231 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 1725827533)^862913766 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 1725827533)^575275844 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (6 : ZMod 1725827533)^156893412 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (6 : ZMod 1725827533)^132755964 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
              subst q
              change (6 : ZMod 1725827533)^90833028 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
                subst q
                change (6 : ZMod 1725827533)^40135524 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 1231 := Nat.prime_eq_prime_of_dvd_pow hq prime_1231 hd
                subst q
                change (6 : ZMod 1725827533)^1401972 ≠ 1
                reduce_mod_char
                decide

theorem prime_1802930137 : Nat.Prime 1802930137 := by
  apply lucas_primality 1802930137 (5 : ZMod 1802930137)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1802930137 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((10731727 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1802930137)^901465068 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1802930137)^600976712 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 1802930137)^257561448 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 10731727 := Nat.prime_eq_prime_of_dvd_pow hq prime_10731727 hd
          subst q
          change (5 : ZMod 1802930137)^168 ≠ 1
          reduce_mod_char
          decide

theorem prime_1805954611 : Nat.Prime 1805954611 := by
  apply lucas_primality 1805954611 (10 : ZMod 1805954611)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1805954611 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((60198487 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 1805954611)^902977305 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 1805954611)^601984870 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 1805954611)^361190922 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 60198487 := Nat.prime_eq_prime_of_dvd_pow hq prime_60198487 hd
          subst q
          change (10 : ZMod 1805954611)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_1817731921 : Nat.Prime 1817731921 := by
  apply lucas_primality 1817731921 (7 : ZMod 1817731921)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1817731921 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7573883 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1817731921)^908865960 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 1817731921)^605910640 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 1817731921)^363546384 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7573883 := Nat.prime_eq_prime_of_dvd_pow hq prime_7573883 hd
          subst q
          change (7 : ZMod 1817731921)^240 ≠ 1
          reduce_mod_char
          decide

theorem prime_1838265647 : Nat.Prime 1838265647 := by
  apply lucas_primality 1838265647 (5 : ZMod 1838265647)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1838265647 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((3331 : ℕ)^1 * ((39419 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1838265647)^919132823 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 1838265647)^262609378 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 3331 := Nat.prime_eq_prime_of_dvd_pow hq prime_3331 hd
          subst q
          change (5 : ZMod 1838265647)^551866 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 39419 := Nat.prime_eq_prime_of_dvd_pow hq prime_39419 hd
          subst q
          change (5 : ZMod 1838265647)^46634 ≠ 1
          reduce_mod_char
          decide

theorem prime_1838605843 : Nat.Prime 1838605843 := by
  apply lucas_primality 1838605843 (2 : ZMod 1838605843)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1838605843 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((1471 : ℕ)^1 * ((69439 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1838605843)^919302921 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1838605843)^612868614 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1471 := Nat.prime_eq_prime_of_dvd_pow hq prime_1471 hd
          subst q
          change (2 : ZMod 1838605843)^1249902 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 69439 := Nat.prime_eq_prime_of_dvd_pow hq prime_69439 hd
          subst q
          change (2 : ZMod 1838605843)^26478 ≠ 1
          reduce_mod_char
          decide

theorem prime_1843553449 : Nat.Prime 1843553449 := by
  apply lucas_primality 1843553449 (7 : ZMod 1843553449)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1843553449 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((43 : ℕ)^1 * ((54133 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1843553449)^921776724 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 1843553449)^614517816 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (7 : ZMod 1843553449)^167595768 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (7 : ZMod 1843553449)^42873336 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 54133 := Nat.prime_eq_prime_of_dvd_pow hq prime_54133 hd
            subst q
            change (7 : ZMod 1843553449)^34056 ≠ 1
            reduce_mod_char
            decide

theorem prime_1851324029 : Nat.Prime 1851324029 := by
  apply lucas_primality 1851324029 (2 : ZMod 1851324029)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1851324029 - 1 = (2 : ℕ)^2 * ((19841 : ℕ)^1 * ((23327 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1851324029)^925662014 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19841 := Nat.prime_eq_prime_of_dvd_pow hq prime_19841 hd
        subst q
        change (2 : ZMod 1851324029)^93308 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 23327 := Nat.prime_eq_prime_of_dvd_pow hq prime_23327 hd
        subst q
        change (2 : ZMod 1851324029)^79364 ≠ 1
        reduce_mod_char
        decide

theorem prime_1861861909 : Nat.Prime 1861861909 := by
  apply lucas_primality 1861861909 (2 : ZMod 1861861909)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1861861909 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((8166061 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1861861909)^930930954 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1861861909)^620620636 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 1861861909)^97992732 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 8166061 := Nat.prime_eq_prime_of_dvd_pow hq prime_8166061 hd
          subst q
          change (2 : ZMod 1861861909)^228 ≠ 1
          reduce_mod_char
          decide

theorem prime_1939429537 : Nat.Prime 1939429537 := by
  apply lucas_primality 1939429537 (7 : ZMod 1939429537)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1939429537 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((1836581 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1939429537)^969714768 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 1939429537)^646476512 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (7 : ZMod 1939429537)^176311776 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1836581 := Nat.prime_eq_prime_of_dvd_pow hq prime_1836581 hd
          subst q
          change (7 : ZMod 1939429537)^1056 ≠ 1
          reduce_mod_char
          decide

theorem prime_2014441243 : Nat.Prime 2014441243 := by
  apply lucas_primality 2014441243 (2 : ZMod 2014441243)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2014441243 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((1747 : ℕ)^1 * ((17471 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2014441243)^1007220621 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2014441243)^671480414 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 2014441243)^183131022 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1747 := Nat.prime_eq_prime_of_dvd_pow hq prime_1747 hd
            subst q
            change (2 : ZMod 2014441243)^1153086 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 17471 := Nat.prime_eq_prime_of_dvd_pow hq prime_17471 hd
            subst q
            change (2 : ZMod 2014441243)^115302 ≠ 1
            reduce_mod_char
            decide

theorem prime_2049162229 : Nat.Prime 2049162229 := by
  apply lucas_primality 2049162229 (2 : ZMod 2049162229)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2049162229 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((599 : ℕ)^1 * ((95027 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2049162229)^1024581114 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2049162229)^683054076 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 599 := Nat.prime_eq_prime_of_dvd_pow hq prime_599 hd
          subst q
          change (2 : ZMod 2049162229)^3420972 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 95027 := Nat.prime_eq_prime_of_dvd_pow hq prime_95027 hd
          subst q
          change (2 : ZMod 2049162229)^21564 ≠ 1
          reduce_mod_char
          decide

theorem prime_2089430983 : Nat.Prime 2089430983 := by
  apply lucas_primality 2089430983 (3 : ZMod 2089430983)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2089430983 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((1459 : ℕ)^1 * ((79561 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2089430983)^1044715491 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 2089430983)^696476994 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1459 := Nat.prime_eq_prime_of_dvd_pow hq prime_1459 hd
          subst q
          change (3 : ZMod 2089430983)^1432098 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 79561 := Nat.prime_eq_prime_of_dvd_pow hq prime_79561 hd
          subst q
          change (3 : ZMod 2089430983)^26262 ≠ 1
          reduce_mod_char
          decide

theorem prime_2093566009 : Nat.Prime 2093566009 := by
  apply lucas_primality 2093566009 (7 : ZMod 2093566009)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2093566009 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((87231917 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2093566009)^1046783004 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 2093566009)^697855336 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 87231917 := Nat.prime_eq_prime_of_dvd_pow hq prime_87231917 hd
        subst q
        change (7 : ZMod 2093566009)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_2101813507 : Nat.Prime 2101813507 := by
  apply lucas_primality 2101813507 (2 : ZMod 2101813507)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2101813507 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((13 : ℕ)^1 * ((8982109 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2101813507)^1050906753 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2101813507)^700604502 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 2101813507)^161677962 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 8982109 := Nat.prime_eq_prime_of_dvd_pow hq prime_8982109 hd
          subst q
          change (2 : ZMod 2101813507)^234 ≠ 1
          reduce_mod_char
          decide

theorem prime_2109026683 : Nat.Prime 2109026683 := by
  apply lucas_primality 2109026683 (2 : ZMod 2109026683)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2109026683 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((29 : ℕ)^1 * ((163 : ℕ)^1 * ((3541 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2109026683)^1054513341 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2109026683)^703008894 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 2109026683)^301289526 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (2 : ZMod 2109026683)^72725058 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
              subst q
              change (2 : ZMod 2109026683)^12938814 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 3541 := Nat.prime_eq_prime_of_dvd_pow hq prime_3541 hd
              subst q
              change (2 : ZMod 2109026683)^595602 ≠ 1
              reduce_mod_char
              decide

theorem prime_2111234117 : Nat.Prime 2111234117 := by
  apply lucas_primality 2111234117 (2 : ZMod 2111234117)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2111234117 - 1 = (2 : ℕ)^2 * ((137 : ℕ)^1 * ((179 : ℕ)^1 * ((21523 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2111234117)^1055617058 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
        subst q
        change (2 : ZMod 2111234117)^15410468 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 179 := Nat.prime_eq_prime_of_dvd_pow hq prime_179 hd
          subst q
          change (2 : ZMod 2111234117)^11794604 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 21523 := Nat.prime_eq_prime_of_dvd_pow hq prime_21523 hd
          subst q
          change (2 : ZMod 2111234117)^98092 ≠ 1
          reduce_mod_char
          decide

theorem prime_2116847801 : Nat.Prime 2116847801 := by
  apply lucas_primality 2116847801 (3 : ZMod 2116847801)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2116847801 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^2 * ((2393 : ℕ)^1 * ((4423 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2116847801)^1058423900 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 2116847801)^423369560 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2393 := Nat.prime_eq_prime_of_dvd_pow hq prime_2393 hd
          subst q
          change (3 : ZMod 2116847801)^884600 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4423 := Nat.prime_eq_prime_of_dvd_pow hq prime_4423 hd
          subst q
          change (3 : ZMod 2116847801)^478600 ≠ 1
          reduce_mod_char
          decide

theorem prime_2168570071 : Nat.Prime 2168570071 := by
  apply lucas_primality 2168570071 (6 : ZMod 2168570071)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2168570071 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((5 : ℕ)^1 * ((107 : ℕ)^1 * ((131 : ℕ)^1 * ((191 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 2168570071)^1084285035 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 2168570071)^722856690 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 2168570071)^433714014 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
            subst q
            change (6 : ZMod 2168570071)^20267010 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
              subst q
              change (6 : ZMod 2168570071)^16553970 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
              subst q
              change (6 : ZMod 2168570071)^11353770 ≠ 1
              reduce_mod_char
              decide

theorem prime_2176782371 : Nat.Prime 2176782371 := by
  apply lucas_primality 2176782371 (2 : ZMod 2176782371)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2176782371 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^2 * ((4442413 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2176782371)^1088391185 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 2176782371)^435356474 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 2176782371)^310968910 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4442413 := Nat.prime_eq_prime_of_dvd_pow hq prime_4442413 hd
          subst q
          change (2 : ZMod 2176782371)^490 ≠ 1
          reduce_mod_char
          decide

theorem prime_2182361833 : Nat.Prime 2182361833 := by
  apply lucas_primality 2182361833 (5 : ZMod 2182361833)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2182361833 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((409 : ℕ)^1 * ((3529 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2182361833)^1091180916 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 2182361833)^727453944 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 2182361833)^311765976 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 409 := Nat.prime_eq_prime_of_dvd_pow hq prime_409 hd
            subst q
            change (5 : ZMod 2182361833)^5335848 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3529 := Nat.prime_eq_prime_of_dvd_pow hq prime_3529 hd
            subst q
            change (5 : ZMod 2182361833)^618408 ≠ 1
            reduce_mod_char
            decide

theorem prime_2207962213 : Nat.Prime 2207962213 := by
  apply lucas_primality 2207962213 (13 : ZMod 2207962213)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2207962213 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((29 : ℕ)^1 * ((101 : ℕ)^1 * ((62819 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 2207962213)^1103981106 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 2207962213)^735987404 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (13 : ZMod 2207962213)^76136628 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
            subst q
            change (13 : ZMod 2207962213)^21861012 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 62819 := Nat.prime_eq_prime_of_dvd_pow hq prime_62819 hd
            subst q
            change (13 : ZMod 2207962213)^35148 ≠ 1
            reduce_mod_char
            decide

theorem prime_2224045897 : Nat.Prime 2224045897 := by
  apply lucas_primality 2224045897 (11 : ZMod 2224045897)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2224045897 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((31 : ℕ)^1 * ((2989309 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 2224045897)^1112022948 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 2224045897)^741348632 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (11 : ZMod 2224045897)^71743416 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2989309 := Nat.prime_eq_prime_of_dvd_pow hq prime_2989309 hd
          subst q
          change (11 : ZMod 2224045897)^744 ≠ 1
          reduce_mod_char
          decide

theorem prime_2301836213 : Nat.Prime 2301836213 := by
  apply lucas_primality 2301836213 (2 : ZMod 2301836213)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2301836213 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((4919 : ℕ)^1 * ((8999 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2301836213)^1150918106 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 2301836213)^177064324 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 4919 := Nat.prime_eq_prime_of_dvd_pow hq prime_4919 hd
          subst q
          change (2 : ZMod 2301836213)^467948 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 8999 := Nat.prime_eq_prime_of_dvd_pow hq prime_8999 hd
          subst q
          change (2 : ZMod 2301836213)^255788 ≠ 1
          reduce_mod_char
          decide

theorem prime_2302238299 : Nat.Prime 2302238299 := by
  apply lucas_primality 2302238299 (3 : ZMod 2302238299)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2302238299 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((383706383 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2302238299)^1151119149 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 2302238299)^767412766 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 383706383 := Nat.prime_eq_prime_of_dvd_pow hq prime_383706383 hd
        subst q
        change (3 : ZMod 2302238299)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_2336243843 : Nat.Prime 2336243843 := by
  apply lucas_primality 2336243843 (2 : ZMod 2336243843)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2336243843 - 1 = (2 : ℕ)^1 * ((3169 : ℕ)^1 * ((368609 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2336243843)^1168121921 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3169 := Nat.prime_eq_prime_of_dvd_pow hq prime_3169 hd
        subst q
        change (2 : ZMod 2336243843)^737218 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 368609 := Nat.prime_eq_prime_of_dvd_pow hq prime_368609 hd
        subst q
        change (2 : ZMod 2336243843)^6338 ≠ 1
        reduce_mod_char
        decide

theorem prime_2375186453 : Nat.Prime 2375186453 := by
  apply lucas_primality 2375186453 (2 : ZMod 2375186453)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2375186453 - 1 = (2 : ℕ)^2 * ((593796613 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2375186453)^1187593226 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 593796613 := Nat.prime_eq_prime_of_dvd_pow hq prime_593796613 hd
      subst q
      change (2 : ZMod 2375186453)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_2391283261 : Nat.Prime 2391283261 := by
  apply lucas_primality 2391283261 (6 : ZMod 2391283261)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2391283261 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((1447 : ℕ)^1 * ((9181 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 2391283261)^1195641630 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 2391283261)^797094420 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 2391283261)^478256652 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1447 := Nat.prime_eq_prime_of_dvd_pow hq prime_1447 hd
            subst q
            change (6 : ZMod 2391283261)^1652580 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 9181 := Nat.prime_eq_prime_of_dvd_pow hq prime_9181 hd
            subst q
            change (6 : ZMod 2391283261)^260460 ≠ 1
            reduce_mod_char
            decide

theorem prime_2391694213 : Nat.Prime 2391694213 := by
  apply lucas_primality 2391694213 (5 : ZMod 2391694213)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2391694213 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((1867 : ℕ)^1 * ((106753 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2391694213)^1195847106 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 2391694213)^797231404 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1867 := Nat.prime_eq_prime_of_dvd_pow hq prime_1867 hd
          subst q
          change (5 : ZMod 2391694213)^1281036 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 106753 := Nat.prime_eq_prime_of_dvd_pow hq prime_106753 hd
          subst q
          change (5 : ZMod 2391694213)^22404 ≠ 1
          reduce_mod_char
          decide

theorem prime_2414407829 : Nat.Prime 2414407829 := by
  apply lucas_primality 2414407829 (2 : ZMod 2414407829)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2414407829 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((101 : ℕ)^1 * ((919 : ℕ)^1 * ((929 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2414407829)^1207203914 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 2414407829)^344915404 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
          subst q
          change (2 : ZMod 2414407829)^23905028 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 919 := Nat.prime_eq_prime_of_dvd_pow hq prime_919 hd
            subst q
            change (2 : ZMod 2414407829)^2627212 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 929 := Nat.prime_eq_prime_of_dvd_pow hq prime_929 hd
            subst q
            change (2 : ZMod 2414407829)^2598932 ≠ 1
            reduce_mod_char
            decide

theorem prime_2450493391 : Nat.Prime 2450493391 := by
  apply lucas_primality 2450493391 (3 : ZMod 2450493391)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2450493391 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((4804889 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2450493391)^1225246695 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 2450493391)^816831130 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 2450493391)^490098678 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (3 : ZMod 2450493391)^144146670 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 4804889 := Nat.prime_eq_prime_of_dvd_pow hq prime_4804889 hd
            subst q
            change (3 : ZMod 2450493391)^510 ≠ 1
            reduce_mod_char
            decide

theorem prime_2459433737 : Nat.Prime 2459433737 := by
  apply lucas_primality 2459433737 (3 : ZMod 2459433737)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2459433737 - 1 = (2 : ℕ)^3 * ((1109 : ℕ)^1 * ((277213 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2459433737)^1229716868 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1109 := Nat.prime_eq_prime_of_dvd_pow hq prime_1109 hd
        subst q
        change (3 : ZMod 2459433737)^2217704 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 277213 := Nat.prime_eq_prime_of_dvd_pow hq prime_277213 hd
        subst q
        change (3 : ZMod 2459433737)^8872 ≠ 1
        reduce_mod_char
        decide

theorem prime_2462081249 : Nat.Prime 2462081249 := by
  apply lucas_primality 2462081249 (3 : ZMod 2462081249)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2462081249 - 1 = (2 : ℕ)^5 * ((11 : ℕ)^1 * ((6994549 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2462081249)^1231040624 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 2462081249)^223825568 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 6994549 := Nat.prime_eq_prime_of_dvd_pow hq prime_6994549 hd
        subst q
        change (3 : ZMod 2462081249)^352 ≠ 1
        reduce_mod_char
        decide

theorem prime_2477484673 : Nat.Prime 2477484673 := by
  apply lucas_primality 2477484673 (10 : ZMod 2477484673)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2477484673 - 1 = (2 : ℕ)^7 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((496291 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 2477484673)^1238742336 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 2477484673)^825828224 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (10 : ZMod 2477484673)^190575744 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 496291 := Nat.prime_eq_prime_of_dvd_pow hq prime_496291 hd
          subst q
          change (10 : ZMod 2477484673)^4992 ≠ 1
          reduce_mod_char
          decide

theorem prime_2523333941 : Nat.Prime 2523333941 := by
  apply lucas_primality 2523333941 (2 : ZMod 2523333941)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2523333941 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((257 : ℕ)^1 * ((490921 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2523333941)^1261666970 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 2523333941)^504666788 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 257 := Nat.prime_eq_prime_of_dvd_pow hq prime_257 hd
          subst q
          change (2 : ZMod 2523333941)^9818420 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 490921 := Nat.prime_eq_prime_of_dvd_pow hq prime_490921 hd
          subst q
          change (2 : ZMod 2523333941)^5140 ≠ 1
          reduce_mod_char
          decide

theorem prime_2536568681 : Nat.Prime 2536568681 := by
  apply lucas_primality 2536568681 (3 : ZMod 2536568681)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2536568681 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((63414217 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2536568681)^1268284340 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 2536568681)^507313736 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 63414217 := Nat.prime_eq_prime_of_dvd_pow hq prime_63414217 hd
        subst q
        change (3 : ZMod 2536568681)^40 ≠ 1
        reduce_mod_char
        decide

theorem prime_2565726421 : Nat.Prime 2565726421 := by
  apply lucas_primality 2565726421 (6 : ZMod 2565726421)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2565726421 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((42762107 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 2565726421)^1282863210 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 2565726421)^855242140 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 2565726421)^513145284 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 42762107 := Nat.prime_eq_prime_of_dvd_pow hq prime_42762107 hd
          subst q
          change (6 : ZMod 2565726421)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_2618564447 : Nat.Prime 2618564447 := by
  apply lucas_primality 2618564447 (5 : ZMod 2618564447)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2618564447 - 1 = (2 : ℕ)^1 * ((61 : ℕ)^2 * ((351863 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2618564447)^1309282223 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
        subst q
        change (5 : ZMod 2618564447)^42927286 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 351863 := Nat.prime_eq_prime_of_dvd_pow hq prime_351863 hd
        subst q
        change (5 : ZMod 2618564447)^7442 ≠ 1
        reduce_mod_char
        decide

theorem prime_2737256293 : Nat.Prime 2737256293 := by
  apply lucas_primality 2737256293 (2 : ZMod 2737256293)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2737256293 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((17 : ℕ)^1 * ((29 : ℕ)^1 * ((154229 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2737256293)^1368628146 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2737256293)^912418764 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 2737256293)^161015076 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (2 : ZMod 2737256293)^94388148 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 154229 := Nat.prime_eq_prime_of_dvd_pow hq prime_154229 hd
            subst q
            change (2 : ZMod 2737256293)^17748 ≠ 1
            reduce_mod_char
            decide

theorem prime_2742132413 : Nat.Prime 2742132413 := by
  apply lucas_primality 2742132413 (2 : ZMod 2742132413)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2742132413 - 1 = (2 : ℕ)^2 * ((1319 : ℕ)^1 * ((519737 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2742132413)^1371066206 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1319 := Nat.prime_eq_prime_of_dvd_pow hq prime_1319 hd
        subst q
        change (2 : ZMod 2742132413)^2078948 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 519737 := Nat.prime_eq_prime_of_dvd_pow hq prime_519737 hd
        subst q
        change (2 : ZMod 2742132413)^5276 ≠ 1
        reduce_mod_char
        decide

theorem prime_2757693203 : Nat.Prime 2757693203 := by
  apply lucas_primality 2757693203 (2 : ZMod 2757693203)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2757693203 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((125349691 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2757693203)^1378846601 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 2757693203)^250699382 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 125349691 := Nat.prime_eq_prime_of_dvd_pow hq prime_125349691 hd
        subst q
        change (2 : ZMod 2757693203)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_2792321381 : Nat.Prime 2792321381 := by
  apply lucas_primality 2792321381 (2 : ZMod 2792321381)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2792321381 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((283 : ℕ)^1 * ((619 : ℕ)^1 * ((797 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2792321381)^1396160690 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 2792321381)^558464276 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 283 := Nat.prime_eq_prime_of_dvd_pow hq prime_283 hd
          subst q
          change (2 : ZMod 2792321381)^9866860 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 619 := Nat.prime_eq_prime_of_dvd_pow hq prime_619 hd
            subst q
            change (2 : ZMod 2792321381)^4511020 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 797 := Nat.prime_eq_prime_of_dvd_pow hq prime_797 hd
            subst q
            change (2 : ZMod 2792321381)^3503540 ≠ 1
            reduce_mod_char
            decide

theorem prime_2829745133 : Nat.Prime 2829745133 := by
  apply lucas_primality 2829745133 (2 : ZMod 2829745133)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2829745133 - 1 = (2 : ℕ)^2 * ((17 : ℕ)^1 * ((41613899 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2829745133)^1414872566 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 2829745133)^166455596 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 41613899 := Nat.prime_eq_prime_of_dvd_pow hq prime_41613899 hd
        subst q
        change (2 : ZMod 2829745133)^68 ≠ 1
        reduce_mod_char
        decide

theorem prime_2847342961 : Nat.Prime 2847342961 := by
  apply lucas_primality 2847342961 (13 : ZMod 2847342961)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2847342961 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^2 * ((11 : ℕ)^2 * ((23 : ℕ)^1 * ((29 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 2847342961)^1423671480 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 2847342961)^949114320 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 2847342961)^569468592 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (13 : ZMod 2847342961)^406763280 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
              subst q
              change (13 : ZMod 2847342961)^258849360 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
                subst q
                change (13 : ZMod 2847342961)^123797520 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
                subst q
                change (13 : ZMod 2847342961)^98184240 ≠ 1
                reduce_mod_char
                decide

theorem prime_2859068657 : Nat.Prime 2859068657 := by
  apply lucas_primality 2859068657 (3 : ZMod 2859068657)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2859068657 - 1 = (2 : ℕ)^4 * ((47 : ℕ)^1 * ((3801953 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2859068657)^1429534328 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (3 : ZMod 2859068657)^60831248 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3801953 := Nat.prime_eq_prime_of_dvd_pow hq prime_3801953 hd
        subst q
        change (3 : ZMod 2859068657)^752 ≠ 1
        reduce_mod_char
        decide

theorem prime_2869253909 : Nat.Prime 2869253909 := by
  apply lucas_primality 2869253909 (2 : ZMod 2869253909)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2869253909 - 1 = (2 : ℕ)^2 * ((281 : ℕ)^1 * ((2552717 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2869253909)^1434626954 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 281 := Nat.prime_eq_prime_of_dvd_pow hq prime_281 hd
        subst q
        change (2 : ZMod 2869253909)^10210868 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2552717 := Nat.prime_eq_prime_of_dvd_pow hq prime_2552717 hd
        subst q
        change (2 : ZMod 2869253909)^1124 ≠ 1
        reduce_mod_char
        decide

theorem prime_2882609581 : Nat.Prime 2882609581 := by
  apply lucas_primality 2882609581 (6 : ZMod 2882609581)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2882609581 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((53 : ℕ)^1 * ((906481 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 2882609581)^1441304790 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 2882609581)^960869860 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 2882609581)^576521916 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
            subst q
            change (6 : ZMod 2882609581)^54388860 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 906481 := Nat.prime_eq_prime_of_dvd_pow hq prime_906481 hd
            subst q
            change (6 : ZMod 2882609581)^3180 ≠ 1
            reduce_mod_char
            decide

theorem prime_2915911001 : Nat.Prime 2915911001 := by
  apply lucas_primality 2915911001 (3 : ZMod 2915911001)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2915911001 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^3 * ((19 : ℕ)^1 * ((153469 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2915911001)^1457955500 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 2915911001)^583182200 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (3 : ZMod 2915911001)^153469000 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 153469 := Nat.prime_eq_prime_of_dvd_pow hq prime_153469 hd
          subst q
          change (3 : ZMod 2915911001)^19000 ≠ 1
          reduce_mod_char
          decide

theorem prime_2973706301 : Nat.Prime 2973706301 := by
  apply lucas_primality 2973706301 (2 : ZMod 2973706301)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2973706301 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((17 : ℕ)^1 * ((1749239 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2973706301)^1486853150 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 2973706301)^594741260 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 2973706301)^174923900 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1749239 := Nat.prime_eq_prime_of_dvd_pow hq prime_1749239 hd
          subst q
          change (2 : ZMod 2973706301)^1700 ≠ 1
          reduce_mod_char
          decide

theorem prime_2998576733 : Nat.Prime 2998576733 := by
  apply lucas_primality 2998576733 (2 : ZMod 2998576733)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2998576733 - 1 = (2 : ℕ)^2 * ((19 : ℕ)^1 * ((39454957 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2998576733)^1499288366 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 2998576733)^157819828 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 39454957 := Nat.prime_eq_prime_of_dvd_pow hq prime_39454957 hd
        subst q
        change (2 : ZMod 2998576733)^76 ≠ 1
        reduce_mod_char
        decide

theorem prime_3005427967 : Nat.Prime 3005427967 := by
  apply lucas_primality 3005427967 (5 : ZMod 3005427967)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3005427967 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((500904661 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3005427967)^1502713983 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 3005427967)^1001809322 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 500904661 := Nat.prime_eq_prime_of_dvd_pow hq prime_500904661 hd
        subst q
        change (5 : ZMod 3005427967)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_3010936387 : Nat.Prime 3010936387 := by
  apply lucas_primality 3010936387 (2 : ZMod 3010936387)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3010936387 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((83 : ℕ)^1 * ((563 : ℕ)^1 * ((10739 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3010936387)^1505468193 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3010936387)^1003645462 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
          subst q
          change (2 : ZMod 3010936387)^36276342 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 563 := Nat.prime_eq_prime_of_dvd_pow hq prime_563 hd
            subst q
            change (2 : ZMod 3010936387)^5348022 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 10739 := Nat.prime_eq_prime_of_dvd_pow hq prime_10739 hd
            subst q
            change (2 : ZMod 3010936387)^280374 ≠ 1
            reduce_mod_char
            decide

theorem prime_3051604739 : Nat.Prime 3051604739 := by
  apply lucas_primality 3051604739 (6 : ZMod 3051604739)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3051604739 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((433 : ℕ)^1 * ((38723 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 3051604739)^1525802369 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (6 : ZMod 3051604739)^435943534 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (6 : ZMod 3051604739)^234738826 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 433 := Nat.prime_eq_prime_of_dvd_pow hq prime_433 hd
            subst q
            change (6 : ZMod 3051604739)^7047586 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 38723 := Nat.prime_eq_prime_of_dvd_pow hq prime_38723 hd
            subst q
            change (6 : ZMod 3051604739)^78806 ≠ 1
            reduce_mod_char
            decide

theorem prime_3053510399 : Nat.Prime 3053510399 := by
  apply lucas_primality 3053510399 (7 : ZMod 3053510399)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3053510399 - 1 = (2 : ℕ)^1 * ((29 : ℕ)^1 * ((1423 : ℕ)^1 * ((36997 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 3053510399)^1526755199 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (7 : ZMod 3053510399)^105293462 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1423 := Nat.prime_eq_prime_of_dvd_pow hq prime_1423 hd
          subst q
          change (7 : ZMod 3053510399)^2145826 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 36997 := Nat.prime_eq_prime_of_dvd_pow hq prime_36997 hd
          subst q
          change (7 : ZMod 3053510399)^82534 ≠ 1
          reduce_mod_char
          decide

theorem prime_3068572387 : Nat.Prime 3068572387 := by
  apply lucas_primality 3068572387 (3 : ZMod 3068572387)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3068572387 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((31 : ℕ)^1 * ((88223 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3068572387)^1534286193 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3068572387)^1022857462 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 3068572387)^278961126 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (3 : ZMod 3068572387)^180504258 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
              subst q
              change (3 : ZMod 3068572387)^98986206 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 88223 := Nat.prime_eq_prime_of_dvd_pow hq prime_88223 hd
              subst q
              change (3 : ZMod 3068572387)^34782 ≠ 1
              reduce_mod_char
              decide

theorem prime_3077182093 : Nat.Prime 3077182093 := by
  apply lucas_primality 3077182093 (5 : ZMod 3077182093)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3077182093 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((256431841 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3077182093)^1538591046 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 3077182093)^1025727364 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 256431841 := Nat.prime_eq_prime_of_dvd_pow hq prime_256431841 hd
        subst q
        change (5 : ZMod 3077182093)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_3093421411 : Nat.Prime 3093421411 := by
  apply lucas_primality 3093421411 (10 : ZMod 3093421411)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3093421411 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((4397 : ℕ)^1 * ((7817 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 3093421411)^1546710705 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 3093421411)^1031140470 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 3093421411)^618684282 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 4397 := Nat.prime_eq_prime_of_dvd_pow hq prime_4397 hd
            subst q
            change (10 : ZMod 3093421411)^703530 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 7817 := Nat.prime_eq_prime_of_dvd_pow hq prime_7817 hd
            subst q
            change (10 : ZMod 3093421411)^395730 ≠ 1
            reduce_mod_char
            decide

theorem prime_3187877909 : Nat.Prime 3187877909 := by
  apply lucas_primality 3187877909 (2 : ZMod 3187877909)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3187877909 - 1 = (2 : ℕ)^2 * ((796969477 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3187877909)^1593938954 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 796969477 := Nat.prime_eq_prime_of_dvd_pow hq prime_796969477 hd
      subst q
      change (2 : ZMod 3187877909)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_3262166627 : Nat.Prime 3262166627 := by
  apply lucas_primality 3262166627 (2 : ZMod 3262166627)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3262166627 - 1 = (2 : ℕ)^1 * ((1631083313 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3262166627)^1631083313 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1631083313 := Nat.prime_eq_prime_of_dvd_pow hq prime_1631083313 hd
      subst q
      change (2 : ZMod 3262166627)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_3371335973 : Nat.Prime 3371335973 := by
  apply lucas_primality 3371335973 (2 : ZMod 3371335973)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3371335973 - 1 = (2 : ℕ)^2 * ((359 : ℕ)^1 * ((2347727 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3371335973)^1685667986 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 359 := Nat.prime_eq_prime_of_dvd_pow hq prime_359 hd
        subst q
        change (2 : ZMod 3371335973)^9390908 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2347727 := Nat.prime_eq_prime_of_dvd_pow hq prime_2347727 hd
        subst q
        change (2 : ZMod 3371335973)^1436 ≠ 1
        reduce_mod_char
        decide

theorem prime_3375551099 : Nat.Prime 3375551099 := by
  apply lucas_primality 3375551099 (2 : ZMod 3375551099)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3375551099 - 1 = (2 : ℕ)^1 * ((73 : ℕ)^1 * ((101 : ℕ)^1 * ((228913 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3375551099)^1687775549 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
        subst q
        change (2 : ZMod 3375551099)^46240426 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
          subst q
          change (2 : ZMod 3375551099)^33421298 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 228913 := Nat.prime_eq_prime_of_dvd_pow hq prime_228913 hd
          subst q
          change (2 : ZMod 3375551099)^14746 ≠ 1
          reduce_mod_char
          decide

theorem prime_3518743763 : Nat.Prime 3518743763 := by
  apply lucas_primality 3518743763 (2 : ZMod 3518743763)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3518743763 - 1 = (2 : ℕ)^1 * ((761 : ℕ)^1 * ((2311921 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3518743763)^1759371881 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 761 := Nat.prime_eq_prime_of_dvd_pow hq prime_761 hd
        subst q
        change (2 : ZMod 3518743763)^4623842 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2311921 := Nat.prime_eq_prime_of_dvd_pow hq prime_2311921 hd
        subst q
        change (2 : ZMod 3518743763)^1522 ≠ 1
        reduce_mod_char
        decide

theorem prime_3653546161 : Nat.Prime 3653546161 := by
  apply lucas_primality 3653546161 (21 : ZMod 3653546161)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3653546161 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((127 : ℕ)^1 * ((641 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (21 : ZMod 3653546161)^1826773080 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (21 : ZMod 3653546161)^1217848720 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (21 : ZMod 3653546161)^730709232 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (21 : ZMod 3653546161)^332140560 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
              subst q
              change (21 : ZMod 3653546161)^214914480 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
                subst q
                change (21 : ZMod 3653546161)^28768080 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 641 := Nat.prime_eq_prime_of_dvd_pow hq prime_641 hd
                subst q
                change (21 : ZMod 3653546161)^5699760 ≠ 1
                reduce_mod_char
                decide

theorem prime_3683143267 : Nat.Prime 3683143267 := by
  apply lucas_primality 3683143267 (2 : ZMod 3683143267)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3683143267 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((55805201 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3683143267)^1841571633 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3683143267)^1227714422 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 3683143267)^334831206 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 55805201 := Nat.prime_eq_prime_of_dvd_pow hq prime_55805201 hd
          subst q
          change (2 : ZMod 3683143267)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_3740080423 : Nat.Prime 3740080423 := by
  apply lucas_primality 3740080423 (3 : ZMod 3740080423)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3740080423 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((19 : ℕ)^1 * ((2523671 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3740080423)^1870040211 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3740080423)^1246693474 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 3740080423)^287698494 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (3 : ZMod 3740080423)^196846338 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2523671 := Nat.prime_eq_prime_of_dvd_pow hq prime_2523671 hd
            subst q
            change (3 : ZMod 3740080423)^1482 ≠ 1
            reduce_mod_char
            decide

theorem prime_3774645071 : Nat.Prime 3774645071 := by
  apply lucas_primality 3774645071 (13 : ZMod 3774645071)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3774645071 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((19 : ℕ)^1 * ((2838079 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 3774645071)^1887322535 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (13 : ZMod 3774645071)^754929014 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (13 : ZMod 3774645071)^539235010 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (13 : ZMod 3774645071)^198665530 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2838079 := Nat.prime_eq_prime_of_dvd_pow hq prime_2838079 hd
            subst q
            change (13 : ZMod 3774645071)^1330 ≠ 1
            reduce_mod_char
            decide

theorem prime_3783915103 : Nat.Prime 3783915103 := by
  apply lucas_primality 3783915103 (5 : ZMod 3783915103)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3783915103 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((57332047 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3783915103)^1891957551 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 3783915103)^1261305034 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 3783915103)^343992282 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 57332047 := Nat.prime_eq_prime_of_dvd_pow hq prime_57332047 hd
          subst q
          change (5 : ZMod 3783915103)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_3795868607 : Nat.Prime 3795868607 := by
  apply lucas_primality 3795868607 (5 : ZMod 3795868607)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3795868607 - 1 = (2 : ℕ)^1 * ((5419 : ℕ)^1 * ((350237 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3795868607)^1897934303 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5419 := Nat.prime_eq_prime_of_dvd_pow hq prime_5419 hd
        subst q
        change (5 : ZMod 3795868607)^700474 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 350237 := Nat.prime_eq_prime_of_dvd_pow hq prime_350237 hd
        subst q
        change (5 : ZMod 3795868607)^10838 ≠ 1
        reduce_mod_char
        decide

theorem prime_3829100729 : Nat.Prime 3829100729 := by
  apply lucas_primality 3829100729 (3 : ZMod 3829100729)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3829100729 - 1 = (2 : ℕ)^3 * ((478637591 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3829100729)^1914550364 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 478637591 := Nat.prime_eq_prime_of_dvd_pow hq prime_478637591 hd
      subst q
      change (3 : ZMod 3829100729)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_3924946457 : Nat.Prime 3924946457 := by
  apply lucas_primality 3924946457 (3 : ZMod 3924946457)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3924946457 - 1 = (2 : ℕ)^3 * ((31 : ℕ)^1 * ((71 : ℕ)^1 * ((101 : ℕ)^1 * ((2207 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3924946457)^1962473228 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (3 : ZMod 3924946457)^126611176 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
          subst q
          change (3 : ZMod 3924946457)^55280936 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
            subst q
            change (3 : ZMod 3924946457)^38860856 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2207 := Nat.prime_eq_prime_of_dvd_pow hq prime_2207 hd
            subst q
            change (3 : ZMod 3924946457)^1778408 ≠ 1
            reduce_mod_char
            decide

theorem prime_3941522017 : Nat.Prime 3941522017 := by
  apply lucas_primality 3941522017 (5 : ZMod 3941522017)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3941522017 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((41057521 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3941522017)^1970761008 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 3941522017)^1313840672 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 41057521 := Nat.prime_eq_prime_of_dvd_pow hq prime_41057521 hd
        subst q
        change (5 : ZMod 3941522017)^96 ≠ 1
        reduce_mod_char
        decide

theorem prime_3954234353 : Nat.Prime 3954234353 := by
  apply lucas_primality 3954234353 (3 : ZMod 3954234353)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3954234353 - 1 = (2 : ℕ)^4 * ((247139647 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3954234353)^1977117176 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 247139647 := Nat.prime_eq_prime_of_dvd_pow hq prime_247139647 hd
      subst q
      change (3 : ZMod 3954234353)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_3976863589 : Nat.Prime 3976863589 := by
  apply lucas_primality 3976863589 (2 : ZMod 3976863589)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3976863589 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((36822811 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3976863589)^1988431794 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3976863589)^1325621196 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 36822811 := Nat.prime_eq_prime_of_dvd_pow hq prime_36822811 hd
        subst q
        change (2 : ZMod 3976863589)^108 ≠ 1
        reduce_mod_char
        decide

theorem prime_4058412187 : Nat.Prime 4058412187 := by
  apply lucas_primality 4058412187 (2 : ZMod 4058412187)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4058412187 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1733 : ℕ)^1 * ((390307 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4058412187)^2029206093 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 4058412187)^1352804062 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1733 := Nat.prime_eq_prime_of_dvd_pow hq prime_1733 hd
          subst q
          change (2 : ZMod 4058412187)^2341842 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 390307 := Nat.prime_eq_prime_of_dvd_pow hq prime_390307 hd
          subst q
          change (2 : ZMod 4058412187)^10398 ≠ 1
          reduce_mod_char
          decide

theorem prime_4096000019 : Nat.Prime 4096000019 := by
  apply lucas_primality 4096000019 (6 : ZMod 4096000019)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4096000019 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((107 : ℕ)^1 * ((929 : ℕ)^1 * ((1873 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 4096000019)^2048000009 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (6 : ZMod 4096000019)^372363638 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
          subst q
          change (6 : ZMod 4096000019)^38280374 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 929 := Nat.prime_eq_prime_of_dvd_pow hq prime_929 hd
            subst q
            change (6 : ZMod 4096000019)^4409042 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1873 := Nat.prime_eq_prime_of_dvd_pow hq prime_1873 hd
            subst q
            change (6 : ZMod 4096000019)^2186866 ≠ 1
            reduce_mod_char
            decide

theorem prime_4127986259 : Nat.Prime 4127986259 := by
  apply lucas_primality 4127986259 (2 : ZMod 4127986259)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4127986259 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((347 : ℕ)^1 * ((571 : ℕ)^1 * ((947 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4127986259)^2063993129 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 4127986259)^375271478 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 347 := Nat.prime_eq_prime_of_dvd_pow hq prime_347 hd
          subst q
          change (2 : ZMod 4127986259)^11896214 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 571 := Nat.prime_eq_prime_of_dvd_pow hq prime_571 hd
            subst q
            change (2 : ZMod 4127986259)^7229398 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 947 := Nat.prime_eq_prime_of_dvd_pow hq prime_947 hd
            subst q
            change (2 : ZMod 4127986259)^4359014 ≠ 1
            reduce_mod_char
            decide

theorem prime_4186424941 : Nat.Prime 4186424941 := by
  apply lucas_primality 4186424941 (2 : ZMod 4186424941)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4186424941 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((37 : ℕ)^1 * ((97 : ℕ)^1 * ((19441 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4186424941)^2093212470 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 4186424941)^1395474980 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 4186424941)^837284988 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
            subst q
            change (2 : ZMod 4186424941)^113146620 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
              subst q
              change (2 : ZMod 4186424941)^43159020 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 19441 := Nat.prime_eq_prime_of_dvd_pow hq prime_19441 hd
              subst q
              change (2 : ZMod 4186424941)^215340 ≠ 1
              reduce_mod_char
              decide

theorem prime_4265141807 : Nat.Prime 4265141807 := by
  apply lucas_primality 4265141807 (5 : ZMod 4265141807)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4265141807 - 1 = (2 : ℕ)^1 * ((47 : ℕ)^1 * ((45373849 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 4265141807)^2132570903 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (5 : ZMod 4265141807)^90747698 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 45373849 := Nat.prime_eq_prime_of_dvd_pow hq prime_45373849 hd
        subst q
        change (5 : ZMod 4265141807)^94 ≠ 1
        reduce_mod_char
        decide

theorem prime_4425337613 : Nat.Prime 4425337613 := by
  apply lucas_primality 4425337613 (2 : ZMod 4425337613)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4425337613 - 1 = (2 : ℕ)^2 * ((22943 : ℕ)^1 * ((48221 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4425337613)^2212668806 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 22943 := Nat.prime_eq_prime_of_dvd_pow hq prime_22943 hd
        subst q
        change (2 : ZMod 4425337613)^192884 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 48221 := Nat.prime_eq_prime_of_dvd_pow hq prime_48221 hd
        subst q
        change (2 : ZMod 4425337613)^91772 ≠ 1
        reduce_mod_char
        decide

theorem prime_4468694089 : Nat.Prime 4468694089 := by
  apply lucas_primality 4468694089 (11 : ZMod 4468694089)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4468694089 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((186195587 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 4468694089)^2234347044 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 4468694089)^1489564696 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 186195587 := Nat.prime_eq_prime_of_dvd_pow hq prime_186195587 hd
        subst q
        change (11 : ZMod 4468694089)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_4493054977 : Nat.Prime 4493054977 := by
  apply lucas_primality 4493054977 (7 : ZMod 4493054977)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4493054977 - 1 = (2 : ℕ)^10 * ((3 : ℕ)^1 * ((107 : ℕ)^1 * ((13669 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 4493054977)^2246527488 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 4493054977)^1497684992 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
          subst q
          change (7 : ZMod 4493054977)^41991168 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13669 := Nat.prime_eq_prime_of_dvd_pow hq prime_13669 hd
          subst q
          change (7 : ZMod 4493054977)^328704 ≠ 1
          reduce_mod_char
          decide

theorem prime_4506039767 : Nat.Prime 4506039767 := by
  apply lucas_primality 4506039767 (5 : ZMod 4506039767)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4506039767 - 1 = (2 : ℕ)^1 * ((283 : ℕ)^1 * ((557 : ℕ)^1 * ((14293 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 4506039767)^2253019883 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 283 := Nat.prime_eq_prime_of_dvd_pow hq prime_283 hd
        subst q
        change (5 : ZMod 4506039767)^15922402 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 557 := Nat.prime_eq_prime_of_dvd_pow hq prime_557 hd
          subst q
          change (5 : ZMod 4506039767)^8089838 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 14293 := Nat.prime_eq_prime_of_dvd_pow hq prime_14293 hd
          subst q
          change (5 : ZMod 4506039767)^315262 ≠ 1
          reduce_mod_char
          decide

theorem prime_4652230307 : Nat.Prime 4652230307 := by
  apply lucas_primality 4652230307 (2 : ZMod 4652230307)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4652230307 - 1 = (2 : ℕ)^1 * ((379 : ℕ)^1 * ((947 : ℕ)^1 * ((6481 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4652230307)^2326115153 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 379 := Nat.prime_eq_prime_of_dvd_pow hq prime_379 hd
        subst q
        change (2 : ZMod 4652230307)^12275014 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 947 := Nat.prime_eq_prime_of_dvd_pow hq prime_947 hd
          subst q
          change (2 : ZMod 4652230307)^4912598 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 6481 := Nat.prime_eq_prime_of_dvd_pow hq prime_6481 hd
          subst q
          change (2 : ZMod 4652230307)^717826 ≠ 1
          reduce_mod_char
          decide

theorem prime_4662920573 : Nat.Prime 4662920573 := by
  apply lucas_primality 4662920573 (2 : ZMod 4662920573)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4662920573 - 1 = (2 : ℕ)^2 * ((47 : ℕ)^1 * ((24802769 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4662920573)^2331460286 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (2 : ZMod 4662920573)^99211076 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 24802769 := Nat.prime_eq_prime_of_dvd_pow hq prime_24802769 hd
        subst q
        change (2 : ZMod 4662920573)^188 ≠ 1
        reduce_mod_char
        decide

theorem prime_4750104287 : Nat.Prime 4750104287 := by
  apply lucas_primality 4750104287 (5 : ZMod 4750104287)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4750104287 - 1 = (2 : ℕ)^1 * ((107 : ℕ)^1 * ((349 : ℕ)^1 * ((63601 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 4750104287)^2375052143 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
        subst q
        change (5 : ZMod 4750104287)^44393498 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 349 := Nat.prime_eq_prime_of_dvd_pow hq prime_349 hd
          subst q
          change (5 : ZMod 4750104287)^13610614 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 63601 := Nat.prime_eq_prime_of_dvd_pow hq prime_63601 hd
          subst q
          change (5 : ZMod 4750104287)^74686 ≠ 1
          reduce_mod_char
          decide

theorem prime_4777586239 : Nat.Prime 4777586239 := by
  apply lucas_primality 4777586239 (3 : ZMod 4777586239)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4777586239 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((229 : ℕ)^1 * ((3477137 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4777586239)^2388793119 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 4777586239)^1592528746 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 229 := Nat.prime_eq_prime_of_dvd_pow hq prime_229 hd
          subst q
          change (3 : ZMod 4777586239)^20862822 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3477137 := Nat.prime_eq_prime_of_dvd_pow hq prime_3477137 hd
          subst q
          change (3 : ZMod 4777586239)^1374 ≠ 1
          reduce_mod_char
          decide

theorem prime_4815870253 : Nat.Prime 4815870253 := by
  apply lucas_primality 4815870253 (2 : ZMod 4815870253)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4815870253 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((467 : ℕ)^1 * ((859363 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4815870253)^2407935126 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 4815870253)^1605290084 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 467 := Nat.prime_eq_prime_of_dvd_pow hq prime_467 hd
          subst q
          change (2 : ZMod 4815870253)^10312356 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 859363 := Nat.prime_eq_prime_of_dvd_pow hq prime_859363 hd
          subst q
          change (2 : ZMod 4815870253)^5604 ≠ 1
          reduce_mod_char
          decide

theorem prime_4873296397 : Nat.Prime 4873296397 := by
  apply lucas_primality 4873296397 (2 : ZMod 4873296397)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4873296397 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((19 : ℕ)^2 * ((23 : ℕ)^1 * ((59 : ℕ)^1 * ((829 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4873296397)^2436648198 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 4873296397)^1624432132 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 4873296397)^256489284 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (2 : ZMod 4873296397)^211882452 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
              subst q
              change (2 : ZMod 4873296397)^82598244 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 829 := Nat.prime_eq_prime_of_dvd_pow hq prime_829 hd
              subst q
              change (2 : ZMod 4873296397)^5878524 ≠ 1
              reduce_mod_char
              decide

theorem prime_4886092427 : Nat.Prime 4886092427 := by
  apply lucas_primality 4886092427 (2 : ZMod 4886092427)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4886092427 - 1 = (2 : ℕ)^1 * ((41 : ℕ)^1 * ((347 : ℕ)^1 * ((171719 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4886092427)^2443046213 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
        subst q
        change (2 : ZMod 4886092427)^119172986 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 347 := Nat.prime_eq_prime_of_dvd_pow hq prime_347 hd
          subst q
          change (2 : ZMod 4886092427)^14080958 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 171719 := Nat.prime_eq_prime_of_dvd_pow hq prime_171719 hd
          subst q
          change (2 : ZMod 4886092427)^28454 ≠ 1
          reduce_mod_char
          decide

theorem prime_4893656953 : Nat.Prime 4893656953 := by
  apply lucas_primality 4893656953 (5 : ZMod 4893656953)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4893656953 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((67 : ℕ)^1 * ((643 : ℕ)^1 * ((4733 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 4893656953)^2446828476 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 4893656953)^1631218984 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (5 : ZMod 4893656953)^73039656 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 643 := Nat.prime_eq_prime_of_dvd_pow hq prime_643 hd
            subst q
            change (5 : ZMod 4893656953)^7610664 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 4733 := Nat.prime_eq_prime_of_dvd_pow hq prime_4733 hd
            subst q
            change (5 : ZMod 4893656953)^1033944 ≠ 1
            reduce_mod_char
            decide

end LegendreK6.Pratt
