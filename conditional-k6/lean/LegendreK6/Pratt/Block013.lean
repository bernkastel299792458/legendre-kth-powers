import LegendreK6.Pratt.Block012

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LegendreK6.Pratt

theorem prime_5104123 : Nat.Prime 5104123 := by
  apply lucas_primality 5104123 (3 : ZMod 5104123)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5104123 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((44773 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 5104123)^2552061 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 5104123)^1701374 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (3 : ZMod 5104123)^268638 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 44773 := Nat.prime_eq_prime_of_dvd_pow hq prime_44773 hd
          subst q
          change (3 : ZMod 5104123)^114 ≠ 1
          reduce_mod_char
          decide

theorem prime_5109857 : Nat.Prime 5109857 := by
  apply lucas_primality 5109857 (3 : ZMod 5109857)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5109857 - 1 = (2 : ℕ)^5 * ((159683 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 5109857)^2554928 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 159683 := Nat.prime_eq_prime_of_dvd_pow hq prime_159683 hd
      subst q
      change (3 : ZMod 5109857)^32 ≠ 1
      reduce_mod_char
      decide

theorem prime_5110739 : Nat.Prime 5110739 := by
  apply lucas_primality 5110739 (2 : ZMod 5110739)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5110739 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((111103 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5110739)^2555369 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (2 : ZMod 5110739)^222206 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 111103 := Nat.prime_eq_prime_of_dvd_pow hq prime_111103 hd
        subst q
        change (2 : ZMod 5110739)^46 ≠ 1
        reduce_mod_char
        decide

theorem prime_5111923 : Nat.Prime 5111923 := by
  apply lucas_primality 5111923 (2 : ZMod 5111923)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5111923 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((61 : ℕ)^1 * ((13967 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5111923)^2555961 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 5111923)^1703974 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (2 : ZMod 5111923)^83802 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13967 := Nat.prime_eq_prime_of_dvd_pow hq prime_13967 hd
          subst q
          change (2 : ZMod 5111923)^366 ≠ 1
          reduce_mod_char
          decide

theorem prime_5199049 : Nat.Prime 5199049 := by
  apply lucas_primality 5199049 (17 : ZMod 5199049)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5199049 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((163 : ℕ)^1 * ((443 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 5199049)^2599524 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 5199049)^1733016 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
          subst q
          change (17 : ZMod 5199049)^31896 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 443 := Nat.prime_eq_prime_of_dvd_pow hq prime_443 hd
          subst q
          change (17 : ZMod 5199049)^11736 ≠ 1
          reduce_mod_char
          decide

theorem prime_5212843 : Nat.Prime 5212843 := by
  apply lucas_primality 5212843 (2 : ZMod 5212843)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5212843 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((127 : ℕ)^1 * ((6841 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5212843)^2606421 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 5212843)^1737614 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
          subst q
          change (2 : ZMod 5212843)^41046 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 6841 := Nat.prime_eq_prime_of_dvd_pow hq prime_6841 hd
          subst q
          change (2 : ZMod 5212843)^762 ≠ 1
          reduce_mod_char
          decide

theorem prime_5231389 : Nat.Prime 5231389 := by
  apply lucas_primality 5231389 (2 : ZMod 5231389)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5231389 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((435949 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5231389)^2615694 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 5231389)^1743796 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 435949 := Nat.prime_eq_prime_of_dvd_pow hq prime_435949 hd
        subst q
        change (2 : ZMod 5231389)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_5270981 : Nat.Prime 5270981 := by
  apply lucas_primality 5270981 (12 : ZMod 5270981)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5270981 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((19 : ℕ)^1 * ((97 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (12 : ZMod 5270981)^2635490 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (12 : ZMod 5270981)^1054196 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (12 : ZMod 5270981)^479180 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (12 : ZMod 5270981)^405460 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
              subst q
              change (12 : ZMod 5270981)^277420 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
              subst q
              change (12 : ZMod 5270981)^54340 ≠ 1
              reduce_mod_char
              decide

theorem prime_5279353 : Nat.Prime 5279353 := by
  apply lucas_primality 5279353 (5 : ZMod 5279353)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5279353 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((16921 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 5279353)^2639676 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 5279353)^1759784 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (5 : ZMod 5279353)^406104 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 16921 := Nat.prime_eq_prime_of_dvd_pow hq prime_16921 hd
          subst q
          change (5 : ZMod 5279353)^312 ≠ 1
          reduce_mod_char
          decide

theorem prime_5339723 : Nat.Prime 5339723 := by
  apply lucas_primality 5339723 (2 : ZMod 5339723)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5339723 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((83 : ℕ)^1 * ((1693 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5339723)^2669861 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 5339723)^281038 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
          subst q
          change (2 : ZMod 5339723)^64334 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1693 := Nat.prime_eq_prime_of_dvd_pow hq prime_1693 hd
          subst q
          change (2 : ZMod 5339723)^3154 ≠ 1
          reduce_mod_char
          decide

theorem prime_5345203 : Nat.Prime 5345203 := by
  apply lucas_primality 5345203 (5 : ZMod 5345203)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5345203 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((890867 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 5345203)^2672601 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 5345203)^1781734 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 890867 := Nat.prime_eq_prime_of_dvd_pow hq prime_890867 hd
        subst q
        change (5 : ZMod 5345203)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_5379611 : Nat.Prime 5379611 := by
  apply lucas_primality 5379611 (6 : ZMod 5379611)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5379611 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((41 : ℕ)^1 * ((13121 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 5379611)^2689805 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 5379611)^1075922 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (6 : ZMod 5379611)^131210 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13121 := Nat.prime_eq_prime_of_dvd_pow hq prime_13121 hd
          subst q
          change (6 : ZMod 5379611)^410 ≠ 1
          reduce_mod_char
          decide

theorem prime_5385997 : Nat.Prime 5385997 := by
  apply lucas_primality 5385997 (5 : ZMod 5385997)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5385997 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((29 : ℕ)^1 * ((67 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 5385997)^2692998 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 5385997)^1795332 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 5385997)^769428 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (5 : ZMod 5385997)^489636 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
              subst q
              change (5 : ZMod 5385997)^185724 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
              subst q
              change (5 : ZMod 5385997)^80388 ≠ 1
              reduce_mod_char
              decide

theorem prime_5408569 : Nat.Prime 5408569 := by
  apply lucas_primality 5408569 (14 : ZMod 5408569)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5408569 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((6829 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 5408569)^2704284 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 5408569)^1802856 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (14 : ZMod 5408569)^491688 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 6829 := Nat.prime_eq_prime_of_dvd_pow hq prime_6829 hd
          subst q
          change (14 : ZMod 5408569)^792 ≠ 1
          reduce_mod_char
          decide

theorem prime_5411821 : Nat.Prime 5411821 := by
  apply lucas_primality 5411821 (2 : ZMod 5411821)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5411821 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((90197 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5411821)^2705910 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 5411821)^1803940 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 5411821)^1082364 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 90197 := Nat.prime_eq_prime_of_dvd_pow hq prime_90197 hd
          subst q
          change (2 : ZMod 5411821)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_5432971 : Nat.Prime 5432971 := by
  apply lucas_primality 5432971 (10 : ZMod 5432971)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5432971 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((97 : ℕ)^1 * ((1867 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 5432971)^2716485 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 5432971)^1810990 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 5432971)^1086594 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
            subst q
            change (10 : ZMod 5432971)^56010 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1867 := Nat.prime_eq_prime_of_dvd_pow hq prime_1867 hd
            subst q
            change (10 : ZMod 5432971)^2910 ≠ 1
            reduce_mod_char
            decide

theorem prime_5476813 : Nat.Prime 5476813 := by
  apply lucas_primality 5476813 (7 : ZMod 5476813)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5476813 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((41491 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 5476813)^2738406 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 5476813)^1825604 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (7 : ZMod 5476813)^497892 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 41491 := Nat.prime_eq_prime_of_dvd_pow hq prime_41491 hd
          subst q
          change (7 : ZMod 5476813)^132 ≠ 1
          reduce_mod_char
          decide

theorem prime_5510173 : Nat.Prime 5510173 := by
  apply lucas_primality 5510173 (2 : ZMod 5510173)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5510173 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((459181 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5510173)^2755086 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 5510173)^1836724 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 459181 := Nat.prime_eq_prime_of_dvd_pow hq prime_459181 hd
        subst q
        change (2 : ZMod 5510173)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_5518397 : Nat.Prime 5518397 := by
  apply lucas_primality 5518397 (2 : ZMod 5518397)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5518397 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((106123 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5518397)^2759198 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 5518397)^424492 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 106123 := Nat.prime_eq_prime_of_dvd_pow hq prime_106123 hd
        subst q
        change (2 : ZMod 5518397)^52 ≠ 1
        reduce_mod_char
        decide

theorem prime_5535511 : Nat.Prime 5535511 := by
  apply lucas_primality 5535511 (11 : ZMod 5535511)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5535511 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((184517 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 5535511)^2767755 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 5535511)^1845170 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 5535511)^1107102 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 184517 := Nat.prime_eq_prime_of_dvd_pow hq prime_184517 hd
          subst q
          change (11 : ZMod 5535511)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_5556169 : Nat.Prime 5556169 := by
  apply lucas_primality 5556169 (7 : ZMod 5556169)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5556169 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((29 : ℕ)^1 * ((887 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 5556169)^2778084 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 5556169)^1852056 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (7 : ZMod 5556169)^191592 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 887 := Nat.prime_eq_prime_of_dvd_pow hq prime_887 hd
          subst q
          change (7 : ZMod 5556169)^6264 ≠ 1
          reduce_mod_char
          decide

theorem prime_5587811 : Nat.Prime 5587811 := by
  apply lucas_primality 5587811 (2 : ZMod 5587811)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5587811 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((558781 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5587811)^2793905 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 5587811)^1117562 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 558781 := Nat.prime_eq_prime_of_dvd_pow hq prime_558781 hd
        subst q
        change (2 : ZMod 5587811)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_5603519 : Nat.Prime 5603519 := by
  apply lucas_primality 5603519 (11 : ZMod 5603519)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5603519 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((167 : ℕ)^1 * ((883 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 5603519)^2801759 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (11 : ZMod 5603519)^294922 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
          subst q
          change (11 : ZMod 5603519)^33554 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 883 := Nat.prime_eq_prime_of_dvd_pow hq prime_883 hd
          subst q
          change (11 : ZMod 5603519)^6346 ≠ 1
          reduce_mod_char
          decide

theorem prime_5627603 : Nat.Prime 5627603 := by
  apply lucas_primality 5627603 (2 : ZMod 5627603)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5627603 - 1 = (2 : ℕ)^1 * ((71 : ℕ)^1 * ((39631 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5627603)^2813801 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
        subst q
        change (2 : ZMod 5627603)^79262 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 39631 := Nat.prime_eq_prime_of_dvd_pow hq prime_39631 hd
        subst q
        change (2 : ZMod 5627603)^142 ≠ 1
        reduce_mod_char
        decide

theorem prime_5649001 : Nat.Prime 5649001 := by
  apply lucas_primality 5649001 (26 : ZMod 5649001)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5649001 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^3 * ((7 : ℕ)^1 * ((269 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (26 : ZMod 5649001)^2824500 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (26 : ZMod 5649001)^1883000 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (26 : ZMod 5649001)^1129800 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (26 : ZMod 5649001)^807000 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
            subst q
            change (26 : ZMod 5649001)^21000 ≠ 1
            reduce_mod_char
            decide

theorem prime_5668997 : Nat.Prime 5668997 := by
  apply lucas_primality 5668997 (2 : ZMod 5668997)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5668997 - 1 = (2 : ℕ)^2 * ((617 : ℕ)^1 * ((2297 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5668997)^2834498 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 617 := Nat.prime_eq_prime_of_dvd_pow hq prime_617 hd
        subst q
        change (2 : ZMod 5668997)^9188 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2297 := Nat.prime_eq_prime_of_dvd_pow hq prime_2297 hd
        subst q
        change (2 : ZMod 5668997)^2468 ≠ 1
        reduce_mod_char
        decide

theorem prime_5669801 : Nat.Prime 5669801 := by
  apply lucas_primality 5669801 (3 : ZMod 5669801)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5669801 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^2 * ((28349 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 5669801)^2834900 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 5669801)^1133960 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 28349 := Nat.prime_eq_prime_of_dvd_pow hq prime_28349 hd
        subst q
        change (3 : ZMod 5669801)^200 ≠ 1
        reduce_mod_char
        decide

theorem prime_5754997 : Nat.Prime 5754997 := by
  apply lucas_primality 5754997 (6 : ZMod 5754997)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5754997 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((13 : ℕ)^1 * ((4099 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 5754997)^2877498 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 5754997)^1918332 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (6 : ZMod 5754997)^442692 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4099 := Nat.prime_eq_prime_of_dvd_pow hq prime_4099 hd
          subst q
          change (6 : ZMod 5754997)^1404 ≠ 1
          reduce_mod_char
          decide

theorem prime_5760961 : Nat.Prime 5760961 := by
  apply lucas_primality 5760961 (13 : ZMod 5760961)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5760961 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((353 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 5760961)^2880480 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 5760961)^1920320 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 5760961)^1152192 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (13 : ZMod 5760961)^338880 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 353 := Nat.prime_eq_prime_of_dvd_pow hq prime_353 hd
            subst q
            change (13 : ZMod 5760961)^16320 ≠ 1
            reduce_mod_char
            decide

theorem prime_5858731 : Nat.Prime 5858731 := by
  apply lucas_primality 5858731 (12 : ZMod 5858731)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5858731 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^5 * ((5 : ℕ)^1 * ((2411 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (12 : ZMod 5858731)^2929365 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (12 : ZMod 5858731)^1952910 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (12 : ZMod 5858731)^1171746 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2411 := Nat.prime_eq_prime_of_dvd_pow hq prime_2411 hd
          subst q
          change (12 : ZMod 5858731)^2430 ≠ 1
          reduce_mod_char
          decide

theorem prime_5880737 : Nat.Prime 5880737 := by
  apply lucas_primality 5880737 (3 : ZMod 5880737)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5880737 - 1 = (2 : ℕ)^5 * ((29 : ℕ)^1 * ((6337 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 5880737)^2940368 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (3 : ZMod 5880737)^202784 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 6337 := Nat.prime_eq_prime_of_dvd_pow hq prime_6337 hd
        subst q
        change (3 : ZMod 5880737)^928 ≠ 1
        reduce_mod_char
        decide

theorem prime_5925313 : Nat.Prime 5925313 := by
  apply lucas_primality 5925313 (5 : ZMod 5925313)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5925313 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^6 * ((127 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 5925313)^2962656 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 5925313)^1975104 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
        subst q
        change (5 : ZMod 5925313)^46656 ≠ 1
        reduce_mod_char
        decide

theorem prime_5987347 : Nat.Prime 5987347 := by
  apply lucas_primality 5987347 (3 : ZMod 5987347)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5987347 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((997891 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 5987347)^2993673 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 5987347)^1995782 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 997891 := Nat.prime_eq_prime_of_dvd_pow hq prime_997891 hd
        subst q
        change (3 : ZMod 5987347)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_6034393 : Nat.Prime 6034393 := by
  apply lucas_primality 6034393 (10 : ZMod 6034393)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6034393 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((307 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 6034393)^3017196 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 6034393)^2011464 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (10 : ZMod 6034393)^862056 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (10 : ZMod 6034393)^464184 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 307 := Nat.prime_eq_prime_of_dvd_pow hq prime_307 hd
            subst q
            change (10 : ZMod 6034393)^19656 ≠ 1
            reduce_mod_char
            decide

theorem prime_6054617 : Nat.Prime 6054617 := by
  apply lucas_primality 6054617 (5 : ZMod 6054617)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6054617 - 1 = (2 : ℕ)^3 * ((19 : ℕ)^1 * ((61 : ℕ)^1 * ((653 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 6054617)^3027308 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (5 : ZMod 6054617)^318664 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (5 : ZMod 6054617)^99256 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 653 := Nat.prime_eq_prime_of_dvd_pow hq prime_653 hd
          subst q
          change (5 : ZMod 6054617)^9272 ≠ 1
          reduce_mod_char
          decide

theorem prime_6088301 : Nat.Prime 6088301 := by
  apply lucas_primality 6088301 (3 : ZMod 6088301)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6088301 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((107 : ℕ)^1 * ((569 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 6088301)^3044150 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 6088301)^1217660 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
          subst q
          change (3 : ZMod 6088301)^56900 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 569 := Nat.prime_eq_prime_of_dvd_pow hq prime_569 hd
          subst q
          change (3 : ZMod 6088301)^10700 ≠ 1
          reduce_mod_char
          decide

theorem prime_6179087 : Nat.Prime 6179087 := by
  apply lucas_primality 6179087 (5 : ZMod 6179087)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6179087 - 1 = (2 : ℕ)^1 * ((719 : ℕ)^1 * ((4297 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 6179087)^3089543 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 719 := Nat.prime_eq_prime_of_dvd_pow hq prime_719 hd
        subst q
        change (5 : ZMod 6179087)^8594 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4297 := Nat.prime_eq_prime_of_dvd_pow hq prime_4297 hd
        subst q
        change (5 : ZMod 6179087)^1438 ≠ 1
        reduce_mod_char
        decide

theorem prime_6279089 : Nat.Prime 6279089 := by
  apply lucas_primality 6279089 (3 : ZMod 6279089)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6279089 - 1 = (2 : ℕ)^4 * ((392443 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 6279089)^3139544 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 392443 := Nat.prime_eq_prime_of_dvd_pow hq prime_392443 hd
      subst q
      change (3 : ZMod 6279089)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_6319679 : Nat.Prime 6319679 := by
  apply lucas_primality 6319679 (7 : ZMod 6319679)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6319679 - 1 = (2 : ℕ)^1 * ((251 : ℕ)^1 * ((12589 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 6319679)^3159839 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 251 := Nat.prime_eq_prime_of_dvd_pow hq prime_251 hd
        subst q
        change (7 : ZMod 6319679)^25178 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 12589 := Nat.prime_eq_prime_of_dvd_pow hq prime_12589 hd
        subst q
        change (7 : ZMod 6319679)^502 ≠ 1
        reduce_mod_char
        decide

theorem prime_6393773 : Nat.Prime 6393773 := by
  apply lucas_primality 6393773 (2 : ZMod 6393773)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6393773 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((20759 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6393773)^3196886 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 6393773)^913396 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 6393773)^581252 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 20759 := Nat.prime_eq_prime_of_dvd_pow hq prime_20759 hd
          subst q
          change (2 : ZMod 6393773)^308 ≠ 1
          reduce_mod_char
          decide

theorem prime_6411571 : Nat.Prime 6411571 := by
  apply lucas_primality 6411571 (10 : ZMod 6411571)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6411571 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((19429 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 6411571)^3205785 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 6411571)^2137190 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 6411571)^1282314 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (10 : ZMod 6411571)^582870 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 19429 := Nat.prime_eq_prime_of_dvd_pow hq prime_19429 hd
            subst q
            change (10 : ZMod 6411571)^330 ≠ 1
            reduce_mod_char
            decide

theorem prime_6417779 : Nat.Prime 6417779 := by
  apply lucas_primality 6417779 (2 : ZMod 6417779)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6417779 - 1 = (2 : ℕ)^1 * ((3208889 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6417779)^3208889 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3208889 := Nat.prime_eq_prime_of_dvd_pow hq prime_3208889 hd
      subst q
      change (2 : ZMod 6417779)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_6462319 : Nat.Prime 6462319 := by
  apply lucas_primality 6462319 (15 : ZMod 6462319)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6462319 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((56687 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (15 : ZMod 6462319)^3231159 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (15 : ZMod 6462319)^2154106 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (15 : ZMod 6462319)^340122 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 56687 := Nat.prime_eq_prime_of_dvd_pow hq prime_56687 hd
          subst q
          change (15 : ZMod 6462319)^114 ≠ 1
          reduce_mod_char
          decide

theorem prime_6612691 : Nat.Prime 6612691 := by
  apply lucas_primality 6612691 (3 : ZMod 6612691)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6612691 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((31489 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 6612691)^3306345 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 6612691)^2204230 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 6612691)^1322538 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (3 : ZMod 6612691)^944670 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 31489 := Nat.prime_eq_prime_of_dvd_pow hq prime_31489 hd
            subst q
            change (3 : ZMod 6612691)^210 ≠ 1
            reduce_mod_char
            decide

theorem prime_6731449 : Nat.Prime 6731449 := by
  apply lucas_primality 6731449 (11 : ZMod 6731449)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6731449 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((101 : ℕ)^1 * ((2777 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 6731449)^3365724 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 6731449)^2243816 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
          subst q
          change (11 : ZMod 6731449)^66648 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2777 := Nat.prime_eq_prime_of_dvd_pow hq prime_2777 hd
          subst q
          change (11 : ZMod 6731449)^2424 ≠ 1
          reduce_mod_char
          decide

theorem prime_6778397 : Nat.Prime 6778397 := by
  apply lucas_primality 6778397 (2 : ZMod 6778397)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6778397 - 1 = (2 : ℕ)^2 * ((1694599 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6778397)^3389198 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1694599 := Nat.prime_eq_prime_of_dvd_pow hq prime_1694599 hd
      subst q
      change (2 : ZMod 6778397)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_6792977 : Nat.Prime 6792977 := by
  apply lucas_primality 6792977 (3 : ZMod 6792977)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6792977 - 1 = (2 : ℕ)^4 * ((127 : ℕ)^1 * ((3343 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 6792977)^3396488 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
        subst q
        change (3 : ZMod 6792977)^53488 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3343 := Nat.prime_eq_prime_of_dvd_pow hq prime_3343 hd
        subst q
        change (3 : ZMod 6792977)^2032 ≠ 1
        reduce_mod_char
        decide

theorem prime_6893681 : Nat.Prime 6893681 := by
  apply lucas_primality 6893681 (3 : ZMod 6893681)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6893681 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((86171 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 6893681)^3446840 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 6893681)^1378736 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 86171 := Nat.prime_eq_prime_of_dvd_pow hq prime_86171 hd
        subst q
        change (3 : ZMod 6893681)^80 ≠ 1
        reduce_mod_char
        decide

theorem prime_6903467 : Nat.Prime 6903467 := by
  apply lucas_primality 6903467 (2 : ZMod 6903467)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6903467 - 1 = (2 : ℕ)^1 * ((127 : ℕ)^1 * ((27179 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6903467)^3451733 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
        subst q
        change (2 : ZMod 6903467)^54358 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 27179 := Nat.prime_eq_prime_of_dvd_pow hq prime_27179 hd
        subst q
        change (2 : ZMod 6903467)^254 ≠ 1
        reduce_mod_char
        decide

theorem prime_6903623 : Nat.Prime 6903623 := by
  apply lucas_primality 6903623 (5 : ZMod 6903623)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6903623 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((113 : ℕ)^1 * ((2777 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 6903623)^3451811 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 6903623)^627602 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
          subst q
          change (5 : ZMod 6903623)^61094 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2777 := Nat.prime_eq_prime_of_dvd_pow hq prime_2777 hd
          subst q
          change (5 : ZMod 6903623)^2486 ≠ 1
          reduce_mod_char
          decide

theorem prime_6922273 : Nat.Prime 6922273 := by
  apply lucas_primality 6922273 (5 : ZMod 6922273)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6922273 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((10301 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 6922273)^3461136 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 6922273)^2307424 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 6922273)^988896 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 10301 := Nat.prime_eq_prime_of_dvd_pow hq prime_10301 hd
          subst q
          change (5 : ZMod 6922273)^672 ≠ 1
          reduce_mod_char
          decide

theorem prime_6947539 : Nat.Prime 6947539 := by
  apply lucas_primality 6947539 (3 : ZMod 6947539)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6947539 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((89071 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 6947539)^3473769 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 6947539)^2315846 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 6947539)^534426 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 89071 := Nat.prime_eq_prime_of_dvd_pow hq prime_89071 hd
          subst q
          change (3 : ZMod 6947539)^78 ≠ 1
          reduce_mod_char
          decide

theorem prime_6994549 : Nat.Prime 6994549 := by
  apply lucas_primality 6994549 (6 : ZMod 6994549)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6994549 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((1039 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 6994549)^3497274 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 6994549)^2331516 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (6 : ZMod 6994549)^635868 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (6 : ZMod 6994549)^411444 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1039 := Nat.prime_eq_prime_of_dvd_pow hq prime_1039 hd
            subst q
            change (6 : ZMod 6994549)^6732 ≠ 1
            reduce_mod_char
            decide

theorem prime_7016663 : Nat.Prime 7016663 := by
  apply lucas_primality 7016663 (5 : ZMod 7016663)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7016663 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((184649 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 7016663)^3508331 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (5 : ZMod 7016663)^369298 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 184649 := Nat.prime_eq_prime_of_dvd_pow hq prime_184649 hd
        subst q
        change (5 : ZMod 7016663)^38 ≠ 1
        reduce_mod_char
        decide

theorem prime_7029089 : Nat.Prime 7029089 := by
  apply lucas_primality 7029089 (6 : ZMod 7029089)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7029089 - 1 = (2 : ℕ)^5 * ((11 : ℕ)^1 * ((19 : ℕ)^1 * ((1051 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 7029089)^3514544 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (6 : ZMod 7029089)^639008 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (6 : ZMod 7029089)^369952 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1051 := Nat.prime_eq_prime_of_dvd_pow hq prime_1051 hd
          subst q
          change (6 : ZMod 7029089)^6688 ≠ 1
          reduce_mod_char
          decide

theorem prime_7059251 : Nat.Prime 7059251 := by
  apply lucas_primality 7059251 (10 : ZMod 7059251)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7059251 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^3 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((151 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 7059251)^3529625 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (10 : ZMod 7059251)^1411850 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (10 : ZMod 7059251)^641750 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (10 : ZMod 7059251)^415250 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
            subst q
            change (10 : ZMod 7059251)^46750 ≠ 1
            reduce_mod_char
            decide

theorem prime_7113913 : Nat.Prime 7113913 := by
  apply lucas_primality 7113913 (10 : ZMod 7113913)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7113913 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((151 : ℕ)^2))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 7113913)^3556956 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 7113913)^2371304 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (10 : ZMod 7113913)^547224 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
          subst q
          change (10 : ZMod 7113913)^47112 ≠ 1
          reduce_mod_char
          decide

theorem prime_7115963 : Nat.Prime 7115963 := by
  apply lucas_primality 7115963 (5 : ZMod 7115963)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7115963 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((17 : ℕ)^1 * ((29 : ℕ)^1 * ((1031 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 7115963)^3557981 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 7115963)^1016566 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (5 : ZMod 7115963)^418586 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (5 : ZMod 7115963)^245378 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1031 := Nat.prime_eq_prime_of_dvd_pow hq prime_1031 hd
            subst q
            change (5 : ZMod 7115963)^6902 ≠ 1
            reduce_mod_char
            decide

theorem prime_7317169 : Nat.Prime 7317169 := by
  apply lucas_primality 7317169 (7 : ZMod 7317169)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7317169 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((152441 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 7317169)^3658584 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 7317169)^2439056 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 152441 := Nat.prime_eq_prime_of_dvd_pow hq prime_152441 hd
        subst q
        change (7 : ZMod 7317169)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_7379347 : Nat.Prime 7379347 := by
  apply lucas_primality 7379347 (2 : ZMod 7379347)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7379347 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((89 : ℕ)^1 * ((1063 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 7379347)^3689673 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 7379347)^2459782 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 7379347)^567642 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
            subst q
            change (2 : ZMod 7379347)^82914 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1063 := Nat.prime_eq_prime_of_dvd_pow hq prime_1063 hd
            subst q
            change (2 : ZMod 7379347)^6942 ≠ 1
            reduce_mod_char
            decide

theorem prime_7393643 : Nat.Prime 7393643 := by
  apply lucas_primality 7393643 (2 : ZMod 7393643)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7393643 - 1 = (2 : ℕ)^1 * ((3696821 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 7393643)^3696821 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3696821 := Nat.prime_eq_prime_of_dvd_pow hq prime_3696821 hd
      subst q
      change (2 : ZMod 7393643)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_7407979 : Nat.Prime 7407979 := by
  apply lucas_primality 7407979 (14 : ZMod 7407979)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7407979 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((53681 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 7407979)^3703989 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 7407979)^2469326 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (14 : ZMod 7407979)^322086 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 53681 := Nat.prime_eq_prime_of_dvd_pow hq prime_53681 hd
          subst q
          change (14 : ZMod 7407979)^138 ≠ 1
          reduce_mod_char
          decide

theorem prime_7469887 : Nat.Prime 7469887 := by
  apply lucas_primality 7469887 (3 : ZMod 7469887)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7469887 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((127 : ℕ)^1 * ((9803 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 7469887)^3734943 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 7469887)^2489962 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
          subst q
          change (3 : ZMod 7469887)^58818 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 9803 := Nat.prime_eq_prime_of_dvd_pow hq prime_9803 hd
          subst q
          change (3 : ZMod 7469887)^762 ≠ 1
          reduce_mod_char
          decide

theorem prime_7529573 : Nat.Prime 7529573 := by
  apply lucas_primality 7529573 (2 : ZMod 7529573)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7529573 - 1 = (2 : ℕ)^2 * ((17 : ℕ)^1 * ((110729 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 7529573)^3764786 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 7529573)^442916 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 110729 := Nat.prime_eq_prime_of_dvd_pow hq prime_110729 hd
        subst q
        change (2 : ZMod 7529573)^68 ≠ 1
        reduce_mod_char
        decide

theorem prime_7544077 : Nat.Prime 7544077 := by
  apply lucas_primality 7544077 (2 : ZMod 7544077)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7544077 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((628673 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 7544077)^3772038 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 7544077)^2514692 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 628673 := Nat.prime_eq_prime_of_dvd_pow hq prime_628673 hd
        subst q
        change (2 : ZMod 7544077)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_7568531 : Nat.Prime 7568531 := by
  apply lucas_primality 7568531 (6 : ZMod 7568531)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7568531 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((756853 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 7568531)^3784265 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 7568531)^1513706 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 756853 := Nat.prime_eq_prime_of_dvd_pow hq prime_756853 hd
        subst q
        change (6 : ZMod 7568531)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_7573883 : Nat.Prime 7573883 := by
  apply lucas_primality 7573883 (2 : ZMod 7573883)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7573883 - 1 = (2 : ℕ)^1 * ((61 : ℕ)^1 * ((62081 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 7573883)^3786941 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
        subst q
        change (2 : ZMod 7573883)^124162 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 62081 := Nat.prime_eq_prime_of_dvd_pow hq prime_62081 hd
        subst q
        change (2 : ZMod 7573883)^122 ≠ 1
        reduce_mod_char
        decide

theorem prime_7587617 : Nat.Prime 7587617 := by
  apply lucas_primality 7587617 (3 : ZMod 7587617)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7587617 - 1 = (2 : ℕ)^5 * ((67 : ℕ)^1 * ((3539 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 7587617)^3793808 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
        subst q
        change (3 : ZMod 7587617)^113248 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3539 := Nat.prime_eq_prime_of_dvd_pow hq prime_3539 hd
        subst q
        change (3 : ZMod 7587617)^2144 ≠ 1
        reduce_mod_char
        decide

theorem prime_7617353 : Nat.Prime 7617353 := by
  apply lucas_primality 7617353 (3 : ZMod 7617353)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7617353 - 1 = (2 : ℕ)^3 * ((952169 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 7617353)^3808676 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 952169 := Nat.prime_eq_prime_of_dvd_pow hq prime_952169 hd
      subst q
      change (3 : ZMod 7617353)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_7652401 : Nat.Prime 7652401 := by
  apply lucas_primality 7652401 (38 : ZMod 7652401)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7652401 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((7 : ℕ)^1 * ((911 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (38 : ZMod 7652401)^3826200 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (38 : ZMod 7652401)^2550800 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (38 : ZMod 7652401)^1530480 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (38 : ZMod 7652401)^1093200 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 911 := Nat.prime_eq_prime_of_dvd_pow hq prime_911 hd
            subst q
            change (38 : ZMod 7652401)^8400 ≠ 1
            reduce_mod_char
            decide

theorem prime_7683409 : Nat.Prime 7683409 := by
  apply lucas_primality 7683409 (7 : ZMod 7683409)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7683409 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((229 : ℕ)^1 * ((233 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 7683409)^3841704 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 7683409)^2561136 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 229 := Nat.prime_eq_prime_of_dvd_pow hq prime_229 hd
          subst q
          change (7 : ZMod 7683409)^33552 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
          subst q
          change (7 : ZMod 7683409)^32976 ≠ 1
          reduce_mod_char
          decide

theorem prime_7696483 : Nat.Prime 7696483 := by
  apply lucas_primality 7696483 (2 : ZMod 7696483)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7696483 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((181 : ℕ)^1 * ((373 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 7696483)^3848241 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 7696483)^2565494 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 7696483)^405078 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 181 := Nat.prime_eq_prime_of_dvd_pow hq prime_181 hd
            subst q
            change (2 : ZMod 7696483)^42522 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 373 := Nat.prime_eq_prime_of_dvd_pow hq prime_373 hd
            subst q
            change (2 : ZMod 7696483)^20634 ≠ 1
            reduce_mod_char
            decide

theorem prime_7724869 : Nat.Prime 7724869 := by
  apply lucas_primality 7724869 (7 : ZMod 7724869)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7724869 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((19 : ℕ)^1 * ((1993 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 7724869)^3862434 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 7724869)^2574956 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (7 : ZMod 7724869)^454404 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (7 : ZMod 7724869)^406572 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1993 := Nat.prime_eq_prime_of_dvd_pow hq prime_1993 hd
            subst q
            change (7 : ZMod 7724869)^3876 ≠ 1
            reduce_mod_char
            decide

theorem prime_7751629 : Nat.Prime 7751629 := by
  apply lucas_primality 7751629 (2 : ZMod 7751629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7751629 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((163 : ℕ)^1 * ((1321 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 7751629)^3875814 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 7751629)^2583876 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
          subst q
          change (2 : ZMod 7751629)^47556 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1321 := Nat.prime_eq_prime_of_dvd_pow hq prime_1321 hd
          subst q
          change (2 : ZMod 7751629)^5868 ≠ 1
          reduce_mod_char
          decide

theorem prime_7836679 : Nat.Prime 7836679 := by
  apply lucas_primality 7836679 (3 : ZMod 7836679)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7836679 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((435371 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 7836679)^3918339 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 7836679)^2612226 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 435371 := Nat.prime_eq_prime_of_dvd_pow hq prime_435371 hd
        subst q
        change (3 : ZMod 7836679)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_7887263 : Nat.Prime 7887263 := by
  apply lucas_primality 7887263 (5 : ZMod 7887263)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7887263 - 1 = (2 : ℕ)^1 * ((3943631 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 7887263)^3943631 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3943631 := Nat.prime_eq_prime_of_dvd_pow hq prime_3943631 hd
      subst q
      change (5 : ZMod 7887263)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_7961227 : Nat.Prime 7961227 := by
  apply lucas_primality 7961227 (2 : ZMod 7961227)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7961227 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((13 : ℕ)^1 * ((2083 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 7961227)^3980613 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 7961227)^2653742 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 7961227)^1137318 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (2 : ZMod 7961227)^612402 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2083 := Nat.prime_eq_prime_of_dvd_pow hq prime_2083 hd
            subst q
            change (2 : ZMod 7961227)^3822 ≠ 1
            reduce_mod_char
            decide

theorem prime_8020303 : Nat.Prime 8020303 := by
  apply lucas_primality 8020303 (3 : ZMod 8020303)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8020303 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((67 : ℕ)^1 * ((71 : ℕ)^1 * ((281 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 8020303)^4010151 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 8020303)^2673434 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (3 : ZMod 8020303)^119706 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
            subst q
            change (3 : ZMod 8020303)^112962 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 281 := Nat.prime_eq_prime_of_dvd_pow hq prime_281 hd
            subst q
            change (3 : ZMod 8020303)^28542 ≠ 1
            reduce_mod_char
            decide

theorem prime_8078051 : Nat.Prime 8078051 := by
  apply lucas_primality 8078051 (6 : ZMod 8078051)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8078051 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((161561 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 8078051)^4039025 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 8078051)^1615610 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 161561 := Nat.prime_eq_prime_of_dvd_pow hq prime_161561 hd
        subst q
        change (6 : ZMod 8078051)^50 ≠ 1
        reduce_mod_char
        decide

theorem prime_8093011 : Nat.Prime 8093011 := by
  apply lucas_primality 8093011 (2 : ZMod 8093011)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8093011 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((23 : ℕ)^1 * ((37 : ℕ)^1 * ((317 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8093011)^4046505 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 8093011)^2697670 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 8093011)^1618602 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (2 : ZMod 8093011)^351870 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
              subst q
              change (2 : ZMod 8093011)^218730 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 317 := Nat.prime_eq_prime_of_dvd_pow hq prime_317 hd
              subst q
              change (2 : ZMod 8093011)^25530 ≠ 1
              reduce_mod_char
              decide

theorem prime_8166061 : Nat.Prime 8166061 := by
  apply lucas_primality 8166061 (6 : ZMod 8166061)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8166061 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((6481 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 8166061)^4083030 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 8166061)^2722020 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 8166061)^1633212 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (6 : ZMod 8166061)^1166580 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 6481 := Nat.prime_eq_prime_of_dvd_pow hq prime_6481 hd
            subst q
            change (6 : ZMod 8166061)^1260 ≠ 1
            reduce_mod_char
            decide

theorem prime_8211191 : Nat.Prime 8211191 := by
  apply lucas_primality 8211191 (7 : ZMod 8211191)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8211191 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((83 : ℕ)^1 * ((761 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 8211191)^4105595 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 8211191)^1642238 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (7 : ZMod 8211191)^631630 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
            subst q
            change (7 : ZMod 8211191)^98930 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 761 := Nat.prime_eq_prime_of_dvd_pow hq prime_761 hd
            subst q
            change (7 : ZMod 8211191)^10790 ≠ 1
            reduce_mod_char
            decide

theorem prime_8378893 : Nat.Prime 8378893 := by
  apply lucas_primality 8378893 (5 : ZMod 8378893)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8378893 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((17 : ℕ)^1 * ((13691 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 8378893)^4189446 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 8378893)^2792964 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (5 : ZMod 8378893)^492876 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13691 := Nat.prime_eq_prime_of_dvd_pow hq prime_13691 hd
          subst q
          change (5 : ZMod 8378893)^612 ≠ 1
          reduce_mod_char
          decide

theorem prime_8490893 : Nat.Prime 8490893 := by
  apply lucas_primality 8490893 (2 : ZMod 8490893)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8490893 - 1 = (2 : ℕ)^2 * ((2122723 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8490893)^4245446 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 2122723 := Nat.prime_eq_prime_of_dvd_pow hq prime_2122723 hd
      subst q
      change (2 : ZMod 8490893)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_8500633 : Nat.Prime 8500633 := by
  apply lucas_primality 8500633 (19 : ZMod 8500633)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8500633 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((50599 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 8500633)^4250316 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 8500633)^2833544 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (19 : ZMod 8500633)^1214376 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 50599 := Nat.prime_eq_prime_of_dvd_pow hq prime_50599 hd
          subst q
          change (19 : ZMod 8500633)^168 ≠ 1
          reduce_mod_char
          decide

theorem prime_8503057 : Nat.Prime 8503057 := by
  apply lucas_primality 8503057 (5 : ZMod 8503057)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8503057 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^12) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 8503057)^4251528 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
      subst q
      change (5 : ZMod 8503057)^2834352 ≠ 1
      reduce_mod_char
      decide

theorem prime_8546843 : Nat.Prime 8546843 := by
  apply lucas_primality 8546843 (2 : ZMod 8546843)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8546843 - 1 = (2 : ℕ)^1 * ((83 : ℕ)^1 * ((51487 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8546843)^4273421 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
        subst q
        change (2 : ZMod 8546843)^102974 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 51487 := Nat.prime_eq_prime_of_dvd_pow hq prime_51487 hd
        subst q
        change (2 : ZMod 8546843)^166 ≠ 1
        reduce_mod_char
        decide

theorem prime_8615137 : Nat.Prime 8615137 := by
  apply lucas_primality 8615137 (5 : ZMod 8615137)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8615137 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((43 : ℕ)^1 * ((2087 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 8615137)^4307568 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 8615137)^2871712 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (5 : ZMod 8615137)^200352 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2087 := Nat.prime_eq_prime_of_dvd_pow hq prime_2087 hd
          subst q
          change (5 : ZMod 8615137)^4128 ≠ 1
          reduce_mod_char
          decide

theorem prime_8701789 : Nat.Prime 8701789 := by
  apply lucas_primality 8701789 (2 : ZMod 8701789)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8701789 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((725149 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8701789)^4350894 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 8701789)^2900596 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 725149 := Nat.prime_eq_prime_of_dvd_pow hq prime_725149 hd
        subst q
        change (2 : ZMod 8701789)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_8708461 : Nat.Prime 8708461 := by
  apply lucas_primality 8708461 (7 : ZMod 8708461)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8708461 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((19 : ℕ)^1 * ((7639 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 8708461)^4354230 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 8708461)^2902820 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 8708461)^1741692 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (7 : ZMod 8708461)^458340 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 7639 := Nat.prime_eq_prime_of_dvd_pow hq prime_7639 hd
            subst q
            change (7 : ZMod 8708461)^1140 ≠ 1
            reduce_mod_char
            decide

theorem prime_8714941 : Nat.Prime 8714941 := by
  apply lucas_primality 8714941 (2 : ZMod 8714941)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8714941 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((11173 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8714941)^4357470 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 8714941)^2904980 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 8714941)^1742988 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (2 : ZMod 8714941)^670380 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 11173 := Nat.prime_eq_prime_of_dvd_pow hq prime_11173 hd
            subst q
            change (2 : ZMod 8714941)^780 ≠ 1
            reduce_mod_char
            decide

theorem prime_8785261 : Nat.Prime 8785261 := by
  apply lucas_primality 8785261 (2 : ZMod 8785261)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8785261 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^4 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((29 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8785261)^4392630 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 8785261)^2928420 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 8785261)^1757052 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (2 : ZMod 8785261)^798660 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
              subst q
              change (2 : ZMod 8785261)^516780 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
              subst q
              change (2 : ZMod 8785261)^302940 ≠ 1
              reduce_mod_char
              decide

theorem prime_8811769 : Nat.Prime 8811769 := by
  apply lucas_primality 8811769 (13 : ZMod 8811769)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8811769 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((59 : ℕ)^1 * ((127 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 8811769)^4405884 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 8811769)^2937256 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (13 : ZMod 8811769)^1258824 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
            subst q
            change (13 : ZMod 8811769)^149352 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
            subst q
            change (13 : ZMod 8811769)^69384 ≠ 1
            reduce_mod_char
            decide

theorem prime_8824169 : Nat.Prime 8824169 := by
  apply lucas_primality 8824169 (3 : ZMod 8824169)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8824169 - 1 = (2 : ℕ)^3 * ((67 : ℕ)^1 * ((101 : ℕ)^1 * ((163 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 8824169)^4412084 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
        subst q
        change (3 : ZMod 8824169)^131704 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
          subst q
          change (3 : ZMod 8824169)^87368 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
          subst q
          change (3 : ZMod 8824169)^54136 ≠ 1
          reduce_mod_char
          decide

theorem prime_8825231 : Nat.Prime 8825231 := by
  apply lucas_primality 8825231 (7 : ZMod 8825231)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8825231 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((127 : ℕ)^1 * ((6949 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 8825231)^4412615 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 8825231)^1765046 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
          subst q
          change (7 : ZMod 8825231)^69490 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 6949 := Nat.prime_eq_prime_of_dvd_pow hq prime_6949 hd
          subst q
          change (7 : ZMod 8825231)^1270 ≠ 1
          reduce_mod_char
          decide

theorem prime_8910103 : Nat.Prime 8910103 := by
  apply lucas_primality 8910103 (5 : ZMod 8910103)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8910103 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1485017 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 8910103)^4455051 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 8910103)^2970034 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1485017 := Nat.prime_eq_prime_of_dvd_pow hq prime_1485017 hd
        subst q
        change (5 : ZMod 8910103)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_8941067 : Nat.Prime 8941067 := by
  apply lucas_primality 8941067 (2 : ZMod 8941067)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8941067 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((194371 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8941067)^4470533 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (2 : ZMod 8941067)^388742 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 194371 := Nat.prime_eq_prime_of_dvd_pow hq prime_194371 hd
        subst q
        change (2 : ZMod 8941067)^46 ≠ 1
        reduce_mod_char
        decide

theorem prime_8982109 : Nat.Prime 8982109 := by
  apply lucas_primality 8982109 (2 : ZMod 8982109)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8982109 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((249503 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8982109)^4491054 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 8982109)^2994036 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 249503 := Nat.prime_eq_prime_of_dvd_pow hq prime_249503 hd
        subst q
        change (2 : ZMod 8982109)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_8987981 : Nat.Prime 8987981 := by
  apply lucas_primality 8987981 (3 : ZMod 8987981)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8987981 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((449399 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 8987981)^4493990 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 8987981)^1797596 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 449399 := Nat.prime_eq_prime_of_dvd_pow hq prime_449399 hd
        subst q
        change (3 : ZMod 8987981)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_8988451 : Nat.Prime 8988451 := by
  apply lucas_primality 8988451 (3 : ZMod 8988451)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8988451 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((31 : ℕ)^1 * ((1933 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 8988451)^4494225 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 8988451)^2996150 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 8988451)^1797690 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (3 : ZMod 8988451)^289950 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1933 := Nat.prime_eq_prime_of_dvd_pow hq prime_1933 hd
            subst q
            change (3 : ZMod 8988451)^4650 ≠ 1
            reduce_mod_char
            decide

theorem prime_8998169 : Nat.Prime 8998169 := by
  apply lucas_primality 8998169 (3 : ZMod 8998169)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8998169 - 1 = (2 : ℕ)^3 * ((17 : ℕ)^1 * ((109 : ℕ)^1 * ((607 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 8998169)^4499084 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (3 : ZMod 8998169)^529304 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
          subst q
          change (3 : ZMod 8998169)^82552 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 607 := Nat.prime_eq_prime_of_dvd_pow hq prime_607 hd
          subst q
          change (3 : ZMod 8998169)^14824 ≠ 1
          reduce_mod_char
          decide

theorem prime_9104413 : Nat.Prime 9104413 := by
  apply lucas_primality 9104413 (2 : ZMod 9104413)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9104413 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((32987 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9104413)^4552206 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 9104413)^3034804 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 9104413)^395844 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 32987 := Nat.prime_eq_prime_of_dvd_pow hq prime_32987 hd
          subst q
          change (2 : ZMod 9104413)^276 ≠ 1
          reduce_mod_char
          decide

theorem prime_9168701 : Nat.Prime 9168701 := by
  apply lucas_primality 9168701 (2 : ZMod 9168701)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9168701 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((277 : ℕ)^1 * ((331 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9168701)^4584350 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 9168701)^1833740 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 277 := Nat.prime_eq_prime_of_dvd_pow hq prime_277 hd
          subst q
          change (2 : ZMod 9168701)^33100 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 331 := Nat.prime_eq_prime_of_dvd_pow hq prime_331 hd
          subst q
          change (2 : ZMod 9168701)^27700 ≠ 1
          reduce_mod_char
          decide

theorem prime_9195223 : Nat.Prime 9195223 := by
  apply lucas_primality 9195223 (3 : ZMod 9195223)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9195223 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((103 : ℕ)^1 * ((14879 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 9195223)^4597611 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 9195223)^3065074 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
          subst q
          change (3 : ZMod 9195223)^89274 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 14879 := Nat.prime_eq_prime_of_dvd_pow hq prime_14879 hd
          subst q
          change (3 : ZMod 9195223)^618 ≠ 1
          reduce_mod_char
          decide

theorem prime_9248543 : Nat.Prime 9248543 := by
  apply lucas_primality 9248543 (5 : ZMod 9248543)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9248543 - 1 = (2 : ℕ)^1 * ((883 : ℕ)^1 * ((5237 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 9248543)^4624271 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 883 := Nat.prime_eq_prime_of_dvd_pow hq prime_883 hd
        subst q
        change (5 : ZMod 9248543)^10474 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5237 := Nat.prime_eq_prime_of_dvd_pow hq prime_5237 hd
        subst q
        change (5 : ZMod 9248543)^1766 ≠ 1
        reduce_mod_char
        decide

theorem prime_9359941 : Nat.Prime 9359941 := by
  apply lucas_primality 9359941 (2 : ZMod 9359941)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9359941 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((257 : ℕ)^1 * ((607 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9359941)^4679970 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 9359941)^3119980 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 9359941)^1871988 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 257 := Nat.prime_eq_prime_of_dvd_pow hq prime_257 hd
            subst q
            change (2 : ZMod 9359941)^36420 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 607 := Nat.prime_eq_prime_of_dvd_pow hq prime_607 hd
            subst q
            change (2 : ZMod 9359941)^15420 ≠ 1
            reduce_mod_char
            decide

theorem prime_9430877 : Nat.Prime 9430877 := by
  apply lucas_primality 9430877 (2 : ZMod 9430877)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9430877 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((13 : ℕ)^2 * ((1993 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9430877)^4715438 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 9430877)^1347268 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 9430877)^725452 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1993 := Nat.prime_eq_prime_of_dvd_pow hq prime_1993 hd
          subst q
          change (2 : ZMod 9430877)^4732 ≠ 1
          reduce_mod_char
          decide

theorem prime_9535873 : Nat.Prime 9535873 := by
  apply lucas_primality 9535873 (5 : ZMod 9535873)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9535873 - 1 = (2 : ℕ)^7 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((1307 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 9535873)^4767936 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 9535873)^3178624 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (5 : ZMod 9535873)^501888 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1307 := Nat.prime_eq_prime_of_dvd_pow hq prime_1307 hd
          subst q
          change (5 : ZMod 9535873)^7296 ≠ 1
          reduce_mod_char
          decide

theorem prime_9581753 : Nat.Prime 9581753 := by
  apply lucas_primality 9581753 (3 : ZMod 9581753)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9581753 - 1 = (2 : ℕ)^3 * ((79 : ℕ)^1 * ((15161 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 9581753)^4790876 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
        subst q
        change (3 : ZMod 9581753)^121288 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 15161 := Nat.prime_eq_prime_of_dvd_pow hq prime_15161 hd
        subst q
        change (3 : ZMod 9581753)^632 ≠ 1
        reduce_mod_char
        decide

theorem prime_9610739 : Nat.Prime 9610739 := by
  apply lucas_primality 9610739 (2 : ZMod 9610739)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9610739 - 1 = (2 : ℕ)^1 * ((139 : ℕ)^1 * ((181 : ℕ)^1 * ((191 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9610739)^4805369 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
        subst q
        change (2 : ZMod 9610739)^69142 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 181 := Nat.prime_eq_prime_of_dvd_pow hq prime_181 hd
          subst q
          change (2 : ZMod 9610739)^53098 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
          subst q
          change (2 : ZMod 9610739)^50318 ≠ 1
          reduce_mod_char
          decide

theorem prime_9662407 : Nat.Prime 9662407 := by
  apply lucas_primality 9662407 (3 : ZMod 9662407)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9662407 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^3 * ((733 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 9662407)^4831203 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 9662407)^3220802 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 9662407)^743262 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 733 := Nat.prime_eq_prime_of_dvd_pow hq prime_733 hd
          subst q
          change (3 : ZMod 9662407)^13182 ≠ 1
          reduce_mod_char
          decide

theorem prime_9668297 : Nat.Prime 9668297 := by
  apply lucas_primality 9668297 (3 : ZMod 9668297)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9668297 - 1 = (2 : ℕ)^3 * ((11 : ℕ)^1 * ((181 : ℕ)^1 * ((607 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 9668297)^4834148 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 9668297)^878936 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 181 := Nat.prime_eq_prime_of_dvd_pow hq prime_181 hd
          subst q
          change (3 : ZMod 9668297)^53416 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 607 := Nat.prime_eq_prime_of_dvd_pow hq prime_607 hd
          subst q
          change (3 : ZMod 9668297)^15928 ≠ 1
          reduce_mod_char
          decide

theorem prime_9672319 : Nat.Prime 9672319 := by
  apply lucas_primality 9672319 (3 : ZMod 9672319)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9672319 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((37 : ℕ)^1 * ((47 : ℕ)^1 * ((103 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 9672319)^4836159 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 9672319)^3224106 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (3 : ZMod 9672319)^261414 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
            subst q
            change (3 : ZMod 9672319)^205794 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
            subst q
            change (3 : ZMod 9672319)^93906 ≠ 1
            reduce_mod_char
            decide

theorem prime_9735701 : Nat.Prime 9735701 := by
  apply lucas_primality 9735701 (2 : ZMod 9735701)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9735701 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((13 : ℕ)^1 * ((7489 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9735701)^4867850 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 9735701)^1947140 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 9735701)^748900 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7489 := Nat.prime_eq_prime_of_dvd_pow hq prime_7489 hd
          subst q
          change (2 : ZMod 9735701)^1300 ≠ 1
          reduce_mod_char
          decide

theorem prime_9996457 : Nat.Prime 9996457 := by
  apply lucas_primality 9996457 (10 : ZMod 9996457)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9996457 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((41 : ℕ)^1 * ((10159 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 9996457)^4998228 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 9996457)^3332152 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (10 : ZMod 9996457)^243816 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 10159 := Nat.prime_eq_prime_of_dvd_pow hq prime_10159 hd
          subst q
          change (10 : ZMod 9996457)^984 ≠ 1
          reduce_mod_char
          decide

theorem prime_10079233 : Nat.Prime 10079233 := by
  apply lucas_primality 10079233 (5 : ZMod 10079233)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10079233 - 1 = (2 : ℕ)^10 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((193 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 10079233)^5039616 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 10079233)^3359744 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (5 : ZMod 10079233)^592896 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
          subst q
          change (5 : ZMod 10079233)^52224 ≠ 1
          reduce_mod_char
          decide

theorem prime_10243201 : Nat.Prime 10243201 := by
  apply lucas_primality 10243201 (21 : ZMod 10243201)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10243201 - 1 = (2 : ℕ)^7 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((11 : ℕ)^1 * ((97 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (21 : ZMod 10243201)^5121600 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (21 : ZMod 10243201)^3414400 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (21 : ZMod 10243201)^2048640 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (21 : ZMod 10243201)^931200 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
            subst q
            change (21 : ZMod 10243201)^105600 ≠ 1
            reduce_mod_char
            decide

theorem prime_10546901 : Nat.Prime 10546901 := by
  apply lucas_primality 10546901 (2 : ZMod 10546901)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10546901 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((19 : ℕ)^1 * ((61 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 10546901)^5273450 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 10546901)^2109380 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 10546901)^1506700 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (2 : ZMod 10546901)^811300 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
              subst q
              change (2 : ZMod 10546901)^555100 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
              subst q
              change (2 : ZMod 10546901)^172900 ≠ 1
              reduce_mod_char
              decide

theorem prime_10575031 : Nat.Prime 10575031 := by
  apply lucas_primality 10575031 (6 : ZMod 10575031)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10575031 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((31 : ℕ)^1 * ((83 : ℕ)^1 * ((137 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 10575031)^5287515 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 10575031)^3525010 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 10575031)^2115006 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (6 : ZMod 10575031)^341130 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
              subst q
              change (6 : ZMod 10575031)^127410 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
              subst q
              change (6 : ZMod 10575031)^77190 ≠ 1
              reduce_mod_char
              decide

theorem prime_10610629 : Nat.Prime 10610629 := by
  apply lucas_primality 10610629 (2 : ZMod 10610629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10610629 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((126317 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 10610629)^5305314 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 10610629)^3536876 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 10610629)^1515804 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 126317 := Nat.prime_eq_prime_of_dvd_pow hq prime_126317 hd
          subst q
          change (2 : ZMod 10610629)^84 ≠ 1
          reduce_mod_char
          decide

theorem prime_10731727 : Nat.Prime 10731727 := by
  apply lucas_primality 10731727 (5 : ZMod 10731727)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10731727 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((17 : ℕ)^2 * ((2063 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 10731727)^5365863 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 10731727)^3577242 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (5 : ZMod 10731727)^631278 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2063 := Nat.prime_eq_prime_of_dvd_pow hq prime_2063 hd
          subst q
          change (5 : ZMod 10731727)^5202 ≠ 1
          reduce_mod_char
          decide

theorem prime_10741963 : Nat.Prime 10741963 := by
  apply lucas_primality 10741963 (2 : ZMod 10741963)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10741963 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((23251 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 10741963)^5370981 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 10741963)^3580654 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 10741963)^1534566 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (2 : ZMod 10741963)^976542 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 23251 := Nat.prime_eq_prime_of_dvd_pow hq prime_23251 hd
            subst q
            change (2 : ZMod 10741963)^462 ≠ 1
            reduce_mod_char
            decide

theorem prime_11014369 : Nat.Prime 11014369 := by
  apply lucas_primality 11014369 (13 : ZMod 11014369)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11014369 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((17 : ℕ)^2 * ((397 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 11014369)^5507184 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 11014369)^3671456 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (13 : ZMod 11014369)^647904 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 397 := Nat.prime_eq_prime_of_dvd_pow hq prime_397 hd
          subst q
          change (13 : ZMod 11014369)^27744 ≠ 1
          reduce_mod_char
          decide

theorem prime_11141929 : Nat.Prime 11141929 := by
  apply lucas_primality 11141929 (11 : ZMod 11141929)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11141929 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((7369 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 11141929)^5570964 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 11141929)^3713976 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (11 : ZMod 11141929)^1591704 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7369 := Nat.prime_eq_prime_of_dvd_pow hq prime_7369 hd
          subst q
          change (11 : ZMod 11141929)^1512 ≠ 1
          reduce_mod_char
          decide

theorem prime_11164003 : Nat.Prime 11164003 := by
  apply lucas_primality 11164003 (2 : ZMod 11164003)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11164003 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((109451 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 11164003)^5582001 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 11164003)^3721334 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 11164003)^656706 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 109451 := Nat.prime_eq_prime_of_dvd_pow hq prime_109451 hd
          subst q
          change (2 : ZMod 11164003)^102 ≠ 1
          reduce_mod_char
          decide

theorem prime_11211883 : Nat.Prime 11211883 := by
  apply lucas_primality 11211883 (2 : ZMod 11211883)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11211883 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((257 : ℕ)^1 * ((661 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 11211883)^5605941 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 11211883)^3737294 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 11211883)^1019262 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 257 := Nat.prime_eq_prime_of_dvd_pow hq prime_257 hd
            subst q
            change (2 : ZMod 11211883)^43626 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 661 := Nat.prime_eq_prime_of_dvd_pow hq prime_661 hd
            subst q
            change (2 : ZMod 11211883)^16962 ≠ 1
            reduce_mod_char
            decide

theorem prime_11217047 : Nat.Prime 11217047 := by
  apply lucas_primality 11217047 (5 : ZMod 11217047)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11217047 - 1 = (2 : ℕ)^1 * ((61 : ℕ)^1 * ((91943 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 11217047)^5608523 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
        subst q
        change (5 : ZMod 11217047)^183886 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 91943 := Nat.prime_eq_prime_of_dvd_pow hq prime_91943 hd
        subst q
        change (5 : ZMod 11217047)^122 ≠ 1
        reduce_mod_char
        decide

theorem prime_11238587 : Nat.Prime 11238587 := by
  apply lucas_primality 11238587 (2 : ZMod 11238587)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11238587 - 1 = (2 : ℕ)^1 * ((659 : ℕ)^1 * ((8527 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 11238587)^5619293 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 659 := Nat.prime_eq_prime_of_dvd_pow hq prime_659 hd
        subst q
        change (2 : ZMod 11238587)^17054 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 8527 := Nat.prime_eq_prime_of_dvd_pow hq prime_8527 hd
        subst q
        change (2 : ZMod 11238587)^1318 ≠ 1
        reduce_mod_char
        decide

theorem prime_11381813 : Nat.Prime 11381813 := by
  apply lucas_primality 11381813 (3 : ZMod 11381813)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11381813 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^2 * ((113 : ℕ)^1 * ((149 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 11381813)^5690906 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 11381813)^875524 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
          subst q
          change (3 : ZMod 11381813)^100724 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
          subst q
          change (3 : ZMod 11381813)^76388 ≠ 1
          reduce_mod_char
          decide

theorem prime_11390641 : Nat.Prime 11390641 := by
  apply lucas_primality 11390641 (7 : ZMod 11390641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11390641 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((31 : ℕ)^1 * ((1531 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 11390641)^5695320 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 11390641)^3796880 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 11390641)^2278128 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (7 : ZMod 11390641)^367440 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1531 := Nat.prime_eq_prime_of_dvd_pow hq prime_1531 hd
            subst q
            change (7 : ZMod 11390641)^7440 ≠ 1
            reduce_mod_char
            decide

theorem prime_11483741 : Nat.Prime 11483741 := by
  apply lucas_primality 11483741 (2 : ZMod 11483741)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11483741 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((173 : ℕ)^1 * ((3319 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 11483741)^5741870 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 11483741)^2296748 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
          subst q
          change (2 : ZMod 11483741)^66380 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3319 := Nat.prime_eq_prime_of_dvd_pow hq prime_3319 hd
          subst q
          change (2 : ZMod 11483741)^3460 ≠ 1
          reduce_mod_char
          decide

theorem prime_11723137 : Nat.Prime 11723137 := by
  apply lucas_primality 11723137 (5 : ZMod 11723137)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11723137 - 1 = (2 : ℕ)^7 * ((3 : ℕ)^1 * ((30529 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 11723137)^5861568 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 11723137)^3907712 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 30529 := Nat.prime_eq_prime_of_dvd_pow hq prime_30529 hd
        subst q
        change (5 : ZMod 11723137)^384 ≠ 1
        reduce_mod_char
        decide

theorem prime_11968643 : Nat.Prime 11968643 := by
  apply lucas_primality 11968643 (2 : ZMod 11968643)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11968643 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^3 * ((73 : ℕ)^1 * ((239 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 11968643)^5984321 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 11968643)^1709806 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
          subst q
          change (2 : ZMod 11968643)^163954 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 239 := Nat.prime_eq_prime_of_dvd_pow hq prime_239 hd
          subst q
          change (2 : ZMod 11968643)^50078 ≠ 1
          reduce_mod_char
          decide

theorem prime_12006251 : Nat.Prime 12006251 := by
  apply lucas_primality 12006251 (6 : ZMod 12006251)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12006251 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^5 * ((17 : ℕ)^1 * ((113 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 12006251)^6003125 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 12006251)^2401250 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (6 : ZMod 12006251)^706250 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
          subst q
          change (6 : ZMod 12006251)^106250 ≠ 1
          reduce_mod_char
          decide

theorem prime_12062191 : Nat.Prime 12062191 := by
  apply lucas_primality 12062191 (3 : ZMod 12062191)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12062191 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((71 : ℕ)^1 * ((809 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 12062191)^6031095 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 12062191)^4020730 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 12062191)^2412438 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (3 : ZMod 12062191)^1723170 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
              subst q
              change (3 : ZMod 12062191)^169890 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 809 := Nat.prime_eq_prime_of_dvd_pow hq prime_809 hd
              subst q
              change (3 : ZMod 12062191)^14910 ≠ 1
              reduce_mod_char
              decide

theorem prime_12161047 : Nat.Prime 12161047 := by
  apply lucas_primality 12161047 (5 : ZMod 12161047)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12161047 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((2026841 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 12161047)^6080523 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 12161047)^4053682 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2026841 := Nat.prime_eq_prime_of_dvd_pow hq prime_2026841 hd
        subst q
        change (5 : ZMod 12161047)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_12176603 : Nat.Prime 12176603 := by
  apply lucas_primality 12176603 (2 : ZMod 12176603)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12176603 - 1 = (2 : ℕ)^1 * ((6088301 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 12176603)^6088301 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 6088301 := Nat.prime_eq_prime_of_dvd_pow hq prime_6088301 hd
      subst q
      change (2 : ZMod 12176603)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_12201593 : Nat.Prime 12201593 := by
  apply lucas_primality 12201593 (3 : ZMod 12201593)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12201593 - 1 = (2 : ℕ)^3 * ((13 : ℕ)^1 * ((23 : ℕ)^1 * ((5101 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 12201593)^6100796 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 12201593)^938584 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (3 : ZMod 12201593)^530504 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 5101 := Nat.prime_eq_prime_of_dvd_pow hq prime_5101 hd
          subst q
          change (3 : ZMod 12201593)^2392 ≠ 1
          reduce_mod_char
          decide

theorem prime_12352559 : Nat.Prime 12352559 := by
  apply lucas_primality 12352559 (7 : ZMod 12352559)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12352559 - 1 = (2 : ℕ)^1 * ((83 : ℕ)^1 * ((74413 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 12352559)^6176279 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
        subst q
        change (7 : ZMod 12352559)^148826 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 74413 := Nat.prime_eq_prime_of_dvd_pow hq prime_74413 hd
        subst q
        change (7 : ZMod 12352559)^166 ≠ 1
        reduce_mod_char
        decide

theorem prime_12426481 : Nat.Prime 12426481 := by
  apply lucas_primality 12426481 (67 : ZMod 12426481)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12426481 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((523 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (67 : ZMod 12426481)^6213240 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (67 : ZMod 12426481)^4142160 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (67 : ZMod 12426481)^2485296 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (67 : ZMod 12426481)^1129680 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 523 := Nat.prime_eq_prime_of_dvd_pow hq prime_523 hd
            subst q
            change (67 : ZMod 12426481)^23760 ≠ 1
            reduce_mod_char
            decide

theorem prime_12487213 : Nat.Prime 12487213 := by
  apply lucas_primality 12487213 (2 : ZMod 12487213)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12487213 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((346867 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 12487213)^6243606 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 12487213)^4162404 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 346867 := Nat.prime_eq_prime_of_dvd_pow hq prime_346867 hd
        subst q
        change (2 : ZMod 12487213)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_12496117 : Nat.Prime 12496117 := by
  apply lucas_primality 12496117 (11 : ZMod 12496117)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12496117 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((1041343 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 12496117)^6248058 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 12496117)^4165372 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1041343 := Nat.prime_eq_prime_of_dvd_pow hq prime_1041343 hd
        subst q
        change (11 : ZMod 12496117)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_12521989 : Nat.Prime 12521989 := by
  apply lucas_primality 12521989 (10 : ZMod 12521989)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12521989 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((19 : ℕ)^1 * ((18307 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 12521989)^6260994 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 12521989)^4173996 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (10 : ZMod 12521989)^659052 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 18307 := Nat.prime_eq_prime_of_dvd_pow hq prime_18307 hd
          subst q
          change (10 : ZMod 12521989)^684 ≠ 1
          reduce_mod_char
          decide

theorem prime_12608957 : Nat.Prime 12608957 := by
  apply lucas_primality 12608957 (2 : ZMod 12608957)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12608957 - 1 = (2 : ℕ)^2 * ((3152239 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 12608957)^6304478 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3152239 := Nat.prime_eq_prime_of_dvd_pow hq prime_3152239 hd
      subst q
      change (2 : ZMod 12608957)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_12639359 : Nat.Prime 12639359 := by
  apply lucas_primality 12639359 (13 : ZMod 12639359)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12639359 - 1 = (2 : ℕ)^1 * ((6319679 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 12639359)^6319679 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 6319679 := Nat.prime_eq_prime_of_dvd_pow hq prime_6319679 hd
      subst q
      change (13 : ZMod 12639359)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_12897889 : Nat.Prime 12897889 := by
  apply lucas_primality 12897889 (17 : ZMod 12897889)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12897889 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((134353 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 12897889)^6448944 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 12897889)^4299296 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 134353 := Nat.prime_eq_prime_of_dvd_pow hq prime_134353 hd
        subst q
        change (17 : ZMod 12897889)^96 ≠ 1
        reduce_mod_char
        decide

theorem prime_12903871 : Nat.Prime 12903871 := by
  apply lucas_primality 12903871 (3 : ZMod 12903871)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12903871 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((43 : ℕ)^1 * ((1429 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 12903871)^6451935 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 12903871)^4301290 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 12903871)^2580774 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (3 : ZMod 12903871)^1843410 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
              subst q
              change (3 : ZMod 12903871)^300090 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1429 := Nat.prime_eq_prime_of_dvd_pow hq prime_1429 hd
              subst q
              change (3 : ZMod 12903871)^9030 ≠ 1
              reduce_mod_char
              decide

theorem prime_12918491 : Nat.Prime 12918491 := by
  apply lucas_primality 12918491 (2 : ZMod 12918491)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12918491 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((43 : ℕ)^1 * ((2311 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 12918491)^6459245 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 12918491)^2583698 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 12918491)^993730 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (2 : ZMod 12918491)^300430 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2311 := Nat.prime_eq_prime_of_dvd_pow hq prime_2311 hd
            subst q
            change (2 : ZMod 12918491)^5590 ≠ 1
            reduce_mod_char
            decide

theorem prime_13122169 : Nat.Prime 13122169 := by
  apply lucas_primality 13122169 (13 : ZMod 13122169)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13122169 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((359 : ℕ)^1 * ((1523 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 13122169)^6561084 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 13122169)^4374056 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 359 := Nat.prime_eq_prime_of_dvd_pow hq prime_359 hd
          subst q
          change (13 : ZMod 13122169)^36552 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1523 := Nat.prime_eq_prime_of_dvd_pow hq prime_1523 hd
          subst q
          change (13 : ZMod 13122169)^8616 ≠ 1
          reduce_mod_char
          decide

theorem prime_13123009 : Nat.Prime 13123009 := by
  apply lucas_primality 13123009 (31 : ZMod 13123009)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13123009 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^2 * ((22783 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (31 : ZMod 13123009)^6561504 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (31 : ZMod 13123009)^4374336 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 22783 := Nat.prime_eq_prime_of_dvd_pow hq prime_22783 hd
        subst q
        change (31 : ZMod 13123009)^576 ≠ 1
        reduce_mod_char
        decide

theorem prime_13186009 : Nat.Prime 13186009 := by
  apply lucas_primality 13186009 (23 : ZMod 13186009)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13186009 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((16649 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (23 : ZMod 13186009)^6593004 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (23 : ZMod 13186009)^4395336 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (23 : ZMod 13186009)^1198728 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 16649 := Nat.prime_eq_prime_of_dvd_pow hq prime_16649 hd
          subst q
          change (23 : ZMod 13186009)^792 ≠ 1
          reduce_mod_char
          decide

theorem prime_13485281 : Nat.Prime 13485281 := by
  apply lucas_primality 13485281 (3 : ZMod 13485281)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13485281 - 1 = (2 : ℕ)^5 * ((5 : ℕ)^1 * ((89 : ℕ)^1 * ((947 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 13485281)^6742640 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 13485281)^2697056 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (3 : ZMod 13485281)^151520 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 947 := Nat.prime_eq_prime_of_dvd_pow hq prime_947 hd
          subst q
          change (3 : ZMod 13485281)^14240 ≠ 1
          reduce_mod_char
          decide

theorem prime_13505993 : Nat.Prime 13505993 := by
  apply lucas_primality 13505993 (3 : ZMod 13505993)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13505993 - 1 = (2 : ℕ)^3 * ((191 : ℕ)^1 * ((8839 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 13505993)^6752996 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
        subst q
        change (3 : ZMod 13505993)^70712 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 8839 := Nat.prime_eq_prime_of_dvd_pow hq prime_8839 hd
        subst q
        change (3 : ZMod 13505993)^1528 ≠ 1
        reduce_mod_char
        decide

theorem prime_13553623 : Nat.Prime 13553623 := by
  apply lucas_primality 13553623 (3 : ZMod 13553623)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13553623 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((250993 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 13553623)^6776811 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 13553623)^4517874 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 250993 := Nat.prime_eq_prime_of_dvd_pow hq prime_250993 hd
        subst q
        change (3 : ZMod 13553623)^54 ≠ 1
        reduce_mod_char
        decide

theorem prime_14012039 : Nat.Prime 14012039 := by
  apply lucas_primality 14012039 (13 : ZMod 14012039)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14012039 - 1 = (2 : ℕ)^1 * ((97 : ℕ)^1 * ((72227 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 14012039)^7006019 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
        subst q
        change (13 : ZMod 14012039)^144454 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 72227 := Nat.prime_eq_prime_of_dvd_pow hq prime_72227 hd
        subst q
        change (13 : ZMod 14012039)^194 ≠ 1
        reduce_mod_char
        decide

theorem prime_14114011 : Nat.Prime 14114011 := by
  apply lucas_primality 14114011 (7 : ZMod 14114011)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14114011 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((29 : ℕ)^1 * ((16223 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 14114011)^7057005 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 14114011)^4704670 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 14114011)^2822802 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (7 : ZMod 14114011)^486690 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 16223 := Nat.prime_eq_prime_of_dvd_pow hq prime_16223 hd
            subst q
            change (7 : ZMod 14114011)^870 ≠ 1
            reduce_mod_char
            decide

theorem prime_14285569 : Nat.Prime 14285569 := by
  apply lucas_primality 14285569 (37 : ZMod 14285569)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14285569 - 1 = (2 : ℕ)^8 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((19 : ℕ)^1 * ((89 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (37 : ZMod 14285569)^7142784 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (37 : ZMod 14285569)^4761856 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (37 : ZMod 14285569)^1298688 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (37 : ZMod 14285569)^751872 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
            subst q
            change (37 : ZMod 14285569)^160512 ≠ 1
            reduce_mod_char
            decide

theorem prime_14391649 : Nat.Prime 14391649 := by
  apply lucas_primality 14391649 (11 : ZMod 14391649)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14391649 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^3 * ((16657 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 14391649)^7195824 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 14391649)^4797216 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 16657 := Nat.prime_eq_prime_of_dvd_pow hq prime_16657 hd
        subst q
        change (11 : ZMod 14391649)^864 ≠ 1
        reduce_mod_char
        decide

theorem prime_14477537 : Nat.Prime 14477537 := by
  apply lucas_primality 14477537 (3 : ZMod 14477537)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14477537 - 1 = (2 : ℕ)^5 * ((487 : ℕ)^1 * ((929 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 14477537)^7238768 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 487 := Nat.prime_eq_prime_of_dvd_pow hq prime_487 hd
        subst q
        change (3 : ZMod 14477537)^29728 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 929 := Nat.prime_eq_prime_of_dvd_pow hq prime_929 hd
        subst q
        change (3 : ZMod 14477537)^15584 ≠ 1
        reduce_mod_char
        decide

theorem prime_14639881 : Nat.Prime 14639881 := by
  apply lucas_primality 14639881 (29 : ZMod 14639881)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14639881 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((19 : ℕ)^1 * ((6421 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (29 : ZMod 14639881)^7319940 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (29 : ZMod 14639881)^4879960 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (29 : ZMod 14639881)^2927976 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (29 : ZMod 14639881)^770520 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 6421 := Nat.prime_eq_prime_of_dvd_pow hq prime_6421 hd
            subst q
            change (29 : ZMod 14639881)^2280 ≠ 1
            reduce_mod_char
            decide

theorem prime_14796371 : Nat.Prime 14796371 := by
  apply lucas_primality 14796371 (2 : ZMod 14796371)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14796371 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((73 : ℕ)^1 * ((20269 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 14796371)^7398185 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 14796371)^2959274 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
          subst q
          change (2 : ZMod 14796371)^202690 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 20269 := Nat.prime_eq_prime_of_dvd_pow hq prime_20269 hd
          subst q
          change (2 : ZMod 14796371)^730 ≠ 1
          reduce_mod_char
          decide

theorem prime_14797417 : Nat.Prime 14797417 := by
  apply lucas_primality 14797417 (10 : ZMod 14797417)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14797417 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((31 : ℕ)^1 * ((19889 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 14797417)^7398708 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 14797417)^4932472 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (10 : ZMod 14797417)^477336 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 19889 := Nat.prime_eq_prime_of_dvd_pow hq prime_19889 hd
          subst q
          change (10 : ZMod 14797417)^744 ≠ 1
          reduce_mod_char
          decide

theorem prime_14915959 : Nat.Prime 14915959 := by
  apply lucas_primality 14915959 (7 : ZMod 14915959)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14915959 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((37 : ℕ)^1 * ((67189 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 14915959)^7457979 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 14915959)^4971986 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (7 : ZMod 14915959)^403134 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 67189 := Nat.prime_eq_prime_of_dvd_pow hq prime_67189 hd
          subst q
          change (7 : ZMod 14915959)^222 ≠ 1
          reduce_mod_char
          decide

theorem prime_15078797 : Nat.Prime 15078797 := by
  apply lucas_primality 15078797 (2 : ZMod 15078797)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15078797 - 1 = (2 : ℕ)^2 * ((17 : ℕ)^1 * ((221747 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 15078797)^7539398 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 15078797)^886988 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 221747 := Nat.prime_eq_prime_of_dvd_pow hq prime_221747 hd
        subst q
        change (2 : ZMod 15078797)^68 ≠ 1
        reduce_mod_char
        decide

theorem prime_15152971 : Nat.Prime 15152971 := by
  apply lucas_primality 15152971 (2 : ZMod 15152971)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15152971 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((59 : ℕ)^1 * ((1223 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 15152971)^7576485 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 15152971)^5050990 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 15152971)^3030594 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (2 : ZMod 15152971)^2164710 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
              subst q
              change (2 : ZMod 15152971)^256830 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1223 := Nat.prime_eq_prime_of_dvd_pow hq prime_1223 hd
              subst q
              change (2 : ZMod 15152971)^12390 ≠ 1
              reduce_mod_char
              decide

theorem prime_15354653 : Nat.Prime 15354653 := by
  apply lucas_primality 15354653 (2 : ZMod 15354653)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15354653 - 1 = (2 : ℕ)^2 * ((919 : ℕ)^1 * ((4177 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 15354653)^7677326 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 919 := Nat.prime_eq_prime_of_dvd_pow hq prime_919 hd
        subst q
        change (2 : ZMod 15354653)^16708 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4177 := Nat.prime_eq_prime_of_dvd_pow hq prime_4177 hd
        subst q
        change (2 : ZMod 15354653)^3676 ≠ 1
        reduce_mod_char
        decide

theorem prime_15362813 : Nat.Prime 15362813 := by
  apply lucas_primality 15362813 (2 : ZMod 15362813)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15362813 - 1 = (2 : ℕ)^2 * ((3840703 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 15362813)^7681406 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3840703 := Nat.prime_eq_prime_of_dvd_pow hq prime_3840703 hd
      subst q
      change (2 : ZMod 15362813)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_15377981 : Nat.Prime 15377981 := by
  apply lucas_primality 15377981 (2 : ZMod 15377981)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15377981 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((787 : ℕ)^1 * ((977 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 15377981)^7688990 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 15377981)^3075596 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 787 := Nat.prime_eq_prime_of_dvd_pow hq prime_787 hd
          subst q
          change (2 : ZMod 15377981)^19540 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 977 := Nat.prime_eq_prime_of_dvd_pow hq prime_977 hd
          subst q
          change (2 : ZMod 15377981)^15740 ≠ 1
          reduce_mod_char
          decide

theorem prime_15510347 : Nat.Prime 15510347 := by
  apply lucas_primality 15510347 (2 : ZMod 15510347)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15510347 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((191 : ℕ)^1 * ((2137 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 15510347)^7755173 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 15510347)^816334 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
          subst q
          change (2 : ZMod 15510347)^81206 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2137 := Nat.prime_eq_prime_of_dvd_pow hq prime_2137 hd
          subst q
          change (2 : ZMod 15510347)^7258 ≠ 1
          reduce_mod_char
          decide

theorem prime_15688193 : Nat.Prime 15688193 := by
  apply lucas_primality 15688193 (3 : ZMod 15688193)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15688193 - 1 = (2 : ℕ)^9 * ((13 : ℕ)^1 * ((2357 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 15688193)^7844096 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 15688193)^1206784 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2357 := Nat.prime_eq_prime_of_dvd_pow hq prime_2357 hd
        subst q
        change (3 : ZMod 15688193)^6656 ≠ 1
        reduce_mod_char
        decide

theorem prime_15838429 : Nat.Prime 15838429 := by
  apply lucas_primality 15838429 (6 : ZMod 15838429)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15838429 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((1319869 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 15838429)^7919214 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 15838429)^5279476 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1319869 := Nat.prime_eq_prime_of_dvd_pow hq prime_1319869 hd
        subst q
        change (6 : ZMod 15838429)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_16146917 : Nat.Prime 16146917 := by
  apply lucas_primality 16146917 (2 : ZMod 16146917)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16146917 - 1 = (2 : ℕ)^2 * ((379 : ℕ)^1 * ((10651 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 16146917)^8073458 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 379 := Nat.prime_eq_prime_of_dvd_pow hq prime_379 hd
        subst q
        change (2 : ZMod 16146917)^42604 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 10651 := Nat.prime_eq_prime_of_dvd_pow hq prime_10651 hd
        subst q
        change (2 : ZMod 16146917)^1516 ≠ 1
        reduce_mod_char
        decide

theorem prime_16218803 : Nat.Prime 16218803 := by
  apply lucas_primality 16218803 (2 : ZMod 16218803)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16218803 - 1 = (2 : ℕ)^1 * ((37 : ℕ)^1 * ((61 : ℕ)^1 * ((3593 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 16218803)^8109401 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (2 : ZMod 16218803)^438346 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (2 : ZMod 16218803)^265882 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3593 := Nat.prime_eq_prime_of_dvd_pow hq prime_3593 hd
          subst q
          change (2 : ZMod 16218803)^4514 ≠ 1
          reduce_mod_char
          decide

theorem prime_16422383 : Nat.Prime 16422383 := by
  apply lucas_primality 16422383 (5 : ZMod 16422383)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16422383 - 1 = (2 : ℕ)^1 * ((8211191 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 16422383)^8211191 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 8211191 := Nat.prime_eq_prime_of_dvd_pow hq prime_8211191 hd
      subst q
      change (5 : ZMod 16422383)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_16476223 : Nat.Prime 16476223 := by
  apply lucas_primality 16476223 (3 : ZMod 16476223)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16476223 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((59 : ℕ)^1 * ((61 : ℕ)^1 * ((109 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 16476223)^8238111 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 16476223)^5492074 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 16476223)^2353746 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
            subst q
            change (3 : ZMod 16476223)^279258 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
              subst q
              change (3 : ZMod 16476223)^270102 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
              subst q
              change (3 : ZMod 16476223)^151158 ≠ 1
              reduce_mod_char
              decide

theorem prime_16777259 : Nat.Prime 16777259 := by
  apply lucas_primality 16777259 (2 : ZMod 16777259)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16777259 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((103 : ℕ)^1 * ((3541 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 16777259)^8388629 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (2 : ZMod 16777259)^729446 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
          subst q
          change (2 : ZMod 16777259)^162886 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3541 := Nat.prime_eq_prime_of_dvd_pow hq prime_3541 hd
          subst q
          change (2 : ZMod 16777259)^4738 ≠ 1
          reduce_mod_char
          decide

theorem prime_17060203 : Nat.Prime 17060203 := by
  apply lucas_primality 17060203 (2 : ZMod 17060203)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17060203 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((149 : ℕ)^1 * ((6361 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 17060203)^8530101 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 17060203)^5686734 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
          subst q
          change (2 : ZMod 17060203)^114498 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 6361 := Nat.prime_eq_prime_of_dvd_pow hq prime_6361 hd
          subst q
          change (2 : ZMod 17060203)^2682 ≠ 1
          reduce_mod_char
          decide

theorem prime_17126653 : Nat.Prime 17126653 := by
  apply lucas_primality 17126653 (2 : ZMod 17126653)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17126653 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((1427221 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 17126653)^8563326 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 17126653)^5708884 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1427221 := Nat.prime_eq_prime_of_dvd_pow hq prime_1427221 hd
        subst q
        change (2 : ZMod 17126653)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_17357143 : Nat.Prime 17357143 := by
  apply lucas_primality 17357143 (3 : ZMod 17357143)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17357143 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((409 : ℕ)^1 * ((643 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 17357143)^8678571 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 17357143)^5785714 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 17357143)^1577922 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 409 := Nat.prime_eq_prime_of_dvd_pow hq prime_409 hd
            subst q
            change (3 : ZMod 17357143)^42438 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 643 := Nat.prime_eq_prime_of_dvd_pow hq prime_643 hd
            subst q
            change (3 : ZMod 17357143)^26994 ≠ 1
            reduce_mod_char
            decide

theorem prime_17474231 : Nat.Prime 17474231 := by
  apply lucas_primality 17474231 (11 : ZMod 17474231)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17474231 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((857 : ℕ)^1 * ((2039 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 17474231)^8737115 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 17474231)^3494846 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 857 := Nat.prime_eq_prime_of_dvd_pow hq prime_857 hd
          subst q
          change (11 : ZMod 17474231)^20390 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2039 := Nat.prime_eq_prime_of_dvd_pow hq prime_2039 hd
          subst q
          change (11 : ZMod 17474231)^8570 ≠ 1
          reduce_mod_char
          decide

theorem prime_17631743 : Nat.Prime 17631743 := by
  apply lucas_primality 17631743 (5 : ZMod 17631743)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17631743 - 1 = (2 : ℕ)^1 * ((257 : ℕ)^1 * ((34303 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 17631743)^8815871 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 257 := Nat.prime_eq_prime_of_dvd_pow hq prime_257 hd
        subst q
        change (5 : ZMod 17631743)^68606 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 34303 := Nat.prime_eq_prime_of_dvd_pow hq prime_34303 hd
        subst q
        change (5 : ZMod 17631743)^514 ≠ 1
        reduce_mod_char
        decide

theorem prime_17648339 : Nat.Prime 17648339 := by
  apply lucas_primality 17648339 (2 : ZMod 17648339)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17648339 - 1 = (2 : ℕ)^1 * ((8824169 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 17648339)^8824169 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 8824169 := Nat.prime_eq_prime_of_dvd_pow hq prime_8824169 hd
      subst q
      change (2 : ZMod 17648339)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_17648531 : Nat.Prime 17648531 := by
  apply lucas_primality 17648531 (2 : ZMod 17648531)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17648531 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((19 : ℕ)^1 * ((29 : ℕ)^1 * ((3203 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 17648531)^8824265 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 17648531)^3529706 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 17648531)^928870 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (2 : ZMod 17648531)^608570 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3203 := Nat.prime_eq_prime_of_dvd_pow hq prime_3203 hd
            subst q
            change (2 : ZMod 17648531)^5510 ≠ 1
            reduce_mod_char
            decide

theorem prime_17674451 : Nat.Prime 17674451 := by
  apply lucas_primality 17674451 (2 : ZMod 17674451)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17674451 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((353489 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 17674451)^8837225 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 17674451)^3534890 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 353489 := Nat.prime_eq_prime_of_dvd_pow hq prime_353489 hd
        subst q
        change (2 : ZMod 17674451)^50 ≠ 1
        reduce_mod_char
        decide

theorem prime_17775011 : Nat.Prime 17775011 := by
  apply lucas_primality 17775011 (2 : ZMod 17775011)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17775011 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((161591 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 17775011)^8887505 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 17775011)^3555002 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 17775011)^1615910 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 161591 := Nat.prime_eq_prime_of_dvd_pow hq prime_161591 hd
          subst q
          change (2 : ZMod 17775011)^110 ≠ 1
          reduce_mod_char
          decide

theorem prime_17839091 : Nat.Prime 17839091 := by
  apply lucas_primality 17839091 (2 : ZMod 17839091)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17839091 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((431 : ℕ)^1 * ((4139 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 17839091)^8919545 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 17839091)^3567818 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 431 := Nat.prime_eq_prime_of_dvd_pow hq prime_431 hd
          subst q
          change (2 : ZMod 17839091)^41390 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4139 := Nat.prime_eq_prime_of_dvd_pow hq prime_4139 hd
          subst q
          change (2 : ZMod 17839091)^4310 ≠ 1
          reduce_mod_char
          decide

theorem prime_17920787 : Nat.Prime 17920787 := by
  apply lucas_primality 17920787 (2 : ZMod 17920787)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17920787 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((689261 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 17920787)^8960393 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 17920787)^1378522 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 689261 := Nat.prime_eq_prime_of_dvd_pow hq prime_689261 hd
        subst q
        change (2 : ZMod 17920787)^26 ≠ 1
        reduce_mod_char
        decide

theorem prime_17921363 : Nat.Prime 17921363 := by
  apply lucas_primality 17921363 (2 : ZMod 17921363)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17921363 - 1 = (2 : ℕ)^1 * ((29 : ℕ)^1 * ((308989 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 17921363)^8960681 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (2 : ZMod 17921363)^617978 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 308989 := Nat.prime_eq_prime_of_dvd_pow hq prime_308989 hd
        subst q
        change (2 : ZMod 17921363)^58 ≠ 1
        reduce_mod_char
        decide

theorem prime_18163121 : Nat.Prime 18163121 := by
  apply lucas_primality 18163121 (3 : ZMod 18163121)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18163121 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((89 : ℕ)^1 * ((2551 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 18163121)^9081560 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 18163121)^3632624 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (3 : ZMod 18163121)^204080 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2551 := Nat.prime_eq_prime_of_dvd_pow hq prime_2551 hd
          subst q
          change (3 : ZMod 18163121)^7120 ≠ 1
          reduce_mod_char
          decide

theorem prime_18168763 : Nat.Prime 18168763 := by
  apply lucas_primality 18168763 (3 : ZMod 18168763)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18168763 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((149 : ℕ)^1 * ((20323 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 18168763)^9084381 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 18168763)^6056254 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
          subst q
          change (3 : ZMod 18168763)^121938 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 20323 := Nat.prime_eq_prime_of_dvd_pow hq prime_20323 hd
          subst q
          change (3 : ZMod 18168763)^894 ≠ 1
          reduce_mod_char
          decide

theorem prime_18325033 : Nat.Prime 18325033 := by
  apply lucas_primality 18325033 (5 : ZMod 18325033)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18325033 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((41 : ℕ)^1 * ((1693 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 18325033)^9162516 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 18325033)^6108344 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 18325033)^1665912 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (5 : ZMod 18325033)^446952 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1693 := Nat.prime_eq_prime_of_dvd_pow hq prime_1693 hd
            subst q
            change (5 : ZMod 18325033)^10824 ≠ 1
            reduce_mod_char
            decide

theorem prime_18438613 : Nat.Prime 18438613 := by
  apply lucas_primality 18438613 (5 : ZMod 18438613)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18438613 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((577 : ℕ)^1 * ((2663 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 18438613)^9219306 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 18438613)^6146204 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 577 := Nat.prime_eq_prime_of_dvd_pow hq prime_577 hd
          subst q
          change (5 : ZMod 18438613)^31956 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2663 := Nat.prime_eq_prime_of_dvd_pow hq prime_2663 hd
          subst q
          change (5 : ZMod 18438613)^6924 ≠ 1
          reduce_mod_char
          decide

theorem prime_18805489 : Nat.Prime 18805489 := by
  apply lucas_primality 18805489 (11 : ZMod 18805489)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18805489 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((30137 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 18805489)^9402744 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 18805489)^6268496 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (11 : ZMod 18805489)^1446576 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 30137 := Nat.prime_eq_prime_of_dvd_pow hq prime_30137 hd
          subst q
          change (11 : ZMod 18805489)^624 ≠ 1
          reduce_mod_char
          decide

theorem prime_19166723 : Nat.Prime 19166723 := by
  apply lucas_primality 19166723 (2 : ZMod 19166723)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19166723 - 1 = (2 : ℕ)^1 * ((1777 : ℕ)^1 * ((5393 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 19166723)^9583361 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1777 := Nat.prime_eq_prime_of_dvd_pow hq prime_1777 hd
        subst q
        change (2 : ZMod 19166723)^10786 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5393 := Nat.prime_eq_prime_of_dvd_pow hq prime_5393 hd
        subst q
        change (2 : ZMod 19166723)^3554 ≠ 1
        reduce_mod_char
        decide

theorem prime_19327193 : Nat.Prime 19327193 := by
  apply lucas_primality 19327193 (3 : ZMod 19327193)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19327193 - 1 = (2 : ℕ)^3 * ((53 : ℕ)^1 * ((79 : ℕ)^1 * ((577 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 19327193)^9663596 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
        subst q
        change (3 : ZMod 19327193)^364664 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (3 : ZMod 19327193)^244648 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 577 := Nat.prime_eq_prime_of_dvd_pow hq prime_577 hd
          subst q
          change (3 : ZMod 19327193)^33496 ≠ 1
          reduce_mod_char
          decide

theorem prime_19333313 : Nat.Prime 19333313 := by
  apply lucas_primality 19333313 (3 : ZMod 19333313)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19333313 - 1 = (2 : ℕ)^6 * ((293 : ℕ)^1 * ((1031 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 19333313)^9666656 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 293 := Nat.prime_eq_prime_of_dvd_pow hq prime_293 hd
        subst q
        change (3 : ZMod 19333313)^65984 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1031 := Nat.prime_eq_prime_of_dvd_pow hq prime_1031 hd
        subst q
        change (3 : ZMod 19333313)^18752 ≠ 1
        reduce_mod_char
        decide

theorem prime_19368257 : Nat.Prime 19368257 := by
  apply lucas_primality 19368257 (3 : ZMod 19368257)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19368257 - 1 = (2 : ℕ)^6 * ((302629 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 19368257)^9684128 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 302629 := Nat.prime_eq_prime_of_dvd_pow hq prime_302629 hd
      subst q
      change (3 : ZMod 19368257)^64 ≠ 1
      reduce_mod_char
      decide

theorem prime_19654451 : Nat.Prime 19654451 := by
  apply lucas_primality 19654451 (2 : ZMod 19654451)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19654451 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((67 : ℕ)^1 * ((5867 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 19654451)^9827225 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 19654451)^3930890 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (2 : ZMod 19654451)^293350 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 5867 := Nat.prime_eq_prime_of_dvd_pow hq prime_5867 hd
          subst q
          change (2 : ZMod 19654451)^3350 ≠ 1
          reduce_mod_char
          decide

theorem prime_19777991 : Nat.Prime 19777991 := by
  apply lucas_primality 19777991 (7 : ZMod 19777991)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19777991 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((41 : ℕ)^1 * ((48239 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 19777991)^9888995 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 19777991)^3955598 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (7 : ZMod 19777991)^482390 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 48239 := Nat.prime_eq_prime_of_dvd_pow hq prime_48239 hd
          subst q
          change (7 : ZMod 19777991)^410 ≠ 1
          reduce_mod_char
          decide

theorem prime_19806337 : Nat.Prime 19806337 := by
  apply lucas_primality 19806337 (5 : ZMod 19806337)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19806337 - 1 = (2 : ℕ)^7 * ((3 : ℕ)^3 * ((11 : ℕ)^1 * ((521 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 19806337)^9903168 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 19806337)^6602112 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 19806337)^1800576 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 521 := Nat.prime_eq_prime_of_dvd_pow hq prime_521 hd
          subst q
          change (5 : ZMod 19806337)^38016 ≠ 1
          reduce_mod_char
          decide

end LegendreK6.Pratt
