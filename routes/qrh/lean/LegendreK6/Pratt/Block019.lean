import LegendreK6.Pratt.Block018

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LegendreK6.Pratt

theorem prime_885780500021 : Nat.Prime 885780500021 := by
  apply lucas_primality 885780500021 (2 : ZMod 885780500021)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 885780500021 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((50383 : ℕ)^1 * ((67619 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 885780500021)^442890250010 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 885780500021)^177156100004 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 885780500021)^68136961540 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 50383 := Nat.prime_eq_prime_of_dvd_pow hq prime_50383 hd
            subst q
            change (2 : ZMod 885780500021)^17580940 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 67619 := Nat.prime_eq_prime_of_dvd_pow hq prime_67619 hd
            subst q
            change (2 : ZMod 885780500021)^13099580 ≠ 1
            reduce_mod_char
            decide

theorem prime_885842380877 : Nat.Prime 885842380877 := by
  apply lucas_primality 885842380877 (2 : ZMod 885842380877)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 885842380877 - 1 = (2 : ℕ)^2 * ((19 : ℕ)^1 * ((307 : ℕ)^1 * ((1567 : ℕ)^1 * ((24229 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 885842380877)^442921190438 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 885842380877)^46623283204 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 307 := Nat.prime_eq_prime_of_dvd_pow hq prime_307 hd
          subst q
          change (2 : ZMod 885842380877)^2885480068 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1567 := Nat.prime_eq_prime_of_dvd_pow hq prime_1567 hd
            subst q
            change (2 : ZMod 885842380877)^565311028 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 24229 := Nat.prime_eq_prime_of_dvd_pow hq prime_24229 hd
            subst q
            change (2 : ZMod 885842380877)^36561244 ≠ 1
            reduce_mod_char
            decide

theorem prime_898143021467 : Nat.Prime 898143021467 := by
  apply lucas_primality 898143021467 (2 : ZMod 898143021467)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 898143021467 - 1 = (2 : ℕ)^1 * ((449071510733 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 898143021467)^449071510733 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 449071510733 := Nat.prime_eq_prime_of_dvd_pow hq prime_449071510733 hd
      subst q
      change (2 : ZMod 898143021467)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_924387773761 : Nat.Prime 924387773761 := by
  apply lucas_primality 924387773761 (17 : ZMod 924387773761)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 924387773761 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((29178907 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 924387773761)^462193886880 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 924387773761)^308129257920 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (17 : ZMod 924387773761)^184877554752 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (17 : ZMod 924387773761)^84035252160 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 29178907 := Nat.prime_eq_prime_of_dvd_pow hq prime_29178907 hd
            subst q
            change (17 : ZMod 924387773761)^31680 ≠ 1
            reduce_mod_char
            decide

theorem prime_933432369647 : Nat.Prime 933432369647 := by
  apply lucas_primality 933432369647 (5 : ZMod 933432369647)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 933432369647 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((5081 : ℕ)^1 * ((13122169 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 933432369647)^466716184823 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 933432369647)^133347481378 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5081 := Nat.prime_eq_prime_of_dvd_pow hq prime_5081 hd
          subst q
          change (5 : ZMod 933432369647)^183710366 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13122169 := Nat.prime_eq_prime_of_dvd_pow hq prime_13122169 hd
          subst q
          change (5 : ZMod 933432369647)^71134 ≠ 1
          reduce_mod_char
          decide

theorem prime_937164233261 : Nat.Prime 937164233261 := by
  apply lucas_primality 937164233261 (2 : ZMod 937164233261)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 937164233261 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((277 : ℕ)^1 * ((2657 : ℕ)^1 * ((63667 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 937164233261)^468582116630 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 937164233261)^187432846652 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 277 := Nat.prime_eq_prime_of_dvd_pow hq prime_277 hd
          subst q
          change (2 : ZMod 937164233261)^3383264380 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2657 := Nat.prime_eq_prime_of_dvd_pow hq prime_2657 hd
            subst q
            change (2 : ZMod 937164233261)^352715180 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 63667 := Nat.prime_eq_prime_of_dvd_pow hq prime_63667 hd
            subst q
            change (2 : ZMod 937164233261)^14719780 ≠ 1
            reduce_mod_char
            decide

theorem prime_941480149433 : Nat.Prime 941480149433 := by
  apply lucas_primality 941480149433 (3 : ZMod 941480149433)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 941480149433 - 1 = (2 : ℕ)^3 * ((117685018679 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 941480149433)^470740074716 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 117685018679 := Nat.prime_eq_prime_of_dvd_pow hq prime_117685018679 hd
      subst q
      change (3 : ZMod 941480149433)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_957430013021 : Nat.Prime 957430013021 := by
  apply lucas_primality 957430013021 (2 : ZMod 957430013021)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 957430013021 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((6871 : ℕ)^1 * ((535937 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 957430013021)^478715006510 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 957430013021)^191486002604 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 957430013021)^73648462540 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 6871 := Nat.prime_eq_prime_of_dvd_pow hq prime_6871 hd
            subst q
            change (2 : ZMod 957430013021)^139343620 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 535937 := Nat.prime_eq_prime_of_dvd_pow hq prime_535937 hd
            subst q
            change (2 : ZMod 957430013021)^1786460 ≠ 1
            reduce_mod_char
            decide

theorem prime_959391145907 : Nat.Prime 959391145907 := by
  apply lucas_primality 959391145907 (2 : ZMod 959391145907)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 959391145907 - 1 = (2 : ℕ)^1 * ((479695572953 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 959391145907)^479695572953 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 479695572953 := Nat.prime_eq_prime_of_dvd_pow hq prime_479695572953 hd
      subst q
      change (2 : ZMod 959391145907)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_968959122529 : Nat.Prime 968959122529 := by
  apply lucas_primality 968959122529 (7 : ZMod 968959122529)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 968959122529 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((31 : ℕ)^1 * ((89 : ℕ)^1 * ((3658327 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 968959122529)^484479561264 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 968959122529)^322986374176 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (7 : ZMod 968959122529)^31256745888 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
            subst q
            change (7 : ZMod 968959122529)^10887181152 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3658327 := Nat.prime_eq_prime_of_dvd_pow hq prime_3658327 hd
            subst q
            change (7 : ZMod 968959122529)^264864 ≠ 1
            reduce_mod_char
            decide

theorem prime_983629708781 : Nat.Prime 983629708781 := by
  apply lucas_primality 983629708781 (2 : ZMod 983629708781)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 983629708781 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((29 : ℕ)^1 * ((173 : ℕ)^1 * ((503 : ℕ)^1 * ((19489 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 983629708781)^491814854390 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 983629708781)^196725941756 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (2 : ZMod 983629708781)^33918265820 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
            subst q
            change (2 : ZMod 983629708781)^5685720860 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 503 := Nat.prime_eq_prime_of_dvd_pow hq prime_503 hd
              subst q
              change (2 : ZMod 983629708781)^1955526260 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 19489 := Nat.prime_eq_prime_of_dvd_pow hq prime_19489 hd
              subst q
              change (2 : ZMod 983629708781)^50471020 ≠ 1
              reduce_mod_char
              decide

theorem prime_990298287827 : Nat.Prime 990298287827 := by
  apply lucas_primality 990298287827 (2 : ZMod 990298287827)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 990298287827 - 1 = (2 : ℕ)^1 * ((495149143913 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 990298287827)^495149143913 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 495149143913 := Nat.prime_eq_prime_of_dvd_pow hq prime_495149143913 hd
      subst q
      change (2 : ZMod 990298287827)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_1000000000039 : Nat.Prime 1000000000039 := by
  apply lucas_primality 1000000000039 (3 : ZMod 1000000000039)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1000000000039 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((17 : ℕ)^1 * ((29 : ℕ)^1 * ((26005097 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1000000000039)^500000000019 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1000000000039)^333333333346 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 1000000000039)^76923076926 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (3 : ZMod 1000000000039)^58823529414 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
              subst q
              change (3 : ZMod 1000000000039)^34482758622 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 26005097 := Nat.prime_eq_prime_of_dvd_pow hq prime_26005097 hd
              subst q
              change (3 : ZMod 1000000000039)^38454 ≠ 1
              reduce_mod_char
              decide

theorem prime_1003421365013 : Nat.Prime 1003421365013 := by
  apply lucas_primality 1003421365013 (2 : ZMod 1003421365013)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1003421365013 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((269 : ℕ)^1 * ((1787 : ℕ)^1 * ((47441 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1003421365013)^501710682506 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 1003421365013)^91220124092 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
          subst q
          change (2 : ZMod 1003421365013)^3730190948 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1787 := Nat.prime_eq_prime_of_dvd_pow hq prime_1787 hd
            subst q
            change (2 : ZMod 1003421365013)^561511676 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 47441 := Nat.prime_eq_prime_of_dvd_pow hq prime_47441 hd
            subst q
            change (2 : ZMod 1003421365013)^21150932 ≠ 1
            reduce_mod_char
            decide

theorem prime_1010482895921 : Nat.Prime 1010482895921 := by
  apply lucas_primality 1010482895921 (3 : ZMod 1010482895921)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1010482895921 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((12631036199 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1010482895921)^505241447960 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 1010482895921)^202096579184 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 12631036199 := Nat.prime_eq_prime_of_dvd_pow hq prime_12631036199 hd
        subst q
        change (3 : ZMod 1010482895921)^80 ≠ 1
        reduce_mod_char
        decide

theorem prime_1022120181167 : Nat.Prime 1022120181167 := by
  apply lucas_primality 1022120181167 (5 : ZMod 1022120181167)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1022120181167 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^2 * ((4253 : ℕ)^1 * ((2452339 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1022120181167)^511060090583 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 1022120181167)^146017168738 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 4253 := Nat.prime_eq_prime_of_dvd_pow hq prime_4253 hd
          subst q
          change (5 : ZMod 1022120181167)^240329222 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2452339 := Nat.prime_eq_prime_of_dvd_pow hq prime_2452339 hd
          subst q
          change (5 : ZMod 1022120181167)^416794 ≠ 1
          reduce_mod_char
          decide

theorem prime_1061520150659 : Nat.Prime 1061520150659 := by
  apply lucas_primality 1061520150659 (2 : ZMod 1061520150659)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1061520150659 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((48250915939 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1061520150659)^530760075329 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 1061520150659)^96501831878 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 48250915939 := Nat.prime_eq_prime_of_dvd_pow hq prime_48250915939 hd
        subst q
        change (2 : ZMod 1061520150659)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_1078026684389 : Nat.Prime 1078026684389 := by
  apply lucas_primality 1078026684389 (2 : ZMod 1078026684389)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1078026684389 - 1 = (2 : ℕ)^2 * ((71 : ℕ)^1 * ((3795868607 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1078026684389)^539013342194 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
        subst q
        change (2 : ZMod 1078026684389)^15183474428 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3795868607 := Nat.prime_eq_prime_of_dvd_pow hq prime_3795868607 hd
        subst q
        change (2 : ZMod 1078026684389)^284 ≠ 1
        reduce_mod_char
        decide

theorem prime_1126162419271 : Nat.Prime 1126162419271 := by
  apply lucas_primality 1126162419271 (15 : ZMod 1126162419271)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1126162419271 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((2699 : ℕ)^1 * ((1986913 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (15 : ZMod 1126162419271)^563081209635 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (15 : ZMod 1126162419271)^375387473090 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (15 : ZMod 1126162419271)^225232483854 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (15 : ZMod 1126162419271)^160880345610 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 2699 := Nat.prime_eq_prime_of_dvd_pow hq prime_2699 hd
              subst q
              change (15 : ZMod 1126162419271)^417251730 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1986913 := Nat.prime_eq_prime_of_dvd_pow hq prime_1986913 hd
              subst q
              change (15 : ZMod 1126162419271)^566790 ≠ 1
              reduce_mod_char
              decide

theorem prime_1137720182089 : Nat.Prime 1137720182089 := by
  apply lucas_primality 1137720182089 (19 : ZMod 1137720182089)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1137720182089 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((191 : ℕ)^1 * ((35456251 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 1137720182089)^568860091044 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 1137720182089)^379240060696 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (19 : ZMod 1137720182089)^162531454584 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
            subst q
            change (19 : ZMod 1137720182089)^5956650168 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 35456251 := Nat.prime_eq_prime_of_dvd_pow hq prime_35456251 hd
            subst q
            change (19 : ZMod 1137720182089)^32088 ≠ 1
            reduce_mod_char
            decide

theorem prime_1140731484769 : Nat.Prime 1140731484769 := by
  apply lucas_primality 1140731484769 (11 : ZMod 1140731484769)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1140731484769 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^2 * ((313 : ℕ)^1 * ((1061 : ℕ)^1 * ((11927 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 1140731484769)^570365742384 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 1140731484769)^380243828256 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 313 := Nat.prime_eq_prime_of_dvd_pow hq prime_313 hd
          subst q
          change (11 : ZMod 1140731484769)^3644509536 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1061 := Nat.prime_eq_prime_of_dvd_pow hq prime_1061 hd
            subst q
            change (11 : ZMod 1140731484769)^1075147488 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 11927 := Nat.prime_eq_prime_of_dvd_pow hq prime_11927 hd
            subst q
            change (11 : ZMod 1140731484769)^95642784 ≠ 1
            reduce_mod_char
            decide

theorem prime_1164120080237 : Nat.Prime 1164120080237 := by
  apply lucas_primality 1164120080237 (2 : ZMod 1164120080237)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1164120080237 - 1 = (2 : ℕ)^2 * ((23 : ℕ)^1 * ((12653479133 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1164120080237)^582060040118 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (2 : ZMod 1164120080237)^50613916532 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 12653479133 := Nat.prime_eq_prime_of_dvd_pow hq prime_12653479133 hd
        subst q
        change (2 : ZMod 1164120080237)^92 ≠ 1
        reduce_mod_char
        decide

theorem prime_1194052296533 : Nat.Prime 1194052296533 := by
  apply lucas_primality 1194052296533 (2 : ZMod 1194052296533)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1194052296533 - 1 = (2 : ℕ)^2 * ((61 : ℕ)^1 * ((4893656953 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1194052296533)^597026148266 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
        subst q
        change (2 : ZMod 1194052296533)^19574627812 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4893656953 := Nat.prime_eq_prime_of_dvd_pow hq prime_4893656953 hd
        subst q
        change (2 : ZMod 1194052296533)^244 ≠ 1
        reduce_mod_char
        decide

theorem prime_1206334149719 : Nat.Prime 1206334149719 := by
  apply lucas_primality 1206334149719 (17 : ZMod 1206334149719)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1206334149719 - 1 = (2 : ℕ)^1 * ((135427 : ℕ)^1 * ((4453817 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 1206334149719)^603167074859 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 135427 := Nat.prime_eq_prime_of_dvd_pow hq prime_135427 hd
        subst q
        change (17 : ZMod 1206334149719)^8907634 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4453817 := Nat.prime_eq_prime_of_dvd_pow hq prime_4453817 hd
        subst q
        change (17 : ZMod 1206334149719)^270854 ≠ 1
        reduce_mod_char
        decide

theorem prime_1220457924199 : Nat.Prime 1220457924199 := by
  apply lucas_primality 1220457924199 (3 : ZMod 1220457924199)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1220457924199 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((31 : ℕ)^1 * ((1291 : ℕ)^1 * ((1694191 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1220457924199)^610228962099 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1220457924199)^406819308066 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (3 : ZMod 1220457924199)^39369610458 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1291 := Nat.prime_eq_prime_of_dvd_pow hq prime_1291 hd
            subst q
            change (3 : ZMod 1220457924199)^945358578 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1694191 := Nat.prime_eq_prime_of_dvd_pow hq prime_1694191 hd
            subst q
            change (3 : ZMod 1220457924199)^720378 ≠ 1
            reduce_mod_char
            decide

theorem prime_1229838842693 : Nat.Prime 1229838842693 := by
  apply lucas_primality 1229838842693 (2 : ZMod 1229838842693)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1229838842693 - 1 = (2 : ℕ)^2 * ((31 : ℕ)^1 * ((4889 : ℕ)^1 * ((2028647 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1229838842693)^614919421346 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (2 : ZMod 1229838842693)^39672220732 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 4889 := Nat.prime_eq_prime_of_dvd_pow hq prime_4889 hd
          subst q
          change (2 : ZMod 1229838842693)^251552228 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2028647 := Nat.prime_eq_prime_of_dvd_pow hq prime_2028647 hd
          subst q
          change (2 : ZMod 1229838842693)^606236 ≠ 1
          reduce_mod_char
          decide

theorem prime_1238601284731 : Nat.Prime 1238601284731 := by
  apply lucas_primality 1238601284731 (3 : ZMod 1238601284731)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1238601284731 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((137 : ℕ)^1 * ((100454281 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1238601284731)^619300642365 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1238601284731)^412867094910 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 1238601284731)^247720256946 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
            subst q
            change (3 : ZMod 1238601284731)^9040885290 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 100454281 := Nat.prime_eq_prime_of_dvd_pow hq prime_100454281 hd
            subst q
            change (3 : ZMod 1238601284731)^12330 ≠ 1
            reduce_mod_char
            decide

theorem prime_1265319018503 : Nat.Prime 1265319018503 := by
  apply lucas_primality 1265319018503 (5 : ZMod 1265319018503)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1265319018503 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((68329 : ℕ)^1 * ((120247 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1265319018503)^632659509251 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 1265319018503)^180759859786 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 1265319018503)^115029001682 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 68329 := Nat.prime_eq_prime_of_dvd_pow hq prime_68329 hd
            subst q
            change (5 : ZMod 1265319018503)^18518038 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 120247 := Nat.prime_eq_prime_of_dvd_pow hq prime_120247 hd
            subst q
            change (5 : ZMod 1265319018503)^10522666 ≠ 1
            reduce_mod_char
            decide

theorem prime_1273948735597 : Nat.Prime 1273948735597 := by
  apply lucas_primality 1273948735597 (5 : ZMod 1273948735597)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1273948735597 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((37 : ℕ)^1 * ((2869253909 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1273948735597)^636974367798 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1273948735597)^424649578532 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (5 : ZMod 1273948735597)^34431046908 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2869253909 := Nat.prime_eq_prime_of_dvd_pow hq prime_2869253909 hd
          subst q
          change (5 : ZMod 1273948735597)^444 ≠ 1
          reduce_mod_char
          decide

theorem prime_1296661289717 : Nat.Prime 1296661289717 := by
  apply lucas_primality 1296661289717 (2 : ZMod 1296661289717)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1296661289717 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((24935794033 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1296661289717)^648330644858 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 1296661289717)^99743176132 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 24935794033 := Nat.prime_eq_prime_of_dvd_pow hq prime_24935794033 hd
        subst q
        change (2 : ZMod 1296661289717)^52 ≠ 1
        reduce_mod_char
        decide

theorem prime_1319988040037 : Nat.Prime 1319988040037 := by
  apply lucas_primality 1319988040037 (2 : ZMod 1319988040037)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1319988040037 - 1 = (2 : ℕ)^2 * ((31 : ℕ)^1 * ((557 : ℕ)^1 * ((4231 : ℕ)^1 * ((4517 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1319988040037)^659994020018 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (2 : ZMod 1319988040037)^42580259356 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 557 := Nat.prime_eq_prime_of_dvd_pow hq prime_557 hd
          subst q
          change (2 : ZMod 1319988040037)^2369816948 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 4231 := Nat.prime_eq_prime_of_dvd_pow hq prime_4231 hd
            subst q
            change (2 : ZMod 1319988040037)^311980156 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 4517 := Nat.prime_eq_prime_of_dvd_pow hq prime_4517 hd
            subst q
            change (2 : ZMod 1319988040037)^292226708 ≠ 1
            reduce_mod_char
            decide

theorem prime_1320382239221 : Nat.Prime 1320382239221 := by
  apply lucas_primality 1320382239221 (2 : ZMod 1320382239221)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1320382239221 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((6001737451 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1320382239221)^660191119610 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 1320382239221)^264076447844 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 1320382239221)^120034749020 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 6001737451 := Nat.prime_eq_prime_of_dvd_pow hq prime_6001737451 hd
          subst q
          change (2 : ZMod 1320382239221)^220 ≠ 1
          reduce_mod_char
          decide

theorem prime_1340095640647 : Nat.Prime 1340095640647 := by
  apply lucas_primality 1340095640647 (3 : ZMod 1340095640647)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1340095640647 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((188261 : ℕ)^1 * ((169483 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1340095640647)^670047820323 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1340095640647)^446698546882 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 1340095640647)^191442234378 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 188261 := Nat.prime_eq_prime_of_dvd_pow hq prime_188261 hd
            subst q
            change (3 : ZMod 1340095640647)^7118286 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 169483 := Nat.prime_eq_prime_of_dvd_pow hq prime_169483 hd
            subst q
            change (3 : ZMod 1340095640647)^7906962 ≠ 1
            reduce_mod_char
            decide

theorem prime_1368798180479 : Nat.Prime 1368798180479 := by
  apply lucas_primality 1368798180479 (7 : ZMod 1368798180479)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1368798180479 - 1 = (2 : ℕ)^1 * ((2053 : ℕ)^1 * ((333365363 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1368798180479)^684399090239 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 2053 := Nat.prime_eq_prime_of_dvd_pow hq prime_2053 hd
        subst q
        change (7 : ZMod 1368798180479)^666730726 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 333365363 := Nat.prime_eq_prime_of_dvd_pow hq prime_333365363 hd
        subst q
        change (7 : ZMod 1368798180479)^4106 ≠ 1
        reduce_mod_char
        decide

theorem prime_1377895995239 : Nat.Prime 1377895995239 := by
  apply lucas_primality 1377895995239 (7 : ZMod 1377895995239)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1377895995239 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((53 : ℕ)^1 * ((73 : ℕ)^1 * ((25438393 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1377895995239)^688947997619 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 1377895995239)^196842285034 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (7 : ZMod 1377895995239)^25998037646 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
            subst q
            change (7 : ZMod 1377895995239)^18875287606 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 25438393 := Nat.prime_eq_prime_of_dvd_pow hq prime_25438393 hd
            subst q
            change (7 : ZMod 1377895995239)^54166 ≠ 1
            reduce_mod_char
            decide

theorem prime_1393829794267 : Nat.Prime 1393829794267 := by
  apply lucas_primality 1393829794267 (7 : ZMod 1393829794267)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1393829794267 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((17 : ℕ)^1 * ((29 : ℕ)^1 * ((227 : ℕ)^1 * ((22811 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1393829794267)^696914897133 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 1393829794267)^464609931422 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 1393829794267)^199118542038 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (7 : ZMod 1393829794267)^107217676482 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
              subst q
              change (7 : ZMod 1393829794267)^81989987898 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
                subst q
                change (7 : ZMod 1393829794267)^48063096354 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 227 := Nat.prime_eq_prime_of_dvd_pow hq prime_227 hd
                  subst q
                  change (7 : ZMod 1393829794267)^6140219358 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 22811 := Nat.prime_eq_prime_of_dvd_pow hq prime_22811 hd
                  subst q
                  change (7 : ZMod 1393829794267)^61103406 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_1418519112281 : Nat.Prime 1418519112281 := by
  apply lucas_primality 1418519112281 (3 : ZMod 1418519112281)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1418519112281 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((193 : ℕ)^1 * ((183745999 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1418519112281)^709259556140 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 1418519112281)^283703822456 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
          subst q
          change (3 : ZMod 1418519112281)^7349839960 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 183745999 := Nat.prime_eq_prime_of_dvd_pow hq prime_183745999 hd
          subst q
          change (3 : ZMod 1418519112281)^7720 ≠ 1
          reduce_mod_char
          decide

theorem prime_1477475405221 : Nat.Prime 1477475405221 := by
  apply lucas_primality 1477475405221 (6 : ZMod 1477475405221)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1477475405221 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((24624590087 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 1477475405221)^738737702610 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 1477475405221)^492491801740 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 1477475405221)^295495081044 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 24624590087 := Nat.prime_eq_prime_of_dvd_pow hq prime_24624590087 hd
          subst q
          change (6 : ZMod 1477475405221)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_1483482723377 : Nat.Prime 1483482723377 := by
  apply lucas_primality 1483482723377 (3 : ZMod 1483482723377)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1483482723377 - 1 = (2 : ℕ)^4 * ((92717670211 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1483482723377)^741741361688 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 92717670211 := Nat.prime_eq_prime_of_dvd_pow hq prime_92717670211 hd
      subst q
      change (3 : ZMod 1483482723377)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_1493690200097 : Nat.Prime 1493690200097 := by
  apply lucas_primality 1493690200097 (3 : ZMod 1493690200097)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1493690200097 - 1 = (2 : ℕ)^5 * ((29 : ℕ)^1 * ((37 : ℕ)^1 * ((43502161 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1493690200097)^746845100048 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (3 : ZMod 1493690200097)^51506558624 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (3 : ZMod 1493690200097)^40370005408 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 43502161 := Nat.prime_eq_prime_of_dvd_pow hq prime_43502161 hd
          subst q
          change (3 : ZMod 1493690200097)^34336 ≠ 1
          reduce_mod_char
          decide

theorem prime_1498988634911 : Nat.Prime 1498988634911 := by
  apply lucas_primality 1498988634911 (17 : ZMod 1498988634911)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1498988634911 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((313 : ℕ)^1 * ((491 : ℕ)^1 * ((75029 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 1498988634911)^749494317455 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (17 : ZMod 1498988634911)^299797726982 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (17 : ZMod 1498988634911)^115306818070 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 313 := Nat.prime_eq_prime_of_dvd_pow hq prime_313 hd
            subst q
            change (17 : ZMod 1498988634911)^4789101070 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 491 := Nat.prime_eq_prime_of_dvd_pow hq prime_491 hd
              subst q
              change (17 : ZMod 1498988634911)^3052930010 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 75029 := Nat.prime_eq_prime_of_dvd_pow hq prime_75029 hd
              subst q
              change (17 : ZMod 1498988634911)^19978790 ≠ 1
              reduce_mod_char
              decide

theorem prime_1500730351853 : Nat.Prime 1500730351853 := by
  apply lucas_primality 1500730351853 (2 : ZMod 1500730351853)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1500730351853 - 1 = (2 : ℕ)^2 * ((375182587963 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1500730351853)^750365175926 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 375182587963 := Nat.prime_eq_prime_of_dvd_pow hq prime_375182587963 hd
      subst q
      change (2 : ZMod 1500730351853)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_1508088892619 : Nat.Prime 1508088892619 := by
  apply lucas_primality 1508088892619 (2 : ZMod 1508088892619)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1508088892619 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((683 : ℕ)^1 * ((1951 : ℕ)^1 * ((7349 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1508088892619)^754044446309 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 1508088892619)^215441270374 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 1508088892619)^137098990238 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 683 := Nat.prime_eq_prime_of_dvd_pow hq prime_683 hd
            subst q
            change (2 : ZMod 1508088892619)^2208036446 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1951 := Nat.prime_eq_prime_of_dvd_pow hq prime_1951 hd
              subst q
              change (2 : ZMod 1508088892619)^772982518 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 7349 := Nat.prime_eq_prime_of_dvd_pow hq prime_7349 hd
              subst q
              change (2 : ZMod 1508088892619)^205210082 ≠ 1
              reduce_mod_char
              decide

theorem prime_1517970517339 : Nat.Prime 1517970517339 := by
  apply lucas_primality 1517970517339 (2 : ZMod 1517970517339)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1517970517339 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((9851 : ℕ)^1 * ((2334743 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1517970517339)^758985258669 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1517970517339)^505990172446 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 1517970517339)^137997319758 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 9851 := Nat.prime_eq_prime_of_dvd_pow hq prime_9851 hd
            subst q
            change (2 : ZMod 1517970517339)^154093038 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2334743 := Nat.prime_eq_prime_of_dvd_pow hq prime_2334743 hd
            subst q
            change (2 : ZMod 1517970517339)^650166 ≠ 1
            reduce_mod_char
            decide

theorem prime_1520255228939 : Nat.Prime 1520255228939 := by
  apply lucas_primality 1520255228939 (2 : ZMod 1520255228939)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1520255228939 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((43 : ℕ)^1 * ((71 : ℕ)^1 * ((229 : ℕ)^1 * ((57223 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1520255228939)^760127614469 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 1520255228939)^80013433102 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (2 : ZMod 1520255228939)^35354772766 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
            subst q
            change (2 : ZMod 1520255228939)^21412045478 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 229 := Nat.prime_eq_prime_of_dvd_pow hq prime_229 hd
              subst q
              change (2 : ZMod 1520255228939)^6638669122 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 57223 := Nat.prime_eq_prime_of_dvd_pow hq prime_57223 hd
              subst q
              change (2 : ZMod 1520255228939)^26567206 ≠ 1
              reduce_mod_char
              decide

theorem prime_1538360356961 : Nat.Prime 1538360356961 := by
  apply lucas_primality 1538360356961 (3 : ZMod 1538360356961)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1538360356961 - 1 = (2 : ℕ)^5 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((2767 : ℕ)^1 * ((496399 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1538360356961)^769180178480 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 1538360356961)^307672071392 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 1538360356961)^219765765280 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2767 := Nat.prime_eq_prime_of_dvd_pow hq prime_2767 hd
            subst q
            change (3 : ZMod 1538360356961)^555966880 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 496399 := Nat.prime_eq_prime_of_dvd_pow hq prime_496399 hd
            subst q
            change (3 : ZMod 1538360356961)^3099040 ≠ 1
            reduce_mod_char
            decide

theorem prime_1546166811307 : Nat.Prime 1546166811307 := by
  apply lucas_primality 1546166811307 (2 : ZMod 1546166811307)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1546166811307 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((47 : ℕ)^1 * ((421758541 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1546166811307)^773083405653 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1546166811307)^515388937102 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 1546166811307)^118935908562 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
            subst q
            change (2 : ZMod 1546166811307)^32897166198 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 421758541 := Nat.prime_eq_prime_of_dvd_pow hq prime_421758541 hd
            subst q
            change (2 : ZMod 1546166811307)^3666 ≠ 1
            reduce_mod_char
            decide

theorem prime_1586874322951 : Nat.Prime 1586874322951 := by
  apply lucas_primality 1586874322951 (11 : ZMod 1586874322951)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1586874322951 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((7 : ℕ)^1 * ((131 : ℕ)^1 * ((347 : ℕ)^1 * ((33247 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 1586874322951)^793437161475 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 1586874322951)^528958107650 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 1586874322951)^317374864590 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (11 : ZMod 1586874322951)^226696331850 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
              subst q
              change (11 : ZMod 1586874322951)^12113544450 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 347 := Nat.prime_eq_prime_of_dvd_pow hq prime_347 hd
                subst q
                change (11 : ZMod 1586874322951)^4573124850 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 33247 := Nat.prime_eq_prime_of_dvd_pow hq prime_33247 hd
                subst q
                change (11 : ZMod 1586874322951)^47729850 ≠ 1
                reduce_mod_char
                decide

theorem prime_1629503475571 : Nat.Prime 1629503475571 := by
  apply lucas_primality 1629503475571 (3 : ZMod 1629503475571)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1629503475571 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((28433 : ℕ)^1 * ((636781 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1629503475571)^814751737785 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1629503475571)^543167825190 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 1629503475571)^325900695114 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 28433 := Nat.prime_eq_prime_of_dvd_pow hq prime_28433 hd
            subst q
            change (3 : ZMod 1629503475571)^57310290 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 636781 := Nat.prime_eq_prime_of_dvd_pow hq prime_636781 hd
            subst q
            change (3 : ZMod 1629503475571)^2558970 ≠ 1
            reduce_mod_char
            decide

theorem prime_1636024758923 : Nat.Prime 1636024758923 := by
  apply lucas_primality 1636024758923 (2 : ZMod 1636024758923)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1636024758923 - 1 = (2 : ℕ)^1 * ((109 : ℕ)^1 * ((173 : ℕ)^1 * ((43379773 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1636024758923)^818012379461 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
        subst q
        change (2 : ZMod 1636024758923)^15009401458 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
          subst q
          change (2 : ZMod 1636024758923)^9456790514 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 43379773 := Nat.prime_eq_prime_of_dvd_pow hq prime_43379773 hd
          subst q
          change (2 : ZMod 1636024758923)^37714 ≠ 1
          reduce_mod_char
          decide

theorem prime_1649194241353 : Nat.Prime 1649194241353 := by
  apply lucas_primality 1649194241353 (5 : ZMod 1649194241353)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1649194241353 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((113 : ℕ)^1 * ((199 : ℕ)^1 * ((436547 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1649194241353)^824597120676 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1649194241353)^549731413784 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 1649194241353)^235599177336 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
            subst q
            change (5 : ZMod 1649194241353)^14594639304 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 199 := Nat.prime_eq_prime_of_dvd_pow hq prime_199 hd
              subst q
              change (5 : ZMod 1649194241353)^8287408248 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 436547 := Nat.prime_eq_prime_of_dvd_pow hq prime_436547 hd
              subst q
              change (5 : ZMod 1649194241353)^3777816 ≠ 1
              reduce_mod_char
              decide

theorem prime_1677100110857 : Nat.Prime 1677100110857 := by
  apply lucas_primality 1677100110857 (3 : ZMod 1677100110857)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1677100110857 - 1 = (2 : ℕ)^3 * ((31 : ℕ)^1 * ((83 : ℕ)^1 * ((4111 : ℕ)^1 * ((19819 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1677100110857)^838550055428 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (3 : ZMod 1677100110857)^54100003576 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
          subst q
          change (3 : ZMod 1677100110857)^20206025432 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 4111 := Nat.prime_eq_prime_of_dvd_pow hq prime_4111 hd
            subst q
            change (3 : ZMod 1677100110857)^407954296 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 19819 := Nat.prime_eq_prime_of_dvd_pow hq prime_19819 hd
            subst q
            change (3 : ZMod 1677100110857)^84620824 ≠ 1
            reduce_mod_char
            decide

theorem prime_1715257439209 : Nat.Prime 1715257439209 := by
  apply lucas_primality 1715257439209 (13 : ZMod 1715257439209)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1715257439209 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^4 * ((17 : ℕ)^1 * ((155706013 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 1715257439209)^857628719604 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 1715257439209)^571752479736 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (13 : ZMod 1715257439209)^100897496424 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 155706013 := Nat.prime_eq_prime_of_dvd_pow hq prime_155706013 hd
          subst q
          change (13 : ZMod 1715257439209)^11016 ≠ 1
          reduce_mod_char
          decide

theorem prime_1745408611607 : Nat.Prime 1745408611607 := by
  apply lucas_primality 1745408611607 (5 : ZMod 1745408611607)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1745408611607 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((631 : ℕ)^1 * ((3917 : ℕ)^1 * ((32099 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1745408611607)^872704305803 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 1745408611607)^158673510146 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 631 := Nat.prime_eq_prime_of_dvd_pow hq prime_631 hd
          subst q
          change (5 : ZMod 1745408611607)^2766099226 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3917 := Nat.prime_eq_prime_of_dvd_pow hq prime_3917 hd
            subst q
            change (5 : ZMod 1745408611607)^445598318 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 32099 := Nat.prime_eq_prime_of_dvd_pow hq prime_32099 hd
            subst q
            change (5 : ZMod 1745408611607)^54375794 ≠ 1
            reduce_mod_char
            decide

theorem prime_1753129284139 : Nat.Prime 1753129284139 := by
  apply lucas_primality 1753129284139 (2 : ZMod 1753129284139)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1753129284139 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((227 : ℕ)^1 * ((313 : ℕ)^1 * ((1033 : ℕ)^1 * ((1327 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1753129284139)^876564642069 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1753129284139)^584376428046 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 227 := Nat.prime_eq_prime_of_dvd_pow hq prime_227 hd
          subst q
          change (2 : ZMod 1753129284139)^7723036494 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 313 := Nat.prime_eq_prime_of_dvd_pow hq prime_313 hd
            subst q
            change (2 : ZMod 1753129284139)^5601052026 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1033 := Nat.prime_eq_prime_of_dvd_pow hq prime_1033 hd
              subst q
              change (2 : ZMod 1753129284139)^1697124186 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1327 := Nat.prime_eq_prime_of_dvd_pow hq prime_1327 hd
              subst q
              change (2 : ZMod 1753129284139)^1321122294 ≠ 1
              reduce_mod_char
              decide

theorem prime_1771561000043 : Nat.Prime 1771561000043 := by
  apply lucas_primality 1771561000043 (2 : ZMod 1771561000043)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1771561000043 - 1 = (2 : ℕ)^1 * ((885780500021 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1771561000043)^885780500021 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 885780500021 := Nat.prime_eq_prime_of_dvd_pow hq prime_885780500021 hd
      subst q
      change (2 : ZMod 1771561000043)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_1782654604397 : Nat.Prime 1782654604397 := by
  apply lucas_primality 1782654604397 (2 : ZMod 1782654604397)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1782654604397 - 1 = (2 : ℕ)^2 * ((341813 : ℕ)^1 * ((1303823 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1782654604397)^891327302198 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 341813 := Nat.prime_eq_prime_of_dvd_pow hq prime_341813 hd
        subst q
        change (2 : ZMod 1782654604397)^5215292 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1303823 := Nat.prime_eq_prime_of_dvd_pow hq prime_1303823 hd
        subst q
        change (2 : ZMod 1782654604397)^1367252 ≠ 1
        reduce_mod_char
        decide

theorem prime_1859361383857 : Nat.Prime 1859361383857 := by
  apply lucas_primality 1859361383857 (5 : ZMod 1859361383857)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1859361383857 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((38736695497 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1859361383857)^929680691928 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1859361383857)^619787127952 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 38736695497 := Nat.prime_eq_prime_of_dvd_pow hq prime_38736695497 hd
        subst q
        change (5 : ZMod 1859361383857)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_1866150019427 : Nat.Prime 1866150019427 := by
  apply lucas_primality 1866150019427 (2 : ZMod 1866150019427)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1866150019427 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^2 * ((11 : ℕ)^1 * ((373 : ℕ)^1 * ((1459 : ℕ)^1 * ((3181 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1866150019427)^933075009713 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 1866150019427)^266592859918 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 1866150019427)^169650001766 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 373 := Nat.prime_eq_prime_of_dvd_pow hq prime_373 hd
            subst q
            change (2 : ZMod 1866150019427)^5003083162 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1459 := Nat.prime_eq_prime_of_dvd_pow hq prime_1459 hd
              subst q
              change (2 : ZMod 1866150019427)^1279061014 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 3181 := Nat.prime_eq_prime_of_dvd_pow hq prime_3181 hd
              subst q
              change (2 : ZMod 1866150019427)^586655146 ≠ 1
              reduce_mod_char
              decide

theorem prime_1870414552177 : Nat.Prime 1870414552177 := by
  apply lucas_primality 1870414552177 (5 : ZMod 1870414552177)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1870414552177 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((31 : ℕ)^1 * ((1201 : ℕ)^1 * ((1046627 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1870414552177)^935207276088 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1870414552177)^623471517392 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (5 : ZMod 1870414552177)^60335953296 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1201 := Nat.prime_eq_prime_of_dvd_pow hq prime_1201 hd
            subst q
            change (5 : ZMod 1870414552177)^1557380976 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1046627 := Nat.prime_eq_prime_of_dvd_pow hq prime_1046627 hd
            subst q
            change (5 : ZMod 1870414552177)^1787088 ≠ 1
            reduce_mod_char
            decide

theorem prime_1878288356761 : Nat.Prime 1878288356761 := by
  apply lucas_primality 1878288356761 (19 : ZMod 1878288356761)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1878288356761 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((541 : ℕ)^1 * ((28932353 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 1878288356761)^939144178380 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 1878288356761)^626096118920 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (19 : ZMod 1878288356761)^375657671352 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 541 := Nat.prime_eq_prime_of_dvd_pow hq prime_541 hd
            subst q
            change (19 : ZMod 1878288356761)^3471882360 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 28932353 := Nat.prime_eq_prime_of_dvd_pow hq prime_28932353 hd
            subst q
            change (19 : ZMod 1878288356761)^64920 ≠ 1
            reduce_mod_char
            decide

theorem prime_1880437615499 : Nat.Prime 1880437615499 := by
  apply lucas_primality 1880437615499 (2 : ZMod 1880437615499)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1880437615499 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((71 : ℕ)^1 * ((233 : ℕ)^1 * ((4371911 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1880437615499)^940218807749 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 1880437615499)^144649047346 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
          subst q
          change (2 : ZMod 1880437615499)^26485036838 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
            subst q
            change (2 : ZMod 1880437615499)^8070547706 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 4371911 := Nat.prime_eq_prime_of_dvd_pow hq prime_4371911 hd
            subst q
            change (2 : ZMod 1880437615499)^430118 ≠ 1
            reduce_mod_char
            decide

theorem prime_1909346287447 : Nat.Prime 1909346287447 := by
  apply lucas_primality 1909346287447 (3 : ZMod 1909346287447)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1909346287447 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((13 : ℕ)^1 * ((8159599519 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1909346287447)^954673143723 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1909346287447)^636448762482 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 1909346287447)^146872791342 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 8159599519 := Nat.prime_eq_prime_of_dvd_pow hq prime_8159599519 hd
          subst q
          change (3 : ZMod 1909346287447)^234 ≠ 1
          reduce_mod_char
          decide

theorem prime_1922431170221 : Nat.Prime 1922431170221 := by
  apply lucas_primality 1922431170221 (2 : ZMod 1922431170221)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1922431170221 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((557 : ℕ)^1 * ((15688193 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1922431170221)^961215585110 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 1922431170221)^384486234044 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 1922431170221)^174766470020 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 557 := Nat.prime_eq_prime_of_dvd_pow hq prime_557 hd
            subst q
            change (2 : ZMod 1922431170221)^3451402460 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 15688193 := Nat.prime_eq_prime_of_dvd_pow hq prime_15688193 hd
            subst q
            change (2 : ZMod 1922431170221)^122540 ≠ 1
            reduce_mod_char
            decide

theorem prime_1931902663891 : Nat.Prime 1931902663891 := by
  apply lucas_primality 1931902663891 (3 : ZMod 1931902663891)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1931902663891 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((317 : ℕ)^1 * ((953 : ℕ)^1 * ((12539 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1931902663891)^965951331945 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1931902663891)^643967554630 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 1931902663891)^386380532778 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (3 : ZMod 1931902663891)^113641333170 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 317 := Nat.prime_eq_prime_of_dvd_pow hq prime_317 hd
              subst q
              change (3 : ZMod 1931902663891)^6094330170 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 953 := Nat.prime_eq_prime_of_dvd_pow hq prime_953 hd
                subst q
                change (3 : ZMod 1931902663891)^2027180130 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 12539 := Nat.prime_eq_prime_of_dvd_pow hq prime_12539 hd
                subst q
                change (3 : ZMod 1931902663891)^154071510 ≠ 1
                reduce_mod_char
                decide

theorem prime_1955873567033 : Nat.Prime 1955873567033 := by
  apply lucas_primality 1955873567033 (3 : ZMod 1955873567033)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1955873567033 - 1 = (2 : ℕ)^3 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((186771731 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1955873567033)^977936783516 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 1955873567033)^279410509576 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 1955873567033)^177806687912 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (3 : ZMod 1955873567033)^115051386296 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 186771731 := Nat.prime_eq_prime_of_dvd_pow hq prime_186771731 hd
            subst q
            change (3 : ZMod 1955873567033)^10472 ≠ 1
            reduce_mod_char
            decide

theorem prime_1971379557649 : Nat.Prime 1971379557649 := by
  apply lucas_primality 1971379557649 (7 : ZMod 1971379557649)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1971379557649 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((239 : ℕ)^1 * ((57280903 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1971379557649)^985689778824 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 1971379557649)^657126519216 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 239 := Nat.prime_eq_prime_of_dvd_pow hq prime_239 hd
          subst q
          change (7 : ZMod 1971379557649)^8248450032 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 57280903 := Nat.prime_eq_prime_of_dvd_pow hq prime_57280903 hd
          subst q
          change (7 : ZMod 1971379557649)^34416 ≠ 1
          reduce_mod_char
          decide

theorem prime_1973822685187 : Nat.Prime 1973822685187 := by
  apply lucas_primality 1973822685187 (2 : ZMod 1973822685187)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1973822685187 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((33937 : ℕ)^1 * ((881233 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1973822685187)^986911342593 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1973822685187)^657940895062 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 1973822685187)^179438425926 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 33937 := Nat.prime_eq_prime_of_dvd_pow hq prime_33937 hd
            subst q
            change (2 : ZMod 1973822685187)^58161378 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 881233 := Nat.prime_eq_prime_of_dvd_pow hq prime_881233 hd
            subst q
            change (2 : ZMod 1973822685187)^2239842 ≠ 1
            reduce_mod_char
            decide

theorem prime_1981521999859 : Nat.Prime 1981521999859 := by
  apply lucas_primality 1981521999859 (2 : ZMod 1981521999859)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1981521999859 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((330253666643 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1981521999859)^990760999929 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1981521999859)^660507333286 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 330253666643 := Nat.prime_eq_prime_of_dvd_pow hq prime_330253666643 hd
        subst q
        change (2 : ZMod 1981521999859)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_2017074259313 : Nat.Prime 2017074259313 := by
  apply lucas_primality 2017074259313 (5 : ZMod 2017074259313)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2017074259313 - 1 = (2 : ℕ)^4 * ((7 : ℕ)^1 * ((137 : ℕ)^1 * ((449 : ℕ)^1 * ((292777 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2017074259313)^1008537129656 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 2017074259313)^288153465616 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
          subst q
          change (5 : ZMod 2017074259313)^14723169776 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 449 := Nat.prime_eq_prime_of_dvd_pow hq prime_449 hd
            subst q
            change (5 : ZMod 2017074259313)^4492370288 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 292777 := Nat.prime_eq_prime_of_dvd_pow hq prime_292777 hd
            subst q
            change (5 : ZMod 2017074259313)^6889456 ≠ 1
            reduce_mod_char
            decide

theorem prime_2029658534861 : Nat.Prime 2029658534861 := by
  apply lucas_primality 2029658534861 (2 : ZMod 2029658534861)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2029658534861 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((29 : ℕ)^1 * ((318128297 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2029658534861)^1014829267430 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 2029658534861)^405931706972 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 2029658534861)^184514412260 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (2 : ZMod 2029658534861)^69988225340 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 318128297 := Nat.prime_eq_prime_of_dvd_pow hq prime_318128297 hd
            subst q
            change (2 : ZMod 2029658534861)^6380 ≠ 1
            reduce_mod_char
            decide

theorem prime_2055950949643 : Nat.Prime 2055950949643 := by
  apply lucas_primality 2055950949643 (5 : ZMod 2055950949643)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2055950949643 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((193 : ℕ)^1 * ((409 : ℕ)^1 * ((228469 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2055950949643)^1027975474821 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 2055950949643)^685316983214 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (5 : ZMod 2055950949643)^108207944718 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
            subst q
            change (5 : ZMod 2055950949643)^10652595594 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 409 := Nat.prime_eq_prime_of_dvd_pow hq prime_409 hd
              subst q
              change (5 : ZMod 2055950949643)^5026774938 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 228469 := Nat.prime_eq_prime_of_dvd_pow hq prime_228469 hd
              subst q
              change (5 : ZMod 2055950949643)^8998818 ≠ 1
              reduce_mod_char
              decide

theorem prime_2081951752631 : Nat.Prime 2081951752631 := by
  apply lucas_primality 2081951752631 (7 : ZMod 2081951752631)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2081951752631 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((208195175263 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2081951752631)^1040975876315 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 2081951752631)^416390350526 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 208195175263 := Nat.prime_eq_prime_of_dvd_pow hq prime_208195175263 hd
        subst q
        change (7 : ZMod 2081951752631)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_2194972623941 : Nat.Prime 2194972623941 := by
  apply lucas_primality 2194972623941 (2 : ZMod 2194972623941)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2194972623941 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((1054373 : ℕ)^1 * ((104089 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2194972623941)^1097486311970 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 2194972623941)^438994524788 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1054373 := Nat.prime_eq_prime_of_dvd_pow hq prime_1054373 hd
          subst q
          change (2 : ZMod 2194972623941)^2081780 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 104089 := Nat.prime_eq_prime_of_dvd_pow hq prime_104089 hd
          subst q
          change (2 : ZMod 2194972623941)^21087460 ≠ 1
          reduce_mod_char
          decide

theorem prime_2212137531521 : Nat.Prime 2212137531521 := by
  apply lucas_primality 2212137531521 (3 : ZMod 2212137531521)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2212137531521 - 1 = (2 : ℕ)^7 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((127 : ℕ)^1 * ((271 : ℕ)^1 * ((14347 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2212137531521)^1106068765760 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 2212137531521)^442427506304 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 2212137531521)^316019647360 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
            subst q
            change (3 : ZMod 2212137531521)^17418405760 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 271 := Nat.prime_eq_prime_of_dvd_pow hq prime_271 hd
              subst q
              change (3 : ZMod 2212137531521)^8162869120 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 14347 := Nat.prime_eq_prime_of_dvd_pow hq prime_14347 hd
              subst q
              change (3 : ZMod 2212137531521)^154188160 ≠ 1
              reduce_mod_char
              decide

theorem prime_2225593623437 : Nat.Prime 2225593623437 := by
  apply lucas_primality 2225593623437 (2 : ZMod 2225593623437)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2225593623437 - 1 = (2 : ℕ)^2 * ((556398405859 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2225593623437)^1112796811718 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 556398405859 := Nat.prime_eq_prime_of_dvd_pow hq prime_556398405859 hd
      subst q
      change (2 : ZMod 2225593623437)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_2237580049009 : Nat.Prime 2237580049009 := by
  apply lucas_primality 2237580049009 (13 : ZMod 2237580049009)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2237580049009 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((2742132413 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 2237580049009)^1118790024504 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 2237580049009)^745860016336 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (13 : ZMod 2237580049009)^131622355824 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2742132413 := Nat.prime_eq_prime_of_dvd_pow hq prime_2742132413 hd
          subst q
          change (13 : ZMod 2237580049009)^816 ≠ 1
          reduce_mod_char
          decide

theorem prime_2298564522557 : Nat.Prime 2298564522557 := by
  apply lucas_primality 2298564522557 (2 : ZMod 2298564522557)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2298564522557 - 1 = (2 : ℕ)^2 * ((574641130639 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2298564522557)^1149282261278 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 574641130639 := Nat.prime_eq_prime_of_dvd_pow hq prime_574641130639 hd
      subst q
      change (2 : ZMod 2298564522557)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_2313060765661 : Nat.Prime 2313060765661 := by
  apply lucas_primality 2313060765661 (10 : ZMod 2313060765661)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2313060765661 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((19267 : ℕ)^1 * ((39233 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 2313060765661)^1156530382830 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 2313060765661)^771020255220 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 2313060765661)^462612153132 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (10 : ZMod 2313060765661)^136062397980 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 19267 := Nat.prime_eq_prime_of_dvd_pow hq prime_19267 hd
              subst q
              change (10 : ZMod 2313060765661)^120052980 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 39233 := Nat.prime_eq_prime_of_dvd_pow hq prime_39233 hd
              subst q
              change (10 : ZMod 2313060765661)^58957020 ≠ 1
              reduce_mod_char
              decide

theorem prime_2425197117293 : Nat.Prime 2425197117293 := by
  apply lucas_primality 2425197117293 (2 : ZMod 2425197117293)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2425197117293 - 1 = (2 : ℕ)^2 * ((606299279323 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2425197117293)^1212598558646 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 606299279323 := Nat.prime_eq_prime_of_dvd_pow hq prime_606299279323 hd
      subst q
      change (2 : ZMod 2425197117293)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_2436396322819 : Nat.Prime 2436396322819 := by
  apply lucas_primality 2436396322819 (2 : ZMod 2436396322819)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2436396322819 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((307 : ℕ)^1 * ((433 : ℕ)^1 * ((179689 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2436396322819)^1218198161409 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2436396322819)^812132107606 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 2436396322819)^143317430754 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 307 := Nat.prime_eq_prime_of_dvd_pow hq prime_307 hd
            subst q
            change (2 : ZMod 2436396322819)^7936144374 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 433 := Nat.prime_eq_prime_of_dvd_pow hq prime_433 hd
              subst q
              change (2 : ZMod 2436396322819)^5626781346 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 179689 := Nat.prime_eq_prime_of_dvd_pow hq prime_179689 hd
              subst q
              change (2 : ZMod 2436396322819)^13558962 ≠ 1
              reduce_mod_char
              decide

theorem prime_2473878907259 : Nat.Prime 2473878907259 := by
  apply lucas_primality 2473878907259 (2 : ZMod 2473878907259)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2473878907259 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((112449041239 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2473878907259)^1236939453629 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 2473878907259)^224898082478 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 112449041239 := Nat.prime_eq_prime_of_dvd_pow hq prime_112449041239 hd
        subst q
        change (2 : ZMod 2473878907259)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_2487431953231 : Nat.Prime 2487431953231 := by
  apply lucas_primality 2487431953231 (11 : ZMod 2487431953231)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2487431953231 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((41 : ℕ)^1 * ((947 : ℕ)^1 * ((305069 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 2487431953231)^1243715976615 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 2487431953231)^829143984410 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 2487431953231)^497486390646 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (11 : ZMod 2487431953231)^355347421890 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
              subst q
              change (11 : ZMod 2487431953231)^60669072030 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 947 := Nat.prime_eq_prime_of_dvd_pow hq prime_947 hd
                subst q
                change (11 : ZMod 2487431953231)^2626644090 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 305069 := Nat.prime_eq_prime_of_dvd_pow hq prime_305069 hd
                subst q
                change (11 : ZMod 2487431953231)^8153670 ≠ 1
                reduce_mod_char
                decide

theorem prime_2497821510889 : Nat.Prime 2497821510889 := by
  apply lucas_primality 2497821510889 (7 : ZMod 2497821510889)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2497821510889 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((23 : ℕ)^1 * ((31 : ℕ)^1 * ((457 : ℕ)^1 * ((9679 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2497821510889)^1248910755444 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 2497821510889)^832607170296 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (7 : ZMod 2497821510889)^227074682808 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (7 : ZMod 2497821510889)^108600935256 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
              subst q
              change (7 : ZMod 2497821510889)^80574887448 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 457 := Nat.prime_eq_prime_of_dvd_pow hq prime_457 hd
                subst q
                change (7 : ZMod 2497821510889)^5465692584 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 9679 := Nat.prime_eq_prime_of_dvd_pow hq prime_9679 hd
                subst q
                change (7 : ZMod 2497821510889)^258066072 ≠ 1
                reduce_mod_char
                decide

theorem prime_2504030641193 : Nat.Prime 2504030641193 := by
  apply lucas_primality 2504030641193 (3 : ZMod 2504030641193)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2504030641193 - 1 = (2 : ℕ)^3 * ((37 : ℕ)^1 * ((181 : ℕ)^1 * ((46737917 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2504030641193)^1252015320596 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (3 : ZMod 2504030641193)^67676503816 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 181 := Nat.prime_eq_prime_of_dvd_pow hq prime_181 hd
          subst q
          change (3 : ZMod 2504030641193)^13834423432 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 46737917 := Nat.prime_eq_prime_of_dvd_pow hq prime_46737917 hd
          subst q
          change (3 : ZMod 2504030641193)^53576 ≠ 1
          reduce_mod_char
          decide

theorem prime_2557708574791 : Nat.Prime 2557708574791 := by
  apply lucas_primality 2557708574791 (3 : ZMod 2557708574791)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2557708574791 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((1747 : ℕ)^1 * ((2293 : ℕ)^1 * ((21283 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2557708574791)^1278854287395 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 2557708574791)^852569524930 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 2557708574791)^511541714958 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1747 := Nat.prime_eq_prime_of_dvd_pow hq prime_1747 hd
            subst q
            change (3 : ZMod 2557708574791)^1464057570 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 2293 := Nat.prime_eq_prime_of_dvd_pow hq prime_2293 hd
              subst q
              change (3 : ZMod 2557708574791)^1115442030 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 21283 := Nat.prime_eq_prime_of_dvd_pow hq prime_21283 hd
              subst q
              change (3 : ZMod 2557708574791)^120176130 ≠ 1
              reduce_mod_char
              decide

theorem prime_2563231525199 : Nat.Prime 2563231525199 := by
  apply lucas_primality 2563231525199 (7 : ZMod 2563231525199)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2563231525199 - 1 = (2 : ℕ)^1 * ((41 : ℕ)^1 * ((53 : ℕ)^1 * ((59 : ℕ)^1 * ((9996457 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2563231525199)^1281615762599 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
        subst q
        change (7 : ZMod 2563231525199)^62517842078 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (7 : ZMod 2563231525199)^48362858966 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
            subst q
            change (7 : ZMod 2563231525199)^43444602122 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 9996457 := Nat.prime_eq_prime_of_dvd_pow hq prime_9996457 hd
            subst q
            change (7 : ZMod 2563231525199)^256414 ≠ 1
            reduce_mod_char
            decide

theorem prime_2565164201783 : Nat.Prime 2565164201783 := by
  apply lucas_primality 2565164201783 (5 : ZMod 2565164201783)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2565164201783 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((52223 : ℕ)^1 * ((269887 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2565164201783)^1282582100891 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 2565164201783)^366452028826 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (5 : ZMod 2565164201783)^197320323214 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 52223 := Nat.prime_eq_prime_of_dvd_pow hq prime_52223 hd
            subst q
            change (5 : ZMod 2565164201783)^49119434 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 269887 := Nat.prime_eq_prime_of_dvd_pow hq prime_269887 hd
            subst q
            change (5 : ZMod 2565164201783)^9504586 ≠ 1
            reduce_mod_char
            decide

theorem prime_2570823185929 : Nat.Prime 2570823185929 := by
  apply lucas_primality 2570823185929 (7 : ZMod 2570823185929)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2570823185929 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((137 : ℕ)^1 * ((6073 : ℕ)^1 * ((128747 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2570823185929)^1285411592964 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 2570823185929)^856941061976 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
          subst q
          change (7 : ZMod 2570823185929)^18765132744 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 6073 := Nat.prime_eq_prime_of_dvd_pow hq prime_6073 hd
            subst q
            change (7 : ZMod 2570823185929)^423320136 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 128747 := Nat.prime_eq_prime_of_dvd_pow hq prime_128747 hd
            subst q
            change (7 : ZMod 2570823185929)^19968024 ≠ 1
            reduce_mod_char
            decide

theorem prime_2592345723659 : Nat.Prime 2592345723659 := by
  apply lucas_primality 2592345723659 (2 : ZMod 2592345723659)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2592345723659 - 1 = (2 : ℕ)^1 * ((352123 : ℕ)^1 * ((3681023 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2592345723659)^1296172861829 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 352123 := Nat.prime_eq_prime_of_dvd_pow hq prime_352123 hd
        subst q
        change (2 : ZMod 2592345723659)^7362046 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3681023 := Nat.prime_eq_prime_of_dvd_pow hq prime_3681023 hd
        subst q
        change (2 : ZMod 2592345723659)^704246 ≠ 1
        reduce_mod_char
        decide

theorem prime_2595973723619 : Nat.Prime 2595973723619 := by
  apply lucas_primality 2595973723619 (2 : ZMod 2595973723619)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2595973723619 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((23 : ℕ)^1 * ((3739 : ℕ)^1 * ((1372127 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2595973723619)^1297986861809 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 2595973723619)^235997611238 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 2595973723619)^112868422766 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3739 := Nat.prime_eq_prime_of_dvd_pow hq prime_3739 hd
            subst q
            change (2 : ZMod 2595973723619)^694296262 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1372127 := Nat.prime_eq_prime_of_dvd_pow hq prime_1372127 hd
            subst q
            change (2 : ZMod 2595973723619)^1891934 ≠ 1
            reduce_mod_char
            decide

theorem prime_2626124922653 : Nat.Prime 2626124922653 := by
  apply lucas_primality 2626124922653 (2 : ZMod 2626124922653)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2626124922653 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((2753 : ℕ)^1 * ((3097123 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2626124922653)^1313062461326 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 2626124922653)^375160703236 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 2626124922653)^238738629332 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2753 := Nat.prime_eq_prime_of_dvd_pow hq prime_2753 hd
            subst q
            change (2 : ZMod 2626124922653)^953913884 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3097123 := Nat.prime_eq_prime_of_dvd_pow hq prime_3097123 hd
            subst q
            change (2 : ZMod 2626124922653)^847924 ≠ 1
            reduce_mod_char
            decide

theorem prime_2629333798577 : Nat.Prime 2629333798577 := by
  apply lucas_primality 2629333798577 (3 : ZMod 2629333798577)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2629333798577 - 1 = (2 : ℕ)^4 * ((757 : ℕ)^1 * ((217085023 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2629333798577)^1314666899288 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 757 := Nat.prime_eq_prime_of_dvd_pow hq prime_757 hd
        subst q
        change (3 : ZMod 2629333798577)^3473360368 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 217085023 := Nat.prime_eq_prime_of_dvd_pow hq prime_217085023 hd
        subst q
        change (3 : ZMod 2629333798577)^12112 ≠ 1
        reduce_mod_char
        decide

theorem prime_2633495908249 : Nat.Prime 2633495908249 := by
  apply lucas_primality 2633495908249 (7 : ZMod 2633495908249)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2633495908249 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((347 : ℕ)^1 * ((105407297 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2633495908249)^1316747954124 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 2633495908249)^877831969416 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 347 := Nat.prime_eq_prime_of_dvd_pow hq prime_347 hd
          subst q
          change (7 : ZMod 2633495908249)^7589325384 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 105407297 := Nat.prime_eq_prime_of_dvd_pow hq prime_105407297 hd
          subst q
          change (7 : ZMod 2633495908249)^24984 ≠ 1
          reduce_mod_char
          decide

theorem prime_2699554153039 : Nat.Prime 2699554153039 := by
  apply lucas_primality 2699554153039 (3 : ZMod 2699554153039)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2699554153039 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((86311 : ℕ)^1 * ((5212843 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2699554153039)^1349777076519 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 2699554153039)^899851384346 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 86311 := Nat.prime_eq_prime_of_dvd_pow hq prime_86311 hd
          subst q
          change (3 : ZMod 2699554153039)^31277058 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 5212843 := Nat.prime_eq_prime_of_dvd_pow hq prime_5212843 hd
          subst q
          change (3 : ZMod 2699554153039)^517866 ≠ 1
          reduce_mod_char
          decide

theorem prime_2704670419513 : Nat.Prime 2704670419513 := by
  apply lucas_primality 2704670419513 (5 : ZMod 2704670419513)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2704670419513 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((112694600813 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2704670419513)^1352335209756 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 2704670419513)^901556806504 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 112694600813 := Nat.prime_eq_prime_of_dvd_pow hq prime_112694600813 hd
        subst q
        change (5 : ZMod 2704670419513)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_2779630546753 : Nat.Prime 2779630546753 := by
  apply lucas_primality 2779630546753 (5 : ZMod 2779630546753)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2779630546753 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^2 * ((131 : ℕ)^1 * ((4679 : ℕ)^1 * ((7873 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2779630546753)^1389815273376 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 2779630546753)^926543515584 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
          subst q
          change (5 : ZMod 2779630546753)^21218553792 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 4679 := Nat.prime_eq_prime_of_dvd_pow hq prime_4679 hd
            subst q
            change (5 : ZMod 2779630546753)^594065088 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 7873 := Nat.prime_eq_prime_of_dvd_pow hq prime_7873 hd
            subst q
            change (5 : ZMod 2779630546753)^353058624 ≠ 1
            reduce_mod_char
            decide

theorem prime_2801231335543 : Nat.Prime 2801231335543 := by
  apply lucas_primality 2801231335543 (3 : ZMod 2801231335543)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2801231335543 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((157 : ℕ)^1 * ((2973706301 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2801231335543)^1400615667771 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 2801231335543)^933743778514 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
          subst q
          change (3 : ZMod 2801231335543)^17842237806 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2973706301 := Nat.prime_eq_prime_of_dvd_pow hq prime_2973706301 hd
          subst q
          change (3 : ZMod 2801231335543)^942 ≠ 1
          reduce_mod_char
          decide

theorem prime_2813319589519 : Nat.Prime 2813319589519 := by
  apply lucas_primality 2813319589519 (6 : ZMod 2813319589519)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2813319589519 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((18973 : ℕ)^1 * ((2745929 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 2813319589519)^1406659794759 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 2813319589519)^937773196506 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 18973 := Nat.prime_eq_prime_of_dvd_pow hq prime_18973 hd
          subst q
          change (6 : ZMod 2813319589519)^148280166 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2745929 := Nat.prime_eq_prime_of_dvd_pow hq prime_2745929 hd
          subst q
          change (6 : ZMod 2813319589519)^1024542 ≠ 1
          reduce_mod_char
          decide

theorem prime_2839760855299 : Nat.Prime 2839760855299 := by
  apply lucas_primality 2839760855299 (2 : ZMod 2839760855299)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2839760855299 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((17 : ℕ)^1 * ((3093421411 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2839760855299)^1419880427649 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2839760855299)^946586951766 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 2839760855299)^167044756194 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3093421411 := Nat.prime_eq_prime_of_dvd_pow hq prime_3093421411 hd
          subst q
          change (2 : ZMod 2839760855299)^918 ≠ 1
          reduce_mod_char
          decide

theorem prime_2887738682329 : Nat.Prime 2887738682329 := by
  apply lucas_primality 2887738682329 (11 : ZMod 2887738682329)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2887738682329 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((349 : ℕ)^1 * ((739 : ℕ)^1 * ((155509 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 2887738682329)^1443869341164 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 2887738682329)^962579560776 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 349 := Nat.prime_eq_prime_of_dvd_pow hq prime_349 hd
          subst q
          change (11 : ZMod 2887738682329)^8274322872 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 739 := Nat.prime_eq_prime_of_dvd_pow hq prime_739 hd
            subst q
            change (11 : ZMod 2887738682329)^3907630152 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 155509 := Nat.prime_eq_prime_of_dvd_pow hq prime_155509 hd
            subst q
            change (11 : ZMod 2887738682329)^18569592 ≠ 1
            reduce_mod_char
            decide

theorem prime_2934363325073 : Nat.Prime 2934363325073 := by
  apply lucas_primality 2934363325073 (3 : ZMod 2934363325073)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2934363325073 - 1 = (2 : ℕ)^4 * ((183397707817 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2934363325073)^1467181662536 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 183397707817 := Nat.prime_eq_prime_of_dvd_pow hq prime_183397707817 hd
      subst q
      change (3 : ZMod 2934363325073)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_2985984000007 : Nat.Prime 2985984000007 := by
  apply lucas_primality 2985984000007 (5 : ZMod 2985984000007)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2985984000007 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((27107 : ℕ)^1 * ((2622749 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2985984000007)^1492992000003 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 2985984000007)^995328000002 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 2985984000007)^426569142858 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 27107 := Nat.prime_eq_prime_of_dvd_pow hq prime_27107 hd
            subst q
            change (5 : ZMod 2985984000007)^110155458 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2622749 := Nat.prime_eq_prime_of_dvd_pow hq prime_2622749 hd
            subst q
            change (5 : ZMod 2985984000007)^1138494 ≠ 1
            reduce_mod_char
            decide

theorem prime_3030486055001 : Nat.Prime 3030486055001 := by
  apply lucas_primality 3030486055001 (6 : ZMod 3030486055001)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3030486055001 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^4 * ((9013 : ℕ)^1 * ((67247 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 3030486055001)^1515243027500 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 3030486055001)^606097211000 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 9013 := Nat.prime_eq_prime_of_dvd_pow hq prime_9013 hd
          subst q
          change (6 : ZMod 3030486055001)^336235000 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 67247 := Nat.prime_eq_prime_of_dvd_pow hq prime_67247 hd
          subst q
          change (6 : ZMod 3030486055001)^45065000 ≠ 1
          reduce_mod_char
          decide

theorem prime_3049623344917 : Nat.Prime 3049623344917 := by
  apply lucas_primality 3049623344917 (5 : ZMod 3049623344917)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3049623344917 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((677 : ℕ)^1 * ((125128153 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3049623344917)^1524811672458 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 3049623344917)^1016541114972 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 677 := Nat.prime_eq_prime_of_dvd_pow hq prime_677 hd
          subst q
          change (5 : ZMod 3049623344917)^4504613508 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 125128153 := Nat.prime_eq_prime_of_dvd_pow hq prime_125128153 hd
          subst q
          change (5 : ZMod 3049623344917)^24372 ≠ 1
          reduce_mod_char
          decide

theorem prime_3059298090881 : Nat.Prime 3059298090881 := by
  apply lucas_primality 3059298090881 (3 : ZMod 3059298090881)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3059298090881 - 1 = (2 : ℕ)^7 * ((5 : ℕ)^1 * ((277 : ℕ)^1 * ((2113 : ℕ)^1 * ((8167 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3059298090881)^1529649045440 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 3059298090881)^611859618176 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 277 := Nat.prime_eq_prime_of_dvd_pow hq prime_277 hd
          subst q
          change (3 : ZMod 3059298090881)^11044397440 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2113 := Nat.prime_eq_prime_of_dvd_pow hq prime_2113 hd
            subst q
            change (3 : ZMod 3059298090881)^1447845760 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 8167 := Nat.prime_eq_prime_of_dvd_pow hq prime_8167 hd
            subst q
            change (3 : ZMod 3059298090881)^374592640 ≠ 1
            reduce_mod_char
            decide

theorem prime_3101707903127 : Nat.Prime 3101707903127 := by
  apply lucas_primality 3101707903127 (5 : ZMod 3101707903127)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3101707903127 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((83273 : ℕ)^1 * ((2660533 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3101707903127)^1550853951563 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 3101707903127)^443101129018 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 83273 := Nat.prime_eq_prime_of_dvd_pow hq prime_83273 hd
          subst q
          change (5 : ZMod 3101707903127)^37247462 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2660533 := Nat.prime_eq_prime_of_dvd_pow hq prime_2660533 hd
          subst q
          change (5 : ZMod 3101707903127)^1165822 ≠ 1
          reduce_mod_char
          decide

theorem prime_3138428376749 : Nat.Prime 3138428376749 := by
  apply lucas_primality 3138428376749 (3 : ZMod 3138428376749)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3138428376749 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((43 : ℕ)^1 * ((349 : ℕ)^1 * ((523 : ℕ)^1 * ((14281 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3138428376749)^1569214188374 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 3138428376749)^448346910964 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (3 : ZMod 3138428376749)^72986706436 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 349 := Nat.prime_eq_prime_of_dvd_pow hq prime_349 hd
            subst q
            change (3 : ZMod 3138428376749)^8992631452 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 523 := Nat.prime_eq_prime_of_dvd_pow hq prime_523 hd
              subst q
              change (3 : ZMod 3138428376749)^6000819076 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 14281 := Nat.prime_eq_prime_of_dvd_pow hq prime_14281 hd
              subst q
              change (3 : ZMod 3138428376749)^219762508 ≠ 1
              reduce_mod_char
              decide

theorem prime_3170719841087 : Nat.Prime 3170719841087 := by
  apply lucas_primality 3170719841087 (7 : ZMod 3170719841087)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3170719841087 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((29 : ℕ)^1 * ((53 : ℕ)^1 * ((109 : ℕ)^1 * ((1351853 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 3170719841087)^1585359920543 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 3170719841087)^452959977298 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (7 : ZMod 3170719841087)^109335166934 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
            subst q
            change (7 : ZMod 3170719841087)^59824902662 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
              subst q
              change (7 : ZMod 3170719841087)^29089172854 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1351853 := Nat.prime_eq_prime_of_dvd_pow hq prime_1351853 hd
              subst q
              change (7 : ZMod 3170719841087)^2345462 ≠ 1
              reduce_mod_char
              decide

theorem prime_3204462973697 : Nat.Prime 3204462973697 := by
  apply lucas_primality 3204462973697 (3 : ZMod 3204462973697)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3204462973697 - 1 = (2 : ℕ)^8 * ((19 : ℕ)^2 * ((191 : ℕ)^1 * ((379 : ℕ)^1 * ((479 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3204462973697)^1602231486848 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (3 : ZMod 3204462973697)^168655945984 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
          subst q
          change (3 : ZMod 3204462973697)^16777293056 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 379 := Nat.prime_eq_prime_of_dvd_pow hq prime_379 hd
            subst q
            change (3 : ZMod 3204462973697)^8455047424 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 479 := Nat.prime_eq_prime_of_dvd_pow hq prime_479 hd
            subst q
            change (3 : ZMod 3204462973697)^6689901824 ≠ 1
            reduce_mod_char
            decide

theorem prime_3297303959107 : Nat.Prime 3297303959107 := by
  apply lucas_primality 3297303959107 (2 : ZMod 3297303959107)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3297303959107 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((521 : ℕ)^1 * ((62047043 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3297303959107)^1648651979553 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3297303959107)^1099101319702 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 3297303959107)^193959056418 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 521 := Nat.prime_eq_prime_of_dvd_pow hq prime_521 hd
            subst q
            change (2 : ZMod 3297303959107)^6328798386 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 62047043 := Nat.prime_eq_prime_of_dvd_pow hq prime_62047043 hd
            subst q
            change (2 : ZMod 3297303959107)^53142 ≠ 1
            reduce_mod_char
            decide

theorem prime_3313904970301 : Nat.Prime 3313904970301 := by
  apply lucas_primality 3313904970301 (2 : ZMod 3313904970301)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3313904970301 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((101 : ℕ)^1 * ((109369801 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3313904970301)^1656952485150 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3313904970301)^1104634990100 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 3313904970301)^662780994060 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
            subst q
            change (2 : ZMod 3313904970301)^32810940300 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 109369801 := Nat.prime_eq_prime_of_dvd_pow hq prime_109369801 hd
            subst q
            change (2 : ZMod 3313904970301)^30300 ≠ 1
            reduce_mod_char
            decide

theorem prime_3462825991721 : Nat.Prime 3462825991721 := by
  apply lucas_primality 3462825991721 (3 : ZMod 3462825991721)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3462825991721 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((47 : ℕ)^1 * ((661 : ℕ)^1 * ((2786579 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3462825991721)^1731412995860 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 3462825991721)^692565198344 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (3 : ZMod 3462825991721)^73677148760 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 661 := Nat.prime_eq_prime_of_dvd_pow hq prime_661 hd
            subst q
            change (3 : ZMod 3462825991721)^5238768520 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2786579 := Nat.prime_eq_prime_of_dvd_pow hq prime_2786579 hd
            subst q
            change (3 : ZMod 3462825991721)^1242680 ≠ 1
            reduce_mod_char
            decide

theorem prime_3528056148413 : Nat.Prime 3528056148413 := by
  apply lucas_primality 3528056148413 (2 : ZMod 3528056148413)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3528056148413 - 1 = (2 : ℕ)^2 * ((31 : ℕ)^1 * ((37 : ℕ)^1 * ((768974749 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3528056148413)^1764028074206 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (2 : ZMod 3528056148413)^113808262852 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (2 : ZMod 3528056148413)^95352868876 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 768974749 := Nat.prime_eq_prime_of_dvd_pow hq prime_768974749 hd
          subst q
          change (2 : ZMod 3528056148413)^4588 ≠ 1
          reduce_mod_char
          decide

theorem prime_3558796789621 : Nat.Prime 3558796789621 := by
  apply lucas_primality 3558796789621 (2 : ZMod 3558796789621)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3558796789621 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((59313279827 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3558796789621)^1779398394810 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3558796789621)^1186265596540 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 3558796789621)^711759357924 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 59313279827 := Nat.prime_eq_prime_of_dvd_pow hq prime_59313279827 hd
          subst q
          change (2 : ZMod 3558796789621)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_3617175874789 : Nat.Prime 3617175874789 := by
  apply lucas_primality 3617175874789 (2 : ZMod 3617175874789)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3617175874789 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((7 : ℕ)^2 * ((683517739 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3617175874789)^1808587937394 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3617175874789)^1205725291596 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 3617175874789)^516739410684 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 683517739 := Nat.prime_eq_prime_of_dvd_pow hq prime_683517739 hd
          subst q
          change (2 : ZMod 3617175874789)^5292 ≠ 1
          reduce_mod_char
          decide

theorem prime_3635215077379 : Nat.Prime 3635215077379 := by
  apply lucas_primality 3635215077379 (2 : ZMod 3635215077379)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3635215077379 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((102251 : ℕ)^1 * ((5925313 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3635215077379)^1817607538689 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3635215077379)^1211738359126 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 102251 := Nat.prime_eq_prime_of_dvd_pow hq prime_102251 hd
          subst q
          change (2 : ZMod 3635215077379)^35551878 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 5925313 := Nat.prime_eq_prime_of_dvd_pow hq prime_5925313 hd
          subst q
          change (2 : ZMod 3635215077379)^613506 ≠ 1
          reduce_mod_char
          decide

theorem prime_3785243996011 : Nat.Prime 3785243996011 := by
  apply lucas_primality 3785243996011 (2 : ZMod 3785243996011)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3785243996011 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((17 : ℕ)^2 * ((881 : ℕ)^1 * ((495563 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3785243996011)^1892621998005 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3785243996011)^1261747998670 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 3785243996011)^757048799202 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (2 : ZMod 3785243996011)^222661411530 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 881 := Nat.prime_eq_prime_of_dvd_pow hq prime_881 hd
              subst q
              change (2 : ZMod 3785243996011)^4296531210 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 495563 := Nat.prime_eq_prime_of_dvd_pow hq prime_495563 hd
              subst q
              change (2 : ZMod 3785243996011)^7638270 ≠ 1
              reduce_mod_char
              decide

theorem prime_3814697265637 : Nat.Prime 3814697265637 := by
  apply lucas_primality 3814697265637 (2 : ZMod 3814697265637)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3814697265637 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((50627 : ℕ)^1 * ((6279089 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3814697265637)^1907348632818 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3814697265637)^1271565755212 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 50627 := Nat.prime_eq_prime_of_dvd_pow hq prime_50627 hd
          subst q
          change (2 : ZMod 3814697265637)^75349068 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 6279089 := Nat.prime_eq_prime_of_dvd_pow hq prime_6279089 hd
          subst q
          change (2 : ZMod 3814697265637)^607524 ≠ 1
          reduce_mod_char
          decide

theorem prime_3948808538471 : Nat.Prime 3948808538471 := by
  apply lucas_primality 3948808538471 (11 : ZMod 3948808538471)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3948808538471 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((241 : ℕ)^1 * ((1638509767 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 3948808538471)^1974404269235 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 3948808538471)^789761707694 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 241 := Nat.prime_eq_prime_of_dvd_pow hq prime_241 hd
          subst q
          change (11 : ZMod 3948808538471)^16385097670 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1638509767 := Nat.prime_eq_prime_of_dvd_pow hq prime_1638509767 hd
          subst q
          change (11 : ZMod 3948808538471)^2410 ≠ 1
          reduce_mod_char
          decide

theorem prime_3973328503189 : Nat.Prime 3973328503189 := by
  apply lucas_primality 3973328503189 (7 : ZMod 3973328503189)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3973328503189 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((5309 : ℕ)^1 * ((5669801 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 3973328503189)^1986664251594 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 3973328503189)^1324442834396 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (7 : ZMod 3973328503189)^361211682108 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 5309 := Nat.prime_eq_prime_of_dvd_pow hq prime_5309 hd
            subst q
            change (7 : ZMod 3973328503189)^748413732 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 5669801 := Nat.prime_eq_prime_of_dvd_pow hq prime_5669801 hd
            subst q
            change (7 : ZMod 3973328503189)^700788 ≠ 1
            reduce_mod_char
            decide

theorem prime_4001504141387 : Nat.Prime 4001504141387 := by
  apply lucas_primality 4001504141387 (2 : ZMod 4001504141387)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4001504141387 - 1 = (2 : ℕ)^1 * ((37 : ℕ)^1 * ((2011 : ℕ)^1 * ((26889299 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4001504141387)^2000752070693 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (2 : ZMod 4001504141387)^108148760578 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2011 := Nat.prime_eq_prime_of_dvd_pow hq prime_2011 hd
          subst q
          change (2 : ZMod 4001504141387)^1989808126 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 26889299 := Nat.prime_eq_prime_of_dvd_pow hq prime_26889299 hd
          subst q
          change (2 : ZMod 4001504141387)^148814 ≠ 1
          reduce_mod_char
          decide

theorem prime_4030372656997 : Nat.Prime 4030372656997 := by
  apply lucas_primality 4030372656997 (5 : ZMod 4030372656997)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4030372656997 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((19 : ℕ)^1 * ((360756593 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 4030372656997)^2015186328498 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 4030372656997)^1343457552332 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 4030372656997)^575767522428 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (5 : ZMod 4030372656997)^212124876684 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 360756593 := Nat.prime_eq_prime_of_dvd_pow hq prime_360756593 hd
            subst q
            change (5 : ZMod 4030372656997)^11172 ≠ 1
            reduce_mod_char
            decide

theorem prime_4100631992239 : Nat.Prime 4100631992239 := by
  apply lucas_primality 4100631992239 (3 : ZMod 4100631992239)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4100631992239 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((683438665373 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4100631992239)^2050315996119 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 4100631992239)^1366877330746 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 683438665373 := Nat.prime_eq_prime_of_dvd_pow hq prime_683438665373 hd
        subst q
        change (3 : ZMod 4100631992239)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_4165669620733 : Nat.Prime 4165669620733 := by
  apply lucas_primality 4165669620733 (7 : ZMod 4165669620733)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4165669620733 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((359 : ℕ)^1 * ((1997 : ℕ)^1 * ((484207 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 4165669620733)^2082834810366 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 4165669620733)^1388556540244 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 359 := Nat.prime_eq_prime_of_dvd_pow hq prime_359 hd
          subst q
          change (7 : ZMod 4165669620733)^11603536548 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1997 := Nat.prime_eq_prime_of_dvd_pow hq prime_1997 hd
            subst q
            change (7 : ZMod 4165669620733)^2085963756 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 484207 := Nat.prime_eq_prime_of_dvd_pow hq prime_484207 hd
            subst q
            change (7 : ZMod 4165669620733)^8603076 ≠ 1
            reduce_mod_char
            decide

theorem prime_4188375982831 : Nat.Prime 4188375982831 := by
  apply lucas_primality 4188375982831 (3 : ZMod 4188375982831)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4188375982831 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((1327 : ℕ)^1 * ((8093011 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4188375982831)^2094187991415 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 4188375982831)^1396125327610 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 4188375982831)^837675196566 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (3 : ZMod 4188375982831)^322182767910 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1327 := Nat.prime_eq_prime_of_dvd_pow hq prime_1327 hd
              subst q
              change (3 : ZMod 4188375982831)^3156274290 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 8093011 := Nat.prime_eq_prime_of_dvd_pow hq prime_8093011 hd
              subst q
              change (3 : ZMod 4188375982831)^517530 ≠ 1
              reduce_mod_char
              decide

theorem prime_4195872914707 : Nat.Prime 4195872914707 := by
  apply lucas_primality 4195872914707 (5 : ZMod 4195872914707)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4195872914707 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((107 : ℕ)^1 * ((198049321 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 4195872914707)^2097936457353 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 4195872914707)^1398624304902 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 4195872914707)^381442992246 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
            subst q
            change (5 : ZMod 4195872914707)^39213765558 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 198049321 := Nat.prime_eq_prime_of_dvd_pow hq prime_198049321 hd
            subst q
            change (5 : ZMod 4195872914707)^21186 ≠ 1
            reduce_mod_char
            decide

theorem prime_4213979354461 : Nat.Prime 4213979354461 := by
  apply lucas_primality 4213979354461 (2 : ZMod 4213979354461)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4213979354461 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((70232989241 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4213979354461)^2106989677230 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 4213979354461)^1404659784820 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 4213979354461)^842795870892 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 70232989241 := Nat.prime_eq_prime_of_dvd_pow hq prime_70232989241 hd
          subst q
          change (2 : ZMod 4213979354461)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_4398046511119 : Nat.Prime 4398046511119 := by
  apply lucas_primality 4398046511119 (7 : ZMod 4398046511119)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4398046511119 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((71 : ℕ)^1 * ((227 : ℕ)^1 * ((3498493 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 4398046511119)^2199023255559 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 4398046511119)^1466015503706 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (7 : ZMod 4398046511119)^338311270086 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
            subst q
            change (7 : ZMod 4398046511119)^61944317058 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 227 := Nat.prime_eq_prime_of_dvd_pow hq prime_227 hd
              subst q
              change (7 : ZMod 4398046511119)^19374654234 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 3498493 := Nat.prime_eq_prime_of_dvd_pow hq prime_3498493 hd
              subst q
              change (7 : ZMod 4398046511119)^1257126 ≠ 1
              reduce_mod_char
              decide

theorem prime_4453588946441 : Nat.Prime 4453588946441 := by
  apply lucas_primality 4453588946441 (3 : ZMod 4453588946441)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4453588946441 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((4831 : ℕ)^1 * ((23046931 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4453588946441)^2226794473220 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 4453588946441)^890717789288 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 4831 := Nat.prime_eq_prime_of_dvd_pow hq prime_4831 hd
          subst q
          change (3 : ZMod 4453588946441)^921877240 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 23046931 := Nat.prime_eq_prime_of_dvd_pow hq prime_23046931 hd
          subst q
          change (3 : ZMod 4453588946441)^193240 ≠ 1
          reduce_mod_char
          decide

theorem prime_4542088085209 : Nat.Prime 4542088085209 := by
  apply lucas_primality 4542088085209 (7 : ZMod 4542088085209)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4542088085209 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((63084556739 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 4542088085209)^2271044042604 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 4542088085209)^1514029361736 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 63084556739 := Nat.prime_eq_prime_of_dvd_pow hq prime_63084556739 hd
        subst q
        change (7 : ZMod 4542088085209)^72 ≠ 1
        reduce_mod_char
        decide

theorem prime_4557270705497 : Nat.Prime 4557270705497 := by
  apply lucas_primality 4557270705497 (3 : ZMod 4557270705497)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4557270705497 - 1 = (2 : ℕ)^3 * ((439 : ℕ)^1 * ((659 : ℕ)^1 * ((827 : ℕ)^1 * ((2381 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4557270705497)^2278635352748 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 439 := Nat.prime_eq_prime_of_dvd_pow hq prime_439 hd
        subst q
        change (3 : ZMod 4557270705497)^10381026664 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 659 := Nat.prime_eq_prime_of_dvd_pow hq prime_659 hd
          subst q
          change (3 : ZMod 4557270705497)^6915433544 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 827 := Nat.prime_eq_prime_of_dvd_pow hq prime_827 hd
            subst q
            change (3 : ZMod 4557270705497)^5510605448 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2381 := Nat.prime_eq_prime_of_dvd_pow hq prime_2381 hd
            subst q
            change (3 : ZMod 4557270705497)^1914015416 ≠ 1
            reduce_mod_char
            decide

theorem prime_4571428571429 : Nat.Prime 4571428571429 := by
  apply lucas_primality 4571428571429 (2 : ZMod 4571428571429)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4571428571429 - 1 = (2 : ℕ)^2 * ((31 : ℕ)^1 * ((2857 : ℕ)^1 * ((12903871 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4571428571429)^2285714285714 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (2 : ZMod 4571428571429)^147465437788 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2857 := Nat.prime_eq_prime_of_dvd_pow hq prime_2857 hd
          subst q
          change (2 : ZMod 4571428571429)^1600080004 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 12903871 := Nat.prime_eq_prime_of_dvd_pow hq prime_12903871 hd
          subst q
          change (2 : ZMod 4571428571429)^354268 ≠ 1
          reduce_mod_char
          decide

theorem prime_4608273662737 : Nat.Prime 4608273662737 := by
  apply lucas_primality 4608273662737 (5 : ZMod 4608273662737)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4608273662737 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((1913 : ℕ)^1 * ((50185939 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 4608273662737)^2304136831368 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 4608273662737)^1536091220912 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1913 := Nat.prime_eq_prime_of_dvd_pow hq prime_1913 hd
          subst q
          change (5 : ZMod 4608273662737)^2408925072 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 50185939 := Nat.prime_eq_prime_of_dvd_pow hq prime_50185939 hd
          subst q
          change (5 : ZMod 4608273662737)^91824 ≠ 1
          reduce_mod_char
          decide

theorem prime_4647057195323 : Nat.Prime 4647057195323 := by
  apply lucas_primality 4647057195323 (2 : ZMod 4647057195323)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4647057195323 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((646957 : ℕ)^1 * ((156151 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4647057195323)^2323528597661 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (2 : ZMod 4647057195323)^202045965014 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 646957 := Nat.prime_eq_prime_of_dvd_pow hq prime_646957 hd
          subst q
          change (2 : ZMod 4647057195323)^7182946 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 156151 := Nat.prime_eq_prime_of_dvd_pow hq prime_156151 hd
          subst q
          change (2 : ZMod 4647057195323)^29760022 ≠ 1
          reduce_mod_char
          decide

theorem prime_4795039903403 : Nat.Prime 4795039903403 := by
  apply lucas_primality 4795039903403 (2 : ZMod 4795039903403)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4795039903403 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((79 : ℕ)^1 * ((97 : ℕ)^1 * ((44695661 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4795039903403)^2397519951701 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 4795039903403)^685005700486 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (2 : ZMod 4795039903403)^60696707638 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
            subst q
            change (2 : ZMod 4795039903403)^49433401066 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 44695661 := Nat.prime_eq_prime_of_dvd_pow hq prime_44695661 hd
            subst q
            change (2 : ZMod 4795039903403)^107282 ≠ 1
            reduce_mod_char
            decide

theorem prime_4820145371737 : Nat.Prime 4820145371737 := by
  apply lucas_primality 4820145371737 (5 : ZMod 4820145371737)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4820145371737 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((233 : ℕ)^1 * ((861971633 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 4820145371737)^2410072685868 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 4820145371737)^1606715123912 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
          subst q
          change (5 : ZMod 4820145371737)^20687319192 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 861971633 := Nat.prime_eq_prime_of_dvd_pow hq prime_861971633 hd
          subst q
          change (5 : ZMod 4820145371737)^5592 ≠ 1
          reduce_mod_char
          decide

theorem prime_4826809000087 : Nat.Prime 4826809000087 := by
  apply lucas_primality 4826809000087 (5 : ZMod 4826809000087)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4826809000087 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((3853 : ℕ)^1 * ((208790077 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 4826809000087)^2413404500043 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 4826809000087)^1608936333362 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 3853 := Nat.prime_eq_prime_of_dvd_pow hq prime_3853 hd
          subst q
          change (5 : ZMod 4826809000087)^1252740462 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 208790077 := Nat.prime_eq_prime_of_dvd_pow hq prime_208790077 hd
          subst q
          change (5 : ZMod 4826809000087)^23118 ≠ 1
          reduce_mod_char
          decide

theorem prime_4939715341039 : Nat.Prime 4939715341039 := by
  apply lucas_primality 4939715341039 (3 : ZMod 4939715341039)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4939715341039 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((53 : ℕ)^1 * ((15533696041 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4939715341039)^2469857670519 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 4939715341039)^1646571780346 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (3 : ZMod 4939715341039)^93202176246 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 15533696041 := Nat.prime_eq_prime_of_dvd_pow hq prime_15533696041 hd
          subst q
          change (3 : ZMod 4939715341039)^318 ≠ 1
          reduce_mod_char
          decide

theorem prime_4953643592363 : Nat.Prime 4953643592363 := by
  apply lucas_primality 4953643592363 (5 : ZMod 4953643592363)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4953643592363 - 1 = (2 : ℕ)^1 * ((101 : ℕ)^1 * ((137 : ℕ)^1 * ((197 : ℕ)^1 * ((359 : ℕ)^1 * ((2531 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 4953643592363)^2476821796181 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
        subst q
        change (5 : ZMod 4953643592363)^49045976162 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
          subst q
          change (5 : ZMod 4953643592363)^36157982426 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
            subst q
            change (5 : ZMod 4953643592363)^25145398946 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 359 := Nat.prime_eq_prime_of_dvd_pow hq prime_359 hd
              subst q
              change (5 : ZMod 4953643592363)^13798450118 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 2531 := Nat.prime_eq_prime_of_dvd_pow hq prime_2531 hd
              subst q
              change (5 : ZMod 4953643592363)^1957188302 ≠ 1
              reduce_mod_char
              decide

theorem prime_5007234125951 : Nat.Prime 5007234125951 := by
  apply lucas_primality 5007234125951 (7 : ZMod 5007234125951)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5007234125951 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((7 : ℕ)^2 * ((5393 : ℕ)^1 * ((378967 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 5007234125951)^2503617062975 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 5007234125951)^1001446825190 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 5007234125951)^715319160850 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 5393 := Nat.prime_eq_prime_of_dvd_pow hq prime_5393 hd
            subst q
            change (7 : ZMod 5007234125951)^928469150 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 378967 := Nat.prime_eq_prime_of_dvd_pow hq prime_378967 hd
            subst q
            change (7 : ZMod 5007234125951)^13212850 ≠ 1
            reduce_mod_char
            decide

theorem prime_5053913144299 : Nat.Prime 5053913144299 := by
  apply lucas_primality 5053913144299 (2 : ZMod 5053913144299)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5053913144299 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((280772952461 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5053913144299)^2526956572149 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 5053913144299)^1684637714766 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 280772952461 := Nat.prime_eq_prime_of_dvd_pow hq prime_280772952461 hd
        subst q
        change (2 : ZMod 5053913144299)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_5077997833421 : Nat.Prime 5077997833421 := by
  apply lucas_primality 5077997833421 (2 : ZMod 5077997833421)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5077997833421 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((179 : ℕ)^1 * ((563 : ℕ)^1 * ((2519423 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5077997833421)^2538998916710 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 5077997833421)^1015599566684 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 179 := Nat.prime_eq_prime_of_dvd_pow hq prime_179 hd
          subst q
          change (2 : ZMod 5077997833421)^28368702980 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 563 := Nat.prime_eq_prime_of_dvd_pow hq prime_563 hd
            subst q
            change (2 : ZMod 5077997833421)^9019534340 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2519423 := Nat.prime_eq_prime_of_dvd_pow hq prime_2519423 hd
            subst q
            change (2 : ZMod 5077997833421)^2015540 ≠ 1
            reduce_mod_char
            decide

theorem prime_5093492820677 : Nat.Prime 5093492820677 := by
  apply lucas_primality 5093492820677 (2 : ZMod 5093492820677)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5093492820677 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((643 : ℕ)^1 * ((152335591 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5093492820677)^2546746410338 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 5093492820677)^391807140052 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 643 := Nat.prime_eq_prime_of_dvd_pow hq prime_643 hd
          subst q
          change (2 : ZMod 5093492820677)^7921450732 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 152335591 := Nat.prime_eq_prime_of_dvd_pow hq prime_152335591 hd
          subst q
          change (2 : ZMod 5093492820677)^33436 ≠ 1
          reduce_mod_char
          decide

theorem prime_5289852801067 : Nat.Prime 5289852801067 := by
  apply lucas_primality 5289852801067 (2 : ZMod 5289852801067)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5289852801067 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((41 : ℕ)^1 * ((21503466671 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5289852801067)^2644926400533 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 5289852801067)^1763284267022 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (2 : ZMod 5289852801067)^129020800026 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 21503466671 := Nat.prime_eq_prime_of_dvd_pow hq prime_21503466671 hd
          subst q
          change (2 : ZMod 5289852801067)^246 ≠ 1
          reduce_mod_char
          decide

theorem prime_5295792513061 : Nat.Prime 5295792513061 := by
  apply lucas_primality 5295792513061 (2 : ZMod 5295792513061)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5295792513061 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((19 : ℕ)^1 * ((37 : ℕ)^1 * ((43 : ℕ)^1 * ((163 : ℕ)^1 * ((853 : ℕ)^1)))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5295792513061)^2647896256530 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 5295792513061)^1765264171020 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 5295792513061)^1059158502612 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (2 : ZMod 5295792513061)^756541787580 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
              subst q
              change (2 : ZMod 5295792513061)^278725921740 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
                subst q
                change (2 : ZMod 5295792513061)^143129527380 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
                  subst q
                  change (2 : ZMod 5295792513061)^123157965420 ≠ 1
                  reduce_mod_char
                  decide
                · rcases hq.dvd_mul.mp hd with hd | hd
                  · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
                    subst q
                    change (2 : ZMod 5295792513061)^32489524620 ≠ 1
                    reduce_mod_char
                    decide
                  · have heq : q = 853 := Nat.prime_eq_prime_of_dvd_pow hq prime_853 hd
                    subst q
                    change (2 : ZMod 5295792513061)^6208432020 ≠ 1
                    reduce_mod_char
                    decide

theorem prime_5373730620481 : Nat.Prime 5373730620481 := by
  apply lucas_primality 5373730620481 (29 : ZMod 5373730620481)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5373730620481 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((23 : ℕ)^1 * ((243375481 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (29 : ZMod 5373730620481)^2686865310240 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (29 : ZMod 5373730620481)^1791243540160 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (29 : ZMod 5373730620481)^1074746124096 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (29 : ZMod 5373730620481)^233640461760 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 243375481 := Nat.prime_eq_prime_of_dvd_pow hq prime_243375481 hd
            subst q
            change (29 : ZMod 5373730620481)^22080 ≠ 1
            reduce_mod_char
            decide

theorem prime_5399215110823 : Nat.Prime 5399215110823 := by
  apply lucas_primality 5399215110823 (3 : ZMod 5399215110823)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5399215110823 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((1367 : ℕ)^1 * ((2143 : ℕ)^1 * ((23629 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 5399215110823)^2699607555411 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 5399215110823)^1799738370274 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 5399215110823)^415324239294 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1367 := Nat.prime_eq_prime_of_dvd_pow hq prime_1367 hd
            subst q
            change (3 : ZMod 5399215110823)^3949681866 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 2143 := Nat.prime_eq_prime_of_dvd_pow hq prime_2143 hd
              subst q
              change (3 : ZMod 5399215110823)^2519465754 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 23629 := Nat.prime_eq_prime_of_dvd_pow hq prime_23629 hd
              subst q
              change (3 : ZMod 5399215110823)^228499518 ≠ 1
              reduce_mod_char
              decide

theorem prime_5405495330513 : Nat.Prime 5405495330513 := by
  apply lucas_primality 5405495330513 (3 : ZMod 5405495330513)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5405495330513 - 1 = (2 : ℕ)^4 * ((641 : ℕ)^1 * ((527056877 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 5405495330513)^2702747665256 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 641 := Nat.prime_eq_prime_of_dvd_pow hq prime_641 hd
        subst q
        change (3 : ZMod 5405495330513)^8432910032 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 527056877 := Nat.prime_eq_prime_of_dvd_pow hq prime_527056877 hd
        subst q
        change (3 : ZMod 5405495330513)^10256 ≠ 1
        reduce_mod_char
        decide

theorem prime_5408227622549 : Nat.Prime 5408227622549 := by
  apply lucas_primality 5408227622549 (2 : ZMod 5408227622549)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5408227622549 - 1 = (2 : ℕ)^2 * ((283 : ℕ)^1 * ((4777586239 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5408227622549)^2704113811274 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 283 := Nat.prime_eq_prime_of_dvd_pow hq prime_283 hd
        subst q
        change (2 : ZMod 5408227622549)^19110344956 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4777586239 := Nat.prime_eq_prime_of_dvd_pow hq prime_4777586239 hd
        subst q
        change (2 : ZMod 5408227622549)^1132 ≠ 1
        reduce_mod_char
        decide

theorem prime_5442516504043 : Nat.Prime 5442516504043 := by
  apply lucas_primality 5442516504043 (3 : ZMod 5442516504043)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5442516504043 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((29 : ℕ)^1 * ((29221 : ℕ)^1 * ((1070423 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 5442516504043)^2721258252021 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 5442516504043)^1814172168014 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (3 : ZMod 5442516504043)^187672982898 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29221 := Nat.prime_eq_prime_of_dvd_pow hq prime_29221 hd
            subst q
            change (3 : ZMod 5442516504043)^186253602 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1070423 := Nat.prime_eq_prime_of_dvd_pow hq prime_1070423 hd
            subst q
            change (3 : ZMod 5442516504043)^5084454 ≠ 1
            reduce_mod_char
            decide

theorem prime_5496304748189 : Nat.Prime 5496304748189 := by
  apply lucas_primality 5496304748189 (2 : ZMod 5496304748189)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5496304748189 - 1 = (2 : ℕ)^2 * ((142973 : ℕ)^1 * ((9610739 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5496304748189)^2748152374094 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 142973 := Nat.prime_eq_prime_of_dvd_pow hq prime_142973 hd
        subst q
        change (2 : ZMod 5496304748189)^38442956 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 9610739 := Nat.prime_eq_prime_of_dvd_pow hq prime_9610739 hd
        subst q
        change (2 : ZMod 5496304748189)^571892 ≠ 1
        reduce_mod_char
        decide

theorem prime_5498839937813 : Nat.Prime 5498839937813 := by
  apply lucas_primality 5498839937813 (2 : ZMod 5498839937813)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5498839937813 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((127549 : ℕ)^1 * ((829069 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5498839937813)^2749419968906 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 5498839937813)^422987687524 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 127549 := Nat.prime_eq_prime_of_dvd_pow hq prime_127549 hd
          subst q
          change (2 : ZMod 5498839937813)^43111588 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 829069 := Nat.prime_eq_prime_of_dvd_pow hq prime_829069 hd
          subst q
          change (2 : ZMod 5498839937813)^6632548 ≠ 1
          reduce_mod_char
          decide

theorem prime_5527889494129 : Nat.Prime 5527889494129 := by
  apply lucas_primality 5527889494129 (11 : ZMod 5527889494129)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5527889494129 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((53 : ℕ)^1 * ((61 : ℕ)^1 * ((307 : ℕ)^1 * ((38677 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 5527889494129)^2763944747064 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 5527889494129)^1842629831376 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (11 : ZMod 5527889494129)^104299801776 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
            subst q
            change (11 : ZMod 5527889494129)^90621139248 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 307 := Nat.prime_eq_prime_of_dvd_pow hq prime_307 hd
              subst q
              change (11 : ZMod 5527889494129)^18006154704 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 38677 := Nat.prime_eq_prime_of_dvd_pow hq prime_38677 hd
              subst q
              change (11 : ZMod 5527889494129)^142924464 ≠ 1
              reduce_mod_char
              decide

theorem prime_5534900853787 : Nat.Prime 5534900853787 := by
  apply lucas_primality 5534900853787 (5 : ZMod 5534900853787)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5534900853787 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((34166054653 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 5534900853787)^2767450426893 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 5534900853787)^1844966951262 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 34166054653 := Nat.prime_eq_prime_of_dvd_pow hq prime_34166054653 hd
        subst q
        change (5 : ZMod 5534900853787)^162 ≠ 1
        reduce_mod_char
        decide

theorem prime_5547717886877 : Nat.Prime 5547717886877 := by
  apply lucas_primality 5547717886877 (2 : ZMod 5547717886877)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5547717886877 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^2 * ((11462227039 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5547717886877)^2773858943438 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 5547717886877)^504337989716 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 11462227039 := Nat.prime_eq_prime_of_dvd_pow hq prime_11462227039 hd
        subst q
        change (2 : ZMod 5547717886877)^484 ≠ 1
        reduce_mod_char
        decide

theorem prime_5642140102843 : Nat.Prime 5642140102843 := by
  apply lucas_primality 5642140102843 (2 : ZMod 5642140102843)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5642140102843 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((40885073209 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5642140102843)^2821070051421 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 5642140102843)^1880713367614 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 5642140102843)^245310439254 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 40885073209 := Nat.prime_eq_prime_of_dvd_pow hq prime_40885073209 hd
          subst q
          change (2 : ZMod 5642140102843)^138 ≠ 1
          reduce_mod_char
          decide

theorem prime_5695312500011 : Nat.Prime 5695312500011 := by
  apply lucas_primality 5695312500011 (2 : ZMod 5695312500011)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5695312500011 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((2083 : ℕ)^1 * ((39059821 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5695312500011)^2847656250005 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 5695312500011)^1139062500002 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 5695312500011)^813616071430 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2083 := Nat.prime_eq_prime_of_dvd_pow hq prime_2083 hd
            subst q
            change (2 : ZMod 5695312500011)^2734187470 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 39059821 := Nat.prime_eq_prime_of_dvd_pow hq prime_39059821 hd
            subst q
            change (2 : ZMod 5695312500011)^145810 ≠ 1
            reduce_mod_char
            decide

theorem prime_5789336458819 : Nat.Prime 5789336458819 := by
  apply lucas_primality 5789336458819 (2 : ZMod 5789336458819)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5789336458819 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^2 * ((1579 : ℕ)^1 * ((5050217 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5789336458819)^2894668229409 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 5789336458819)^1929778819606 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 5789336458819)^526303314438 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1579 := Nat.prime_eq_prime_of_dvd_pow hq prime_1579 hd
            subst q
            change (2 : ZMod 5789336458819)^3666457542 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 5050217 := Nat.prime_eq_prime_of_dvd_pow hq prime_5050217 hd
            subst q
            change (2 : ZMod 5789336458819)^1146354 ≠ 1
            reduce_mod_char
            decide

theorem prime_5982952309021 : Nat.Prime 5982952309021 := by
  apply lucas_primality 5982952309021 (10 : ZMod 5982952309021)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5982952309021 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((199 : ℕ)^1 * ((1973 : ℕ)^1 * ((28219 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 5982952309021)^2991476154510 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 5982952309021)^1994317436340 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 5982952309021)^1196590461804 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 199 := Nat.prime_eq_prime_of_dvd_pow hq prime_199 hd
            subst q
            change (10 : ZMod 5982952309021)^30065086980 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1973 := Nat.prime_eq_prime_of_dvd_pow hq prime_1973 hd
              subst q
              change (10 : ZMod 5982952309021)^3032413740 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 28219 := Nat.prime_eq_prime_of_dvd_pow hq prime_28219 hd
              subst q
              change (10 : ZMod 5982952309021)^212018580 ≠ 1
              reduce_mod_char
              decide

theorem prime_6053445140629 : Nat.Prime 6053445140629 := by
  apply lucas_primality 6053445140629 (6 : ZMod 6053445140629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6053445140629 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((73 : ℕ)^1 * ((5737 : ℕ)^1 * ((1204519 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 6053445140629)^3026722570314 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 6053445140629)^2017815046876 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
          subst q
          change (6 : ZMod 6053445140629)^82923906036 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 5737 := Nat.prime_eq_prime_of_dvd_pow hq prime_5737 hd
            subst q
            change (6 : ZMod 6053445140629)^1055158644 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1204519 := Nat.prime_eq_prime_of_dvd_pow hq prime_1204519 hd
            subst q
            change (6 : ZMod 6053445140629)^5025612 ≠ 1
            reduce_mod_char
            decide

theorem prime_6166918054049 : Nat.Prime 6166918054049 := by
  apply lucas_primality 6166918054049 (3 : ZMod 6166918054049)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6166918054049 - 1 = (2 : ℕ)^5 * ((53 : ℕ)^1 * ((97 : ℕ)^1 * ((103 : ℕ)^1 * ((353 : ℕ)^1 * ((1031 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 6166918054049)^3083459027024 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
        subst q
        change (3 : ZMod 6166918054049)^116356944416 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
          subst q
          change (3 : ZMod 6166918054049)^63576474784 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
            subst q
            change (3 : ZMod 6166918054049)^59872990816 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 353 := Nat.prime_eq_prime_of_dvd_pow hq prime_353 hd
              subst q
              change (3 : ZMod 6166918054049)^17470022816 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1031 := Nat.prime_eq_prime_of_dvd_pow hq prime_1031 hd
              subst q
              change (3 : ZMod 6166918054049)^5981491808 ≠ 1
              reduce_mod_char
              decide

theorem prime_6327518887981 : Nat.Prime 6327518887981 := by
  apply lucas_primality 6327518887981 (2 : ZMod 6327518887981)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6327518887981 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((30757 : ℕ)^1 * ((1142923 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6327518887981)^3163759443990 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 6327518887981)^2109172962660 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 6327518887981)^1265503777596 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 30757 := Nat.prime_eq_prime_of_dvd_pow hq prime_30757 hd
            subst q
            change (2 : ZMod 6327518887981)^205726140 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1142923 := Nat.prime_eq_prime_of_dvd_pow hq prime_1142923 hd
            subst q
            change (2 : ZMod 6327518887981)^5536260 ≠ 1
            reduce_mod_char
            decide

theorem prime_6611856250627 : Nat.Prime 6611856250627 := by
  apply lucas_primality 6611856250627 (2 : ZMod 6611856250627)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6611856250627 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^5 * ((11 : ℕ)^1 * ((2161 : ℕ)^1 * ((572321 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6611856250627)^3305928125313 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 6611856250627)^2203952083542 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 6611856250627)^601077840966 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2161 := Nat.prime_eq_prime_of_dvd_pow hq prime_2161 hd
            subst q
            change (2 : ZMod 6611856250627)^3059628066 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 572321 := Nat.prime_eq_prime_of_dvd_pow hq prime_572321 hd
            subst q
            change (2 : ZMod 6611856250627)^11552706 ≠ 1
            reduce_mod_char
            decide

theorem prime_6624910136753 : Nat.Prime 6624910136753 := by
  apply lucas_primality 6624910136753 (3 : ZMod 6624910136753)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6624910136753 - 1 = (2 : ℕ)^4 * ((414056883547 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 6624910136753)^3312455068376 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 414056883547 := Nat.prime_eq_prime_of_dvd_pow hq prime_414056883547 hd
      subst q
      change (3 : ZMod 6624910136753)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_6709704278863 : Nat.Prime 6709704278863 := by
  apply lucas_primality 6709704278863 (6 : ZMod 6709704278863)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6709704278863 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((23 : ℕ)^1 * ((3740080423 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 6709704278863)^3354852139431 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 6709704278863)^2236568092954 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (6 : ZMod 6709704278863)^516131098374 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (6 : ZMod 6709704278863)^291726272994 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3740080423 := Nat.prime_eq_prime_of_dvd_pow hq prime_3740080423 hd
            subst q
            change (6 : ZMod 6709704278863)^1794 ≠ 1
            reduce_mod_char
            decide

theorem prime_6825811399997 : Nat.Prime 6825811399997 := by
  apply lucas_primality 6825811399997 (2 : ZMod 6825811399997)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6825811399997 - 1 = (2 : ℕ)^2 * ((31 : ℕ)^2 * ((59 : ℕ)^1 * ((743 : ℕ)^1 * ((40507 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6825811399997)^3412905699998 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (2 : ZMod 6825811399997)^220187464516 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (2 : ZMod 6825811399997)^115691718644 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 743 := Nat.prime_eq_prime_of_dvd_pow hq prime_743 hd
            subst q
            change (2 : ZMod 6825811399997)^9186825572 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 40507 := Nat.prime_eq_prime_of_dvd_pow hq prime_40507 hd
            subst q
            change (2 : ZMod 6825811399997)^168509428 ≠ 1
            reduce_mod_char
            decide

theorem prime_6906762437203 : Nat.Prime 6906762437203 := by
  apply lucas_primality 6906762437203 (2 : ZMod 6906762437203)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6906762437203 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((97 : ℕ)^1 * ((2179 : ℕ)^1 * ((1815403 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6906762437203)^3453381218601 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 6906762437203)^2302254145734 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
          subst q
          change (2 : ZMod 6906762437203)^71203736466 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2179 := Nat.prime_eq_prime_of_dvd_pow hq prime_2179 hd
            subst q
            change (2 : ZMod 6906762437203)^3169693638 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1815403 := Nat.prime_eq_prime_of_dvd_pow hq prime_1815403 hd
            subst q
            change (2 : ZMod 6906762437203)^3804534 ≠ 1
            reduce_mod_char
            decide

theorem prime_7212549413171 : Nat.Prime 7212549413171 := by
  apply lucas_primality 7212549413171 (2 : ZMod 7212549413171)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7212549413171 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((61 : ℕ)^1 * ((11823851497 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 7212549413171)^3606274706585 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 7212549413171)^1442509882634 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (2 : ZMod 7212549413171)^118238514970 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11823851497 := Nat.prime_eq_prime_of_dvd_pow hq prime_11823851497 hd
          subst q
          change (2 : ZMod 7212549413171)^610 ≠ 1
          reduce_mod_char
          decide

theorem prime_7358610997937 : Nat.Prime 7358610997937 := by
  apply lucas_primality 7358610997937 (3 : ZMod 7358610997937)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7358610997937 - 1 = (2 : ℕ)^4 * ((11 : ℕ)^1 * ((59 : ℕ)^1 * ((708648979 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 7358610997937)^3679305498968 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 7358610997937)^668964636176 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (3 : ZMod 7358610997937)^124722220304 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 708648979 := Nat.prime_eq_prime_of_dvd_pow hq prime_708648979 hd
          subst q
          change (3 : ZMod 7358610997937)^10384 ≠ 1
          reduce_mod_char
          decide

theorem prime_7372483898887 : Nat.Prime 7372483898887 := by
  apply lucas_primality 7372483898887 (3 : ZMod 7372483898887)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7372483898887 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((4253 : ℕ)^1 * ((32101453 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 7372483898887)^3686241949443 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 7372483898887)^2457494632962 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 4253 := Nat.prime_eq_prime_of_dvd_pow hq prime_4253 hd
          subst q
          change (3 : ZMod 7372483898887)^1733478462 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 32101453 := Nat.prime_eq_prime_of_dvd_pow hq prime_32101453 hd
          subst q
          change (3 : ZMod 7372483898887)^229662 ≠ 1
          reduce_mod_char
          decide

theorem prime_7529536000009 : Nat.Prime 7529536000009 := by
  apply lucas_primality 7529536000009 (19 : ZMod 7529536000009)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7529536000009 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^5 * ((11 : ℕ)^2 * ((2833 : ℕ)^1 * ((11299 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 7529536000009)^3764768000004 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 7529536000009)^2509845333336 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (19 : ZMod 7529536000009)^684503272728 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2833 := Nat.prime_eq_prime_of_dvd_pow hq prime_2833 hd
            subst q
            change (19 : ZMod 7529536000009)^2657795976 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 11299 := Nat.prime_eq_prime_of_dvd_pow hq prime_11299 hd
            subst q
            change (19 : ZMod 7529536000009)^666389592 ≠ 1
            reduce_mod_char
            decide

theorem prime_7708132818493 : Nat.Prime 7708132818493 := by
  apply lucas_primality 7708132818493 (5 : ZMod 7708132818493)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7708132818493 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((642344401541 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 7708132818493)^3854066409246 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 7708132818493)^2569377606164 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 642344401541 := Nat.prime_eq_prime_of_dvd_pow hq prime_642344401541 hd
        subst q
        change (5 : ZMod 7708132818493)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_7858047974851 : Nat.Prime 7858047974851 := by
  apply lucas_primality 7858047974851 (23 : ZMod 7858047974851)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7858047974851 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^2 * ((17462328833 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (23 : ZMod 7858047974851)^3929023987425 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (23 : ZMod 7858047974851)^2619349324950 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (23 : ZMod 7858047974851)^1571609594970 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17462328833 := Nat.prime_eq_prime_of_dvd_pow hq prime_17462328833 hd
          subst q
          change (23 : ZMod 7858047974851)^450 ≠ 1
          reduce_mod_char
          decide

theorem prime_7900712033633 : Nat.Prime 7900712033633 := by
  apply lucas_primality 7900712033633 (3 : ZMod 7900712033633)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7900712033633 - 1 = (2 : ℕ)^5 * ((11 : ℕ)^1 * ((167 : ℕ)^1 * ((134402423 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 7900712033633)^3950356016816 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 7900712033633)^718246548512 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
          subst q
          change (3 : ZMod 7900712033633)^47309652896 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 134402423 := Nat.prime_eq_prime_of_dvd_pow hq prime_134402423 hd
          subst q
          change (3 : ZMod 7900712033633)^58784 ≠ 1
          reduce_mod_char
          decide

theorem prime_8070440987569 : Nat.Prime 8070440987569 := by
  apply lucas_primality 8070440987569 (17 : ZMod 8070440987569)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8070440987569 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((499 : ℕ)^1 * ((336942259 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 8070440987569)^4035220493784 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 8070440987569)^2690146995856 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 499 := Nat.prime_eq_prime_of_dvd_pow hq prime_499 hd
          subst q
          change (17 : ZMod 8070440987569)^16173228432 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 336942259 := Nat.prime_eq_prime_of_dvd_pow hq prime_336942259 hd
          subst q
          change (17 : ZMod 8070440987569)^23952 ≠ 1
          reduce_mod_char
          decide

theorem prime_8198418170951 : Nat.Prime 8198418170951 := by
  apply lucas_primality 8198418170951 (7 : ZMod 8198418170951)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8198418170951 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((7 : ℕ)^2 * ((1447 : ℕ)^1 * ((2312573 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 8198418170951)^4099209085475 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 8198418170951)^1639683634190 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 8198418170951)^1171202595850 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1447 := Nat.prime_eq_prime_of_dvd_pow hq prime_1447 hd
            subst q
            change (7 : ZMod 8198418170951)^5665803850 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2312573 := Nat.prime_eq_prime_of_dvd_pow hq prime_2312573 hd
            subst q
            change (7 : ZMod 8198418170951)^3545150 ≠ 1
            reduce_mod_char
            decide

theorem prime_8271781641707 : Nat.Prime 8271781641707 := by
  apply lucas_primality 8271781641707 (5 : ZMod 8271781641707)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8271781641707 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((29 : ℕ)^1 * ((197 : ℕ)^1 * ((6689 : ℕ)^1 * ((9839 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 8271781641707)^4135890820853 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 8271781641707)^751980149246 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (5 : ZMod 8271781641707)^285233849714 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
            subst q
            change (5 : ZMod 8271781641707)^41988739298 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 6689 := Nat.prime_eq_prime_of_dvd_pow hq prime_6689 hd
              subst q
              change (5 : ZMod 8271781641707)^1236624554 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 9839 := Nat.prime_eq_prime_of_dvd_pow hq prime_9839 hd
              subst q
              change (5 : ZMod 8271781641707)^840713654 ≠ 1
              reduce_mod_char
              decide

theorem prime_8413004585341 : Nat.Prime 8413004585341 := by
  apply lucas_primality 8413004585341 (6 : ZMod 8413004585341)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8413004585341 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^4 * ((5 : ℕ)^1 * ((67679 : ℕ)^1 * ((76733 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 8413004585341)^4206502292670 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 8413004585341)^2804334861780 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 8413004585341)^1682600917068 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 67679 := Nat.prime_eq_prime_of_dvd_pow hq prime_67679 hd
            subst q
            change (6 : ZMod 8413004585341)^124307460 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 76733 := Nat.prime_eq_prime_of_dvd_pow hq prime_76733 hd
            subst q
            change (6 : ZMod 8413004585341)^109639980 ≠ 1
            reduce_mod_char
            decide

theorem prime_8517751758457 : Nat.Prime 8517751758457 := by
  apply lucas_primality 8517751758457 (5 : ZMod 8517751758457)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8517751758457 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((354906323269 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 8517751758457)^4258875879228 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 8517751758457)^2839250586152 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 354906323269 := Nat.prime_eq_prime_of_dvd_pow hq prime_354906323269 hd
        subst q
        change (5 : ZMod 8517751758457)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_8550986578877 : Nat.Prime 8550986578877 := by
  apply lucas_primality 8550986578877 (3 : ZMod 8550986578877)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8550986578877 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((19 : ℕ)^1 * ((157 : ℕ)^1 * ((5113 : ℕ)^1 * ((20023 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 8550986578877)^4275493289438 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 8550986578877)^1221569511268 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (3 : ZMod 8550986578877)^450051925204 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
            subst q
            change (3 : ZMod 8550986578877)^54464882668 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 5113 := Nat.prime_eq_prime_of_dvd_pow hq prime_5113 hd
              subst q
              change (3 : ZMod 8550986578877)^1672401052 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 20023 := Nat.prime_eq_prime_of_dvd_pow hq prime_20023 hd
              subst q
              change (3 : ZMod 8550986578877)^427058212 ≠ 1
              reduce_mod_char
              decide

theorem prime_8658819186317 : Nat.Prime 8658819186317 := by
  apply lucas_primality 8658819186317 (2 : ZMod 8658819186317)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8658819186317 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((46573 : ℕ)^1 * ((3575371 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8658819186317)^4329409593158 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 8658819186317)^666063014332 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 46573 := Nat.prime_eq_prime_of_dvd_pow hq prime_46573 hd
          subst q
          change (2 : ZMod 8658819186317)^185919292 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3575371 := Nat.prime_eq_prime_of_dvd_pow hq prime_3575371 hd
          subst q
          change (2 : ZMod 8658819186317)^2421796 ≠ 1
          reduce_mod_char
          decide

theorem prime_8664263780611 : Nat.Prime 8664263780611 := by
  apply lucas_primality 8664263780611 (10 : ZMod 8664263780611)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8664263780611 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((17 : ℕ)^2 * ((19 : ℕ)^1 * ((643 : ℕ)^1 * ((81799 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 8664263780611)^4332131890305 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 8664263780611)^2888087926870 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 8664263780611)^1732852756122 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (10 : ZMod 8664263780611)^509662575330 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
              subst q
              change (10 : ZMod 8664263780611)^456013883190 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 643 := Nat.prime_eq_prime_of_dvd_pow hq prime_643 hd
                subst q
                change (10 : ZMod 8664263780611)^13474749270 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 81799 := Nat.prime_eq_prime_of_dvd_pow hq prime_81799 hd
                subst q
                change (10 : ZMod 8664263780611)^105921390 ≠ 1
                reduce_mod_char
                decide

theorem prime_8758122958561 : Nat.Prime 8758122958561 := by
  apply lucas_primality 8758122958561 (29 : ZMod 8758122958561)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8758122958561 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((23 : ℕ)^1 * ((937 : ℕ)^1 * ((846647 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (29 : ZMod 8758122958561)^4379061479280 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (29 : ZMod 8758122958561)^2919374319520 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (29 : ZMod 8758122958561)^1751624591712 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (29 : ZMod 8758122958561)^380787954720 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 937 := Nat.prime_eq_prime_of_dvd_pow hq prime_937 hd
              subst q
              change (29 : ZMod 8758122958561)^9346982880 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 846647 := Nat.prime_eq_prime_of_dvd_pow hq prime_846647 hd
              subst q
              change (29 : ZMod 8758122958561)^10344480 ≠ 1
              reduce_mod_char
              decide

theorem prime_8889639126941 : Nat.Prime 8889639126941 := by
  apply lucas_primality 8889639126941 (2 : ZMod 8889639126941)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8889639126941 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((47 : ℕ)^1 * ((2837 : ℕ)^1 * ((23311 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8889639126941)^4444819563470 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 8889639126941)^1777927825388 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 8889639126941)^808149011540 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (2 : ZMod 8889639126941)^683818394380 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
              subst q
              change (2 : ZMod 8889639126941)^189141258020 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 2837 := Nat.prime_eq_prime_of_dvd_pow hq prime_2837 hd
                subst q
                change (2 : ZMod 8889639126941)^3133464620 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 23311 := Nat.prime_eq_prime_of_dvd_pow hq prime_23311 hd
                subst q
                change (2 : ZMod 8889639126941)^381349540 ≠ 1
                reduce_mod_char
                decide

theorem prime_8916100448291 : Nat.Prime 8916100448291 := by
  apply lucas_primality 8916100448291 (2 : ZMod 8916100448291)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8916100448291 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((23 : ℕ)^1 * ((137 : ℕ)^1 * ((307 : ℕ)^1 * ((131671 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8916100448291)^4458050224145 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 8916100448291)^1783220089658 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 8916100448291)^1273728635470 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (2 : ZMod 8916100448291)^387656541230 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
              subst q
              change (2 : ZMod 8916100448291)^65081025170 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 307 := Nat.prime_eq_prime_of_dvd_pow hq prime_307 hd
                subst q
                change (2 : ZMod 8916100448291)^29042672470 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 131671 := Nat.prime_eq_prime_of_dvd_pow hq prime_131671 hd
                subst q
                change (2 : ZMod 8916100448291)^67714990 ≠ 1
                reduce_mod_char
                decide

theorem prime_9294114390647 : Nat.Prime 9294114390647 := by
  apply lucas_primality 9294114390647 (5 : ZMod 9294114390647)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9294114390647 - 1 = (2 : ℕ)^1 * ((4647057195323 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 9294114390647)^4647057195323 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 4647057195323 := Nat.prime_eq_prime_of_dvd_pow hq prime_4647057195323 hd
      subst q
      change (5 : ZMod 9294114390647)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_9677419495171 : Nat.Prime 9677419495171 := by
  apply lucas_primality 9677419495171 (2 : ZMod 9677419495171)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9677419495171 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((46082949977 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9677419495171)^4838709747585 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 9677419495171)^3225806498390 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 9677419495171)^1935483899034 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (2 : ZMod 9677419495171)^1382488499310 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 46082949977 := Nat.prime_eq_prime_of_dvd_pow hq prime_46082949977 hd
            subst q
            change (2 : ZMod 9677419495171)^210 ≠ 1
            reduce_mod_char
            decide

theorem prime_9685390482499 : Nat.Prime 9685390482499 := by
  apply lucas_primality 9685390482499 (2 : ZMod 9685390482499)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9685390482499 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((347 : ℕ)^1 * ((1361 : ℕ)^1 * ((3418049 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9685390482499)^4842695241249 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 9685390482499)^3228463494166 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 347 := Nat.prime_eq_prime_of_dvd_pow hq prime_347 hd
          subst q
          change (2 : ZMod 9685390482499)^27911788134 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1361 := Nat.prime_eq_prime_of_dvd_pow hq prime_1361 hd
            subst q
            change (2 : ZMod 9685390482499)^7116378018 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3418049 := Nat.prime_eq_prime_of_dvd_pow hq prime_3418049 hd
            subst q
            change (2 : ZMod 9685390482499)^2833602 ≠ 1
            reduce_mod_char
            decide

theorem prime_10090298369561 : Nat.Prime 10090298369561 := by
  apply lucas_primality 10090298369561 (6 : ZMod 10090298369561)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10090298369561 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((19 : ℕ)^1 * ((171869 : ℕ)^1 * ((77249 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 10090298369561)^5045149184780 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 10090298369561)^2018059673912 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (6 : ZMod 10090298369561)^531068335240 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 171869 := Nat.prime_eq_prime_of_dvd_pow hq prime_171869 hd
            subst q
            change (6 : ZMod 10090298369561)^58709240 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 77249 := Nat.prime_eq_prime_of_dvd_pow hq prime_77249 hd
            subst q
            change (6 : ZMod 10090298369561)^130620440 ≠ 1
            reduce_mod_char
            decide

theorem prime_10156755927781 : Nat.Prime 10156755927781 := by
  apply lucas_primality 10156755927781 (19 : ZMod 10156755927781)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10156755927781 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^2 * ((11 : ℕ)^1 * ((163 : ℕ)^1 * ((642253 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 10156755927781)^5078377963890 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 10156755927781)^3385585309260 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (19 : ZMod 10156755927781)^2031351185556 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (19 : ZMod 10156755927781)^1450965132540 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
              subst q
              change (19 : ZMod 10156755927781)^923341447980 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
                subst q
                change (19 : ZMod 10156755927781)^62311386060 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 642253 := Nat.prime_eq_prime_of_dvd_pow hq prime_642253 hd
                subst q
                change (19 : ZMod 10156755927781)^15814260 ≠ 1
                reduce_mod_char
                decide

theorem prime_10472451669643 : Nat.Prime 10472451669643 := by
  apply lucas_primality 10472451669643 (2 : ZMod 10472451669643)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10472451669643 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1745408611607 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 10472451669643)^5236225834821 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 10472451669643)^3490817223214 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1745408611607 := Nat.prime_eq_prime_of_dvd_pow hq prime_1745408611607 hd
        subst q
        change (2 : ZMod 10472451669643)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_10509215371267 : Nat.Prime 10509215371267 := by
  apply lucas_primality 10509215371267 (2 : ZMod 10509215371267)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10509215371267 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((396667 : ℕ)^1 * ((4415633 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 10509215371267)^5254607685633 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 10509215371267)^3503071790422 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 396667 := Nat.prime_eq_prime_of_dvd_pow hq prime_396667 hd
          subst q
          change (2 : ZMod 10509215371267)^26493798 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4415633 := Nat.prime_eq_prime_of_dvd_pow hq prime_4415633 hd
          subst q
          change (2 : ZMod 10509215371267)^2380002 ≠ 1
          reduce_mod_char
          decide

theorem prime_10527054320989 : Nat.Prime 10527054320989 := by
  apply lucas_primality 10527054320989 (2 : ZMod 10527054320989)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10527054320989 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((23 : ℕ)^1 * ((401 : ℕ)^1 * ((1321 : ℕ)^1 * ((24001 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 10527054320989)^5263527160494 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 10527054320989)^3509018106996 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 10527054320989)^457698013956 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 401 := Nat.prime_eq_prime_of_dvd_pow hq prime_401 hd
            subst q
            change (2 : ZMod 10527054320989)^26252005788 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1321 := Nat.prime_eq_prime_of_dvd_pow hq prime_1321 hd
              subst q
              change (2 : ZMod 10527054320989)^7969004028 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 24001 := Nat.prime_eq_prime_of_dvd_pow hq prime_24001 hd
              subst q
              change (2 : ZMod 10527054320989)^438608988 ≠ 1
              reduce_mod_char
              decide

theorem prime_10559904320297 : Nat.Prime 10559904320297 := by
  apply lucas_primality 10559904320297 (3 : ZMod 10559904320297)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10559904320297 - 1 = (2 : ℕ)^3 * ((1319988040037 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 10559904320297)^5279952160148 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1319988040037 := Nat.prime_eq_prime_of_dvd_pow hq prime_1319988040037 hd
      subst q
      change (3 : ZMod 10559904320297)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_10655863562077 : Nat.Prime 10655863562077 := by
  apply lucas_primality 10655863562077 (2 : ZMod 10655863562077)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10655863562077 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((6079 : ℕ)^1 * ((146074787 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 10655863562077)^5327931781038 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 10655863562077)^3551954520692 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 6079 := Nat.prime_eq_prime_of_dvd_pow hq prime_6079 hd
          subst q
          change (2 : ZMod 10655863562077)^1752897444 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 146074787 := Nat.prime_eq_prime_of_dvd_pow hq prime_146074787 hd
          subst q
          change (2 : ZMod 10655863562077)^72948 ≠ 1
          reduce_mod_char
          decide

theorem prime_10942526586671 : Nat.Prime 10942526586671 := by
  apply lucas_primality 10942526586671 (14 : ZMod 10942526586671)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10942526586671 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((17 : ℕ)^1 * ((19 : ℕ)^1 * ((47 : ℕ)^1 * ((71 : ℕ)^1 * ((145031 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 10942526586671)^5471263293335 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (14 : ZMod 10942526586671)^2188505317334 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (14 : ZMod 10942526586671)^1563218083810 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (14 : ZMod 10942526586671)^643678034510 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
              subst q
              change (14 : ZMod 10942526586671)^575922451930 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
                subst q
                change (14 : ZMod 10942526586671)^232819714610 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
                  subst q
                  change (14 : ZMod 10942526586671)^154120092770 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 145031 := Nat.prime_eq_prime_of_dvd_pow hq prime_145031 hd
                  subst q
                  change (14 : ZMod 10942526586671)^75449570 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_10970065149301 : Nat.Prime 10970065149301 := by
  apply lucas_primality 10970065149301 (7 : ZMod 10970065149301)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10970065149301 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^2 * ((12188961277 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 10970065149301)^5485032574650 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 10970065149301)^3656688383100 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 10970065149301)^2194013029860 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 12188961277 := Nat.prime_eq_prime_of_dvd_pow hq prime_12188961277 hd
          subst q
          change (7 : ZMod 10970065149301)^900 ≠ 1
          reduce_mod_char
          decide

theorem prime_11019262434907 : Nat.Prime 11019262434907 := by
  apply lucas_primality 11019262434907 (3 : ZMod 11019262434907)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11019262434907 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^2 * ((35831 : ℕ)^1 * ((423601 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 11019262434907)^5509631217453 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 11019262434907)^3673087478302 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 11019262434907)^1001751130446 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 35831 := Nat.prime_eq_prime_of_dvd_pow hq prime_35831 hd
            subst q
            change (3 : ZMod 11019262434907)^307534326 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 423601 := Nat.prime_eq_prime_of_dvd_pow hq prime_423601 hd
            subst q
            change (3 : ZMod 11019262434907)^26013306 ≠ 1
            reduce_mod_char
            decide

theorem prime_11190646504517 : Nat.Prime 11190646504517 := by
  apply lucas_primality 11190646504517 (2 : ZMod 11190646504517)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11190646504517 - 1 = (2 : ℕ)^2 * ((503 : ℕ)^1 * ((5561951543 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 11190646504517)^5595323252258 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 503 := Nat.prime_eq_prime_of_dvd_pow hq prime_503 hd
        subst q
        change (2 : ZMod 11190646504517)^22247806172 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5561951543 := Nat.prime_eq_prime_of_dvd_pow hq prime_5561951543 hd
        subst q
        change (2 : ZMod 11190646504517)^2012 ≠ 1
        reduce_mod_char
        decide

end LegendreK6.Pratt
