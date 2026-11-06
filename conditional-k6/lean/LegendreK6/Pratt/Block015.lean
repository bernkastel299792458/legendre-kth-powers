import LegendreK6.Pratt.Block014

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LegendreK6.Pratt

theorem prime_85304377 : Nat.Prime 85304377 := by
  apply lucas_primality 85304377 (5 : ZMod 85304377)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 85304377 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((19 : ℕ)^1 * ((127 : ℕ)^1 * ((491 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 85304377)^42652188 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 85304377)^28434792 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (5 : ZMod 85304377)^4489704 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
            subst q
            change (5 : ZMod 85304377)^671688 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 491 := Nat.prime_eq_prime_of_dvd_pow hq prime_491 hd
            subst q
            change (5 : ZMod 85304377)^173736 ≠ 1
            reduce_mod_char
            decide

theorem prime_85766147 : Nat.Prime 85766147 := by
  apply lucas_primality 85766147 (2 : ZMod 85766147)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 85766147 - 1 = (2 : ℕ)^1 * ((42883073 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 85766147)^42883073 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 42883073 := Nat.prime_eq_prime_of_dvd_pow hq prime_42883073 hd
      subst q
      change (2 : ZMod 85766147)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_86366257 : Nat.Prime 86366257 := by
  apply lucas_primality 86366257 (5 : ZMod 86366257)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 86366257 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((53 : ℕ)^1 * ((1997 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 86366257)^43183128 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 86366257)^28788752 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (5 : ZMod 86366257)^5080368 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
            subst q
            change (5 : ZMod 86366257)^1629552 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1997 := Nat.prime_eq_prime_of_dvd_pow hq prime_1997 hd
            subst q
            change (5 : ZMod 86366257)^43248 ≠ 1
            reduce_mod_char
            decide

theorem prime_86384689 : Nat.Prime 86384689 := by
  apply lucas_primality 86384689 (7 : ZMod 86384689)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 86384689 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((13 : ℕ)^2 * ((23 : ℕ)^1 * ((463 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 86384689)^43192344 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 86384689)^28794896 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (7 : ZMod 86384689)^6644976 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (7 : ZMod 86384689)^3755856 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 463 := Nat.prime_eq_prime_of_dvd_pow hq prime_463 hd
            subst q
            change (7 : ZMod 86384689)^186576 ≠ 1
            reduce_mod_char
            decide

theorem prime_86882561 : Nat.Prime 86882561 := by
  apply lucas_primality 86882561 (3 : ZMod 86882561)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 86882561 - 1 = (2 : ℕ)^8 * ((5 : ℕ)^1 * ((103 : ℕ)^1 * ((659 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 86882561)^43441280 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 86882561)^17376512 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
          subst q
          change (3 : ZMod 86882561)^843520 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 659 := Nat.prime_eq_prime_of_dvd_pow hq prime_659 hd
          subst q
          change (3 : ZMod 86882561)^131840 ≠ 1
          reduce_mod_char
          decide

theorem prime_87231917 : Nat.Prime 87231917 := by
  apply lucas_primality 87231917 (2 : ZMod 87231917)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 87231917 - 1 = (2 : ℕ)^2 * ((23 : ℕ)^1 * ((948173 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 87231917)^43615958 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (2 : ZMod 87231917)^3792692 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 948173 := Nat.prime_eq_prime_of_dvd_pow hq prime_948173 hd
        subst q
        change (2 : ZMod 87231917)^92 ≠ 1
        reduce_mod_char
        decide

theorem prime_87257593 : Nat.Prime 87257593 := by
  apply lucas_primality 87257593 (7 : ZMod 87257593)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 87257593 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((1211911 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 87257593)^43628796 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 87257593)^29085864 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1211911 := Nat.prime_eq_prime_of_dvd_pow hq prime_1211911 hd
        subst q
        change (7 : ZMod 87257593)^72 ≠ 1
        reduce_mod_char
        decide

theorem prime_88784503 : Nat.Prime 88784503 := by
  apply lucas_primality 88784503 (3 : ZMod 88784503)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 88784503 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((14797417 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 88784503)^44392251 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 88784503)^29594834 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 14797417 := Nat.prime_eq_prime_of_dvd_pow hq prime_14797417 hd
        subst q
        change (3 : ZMod 88784503)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_91297043 : Nat.Prime 91297043 := by
  apply lucas_primality 91297043 (2 : ZMod 91297043)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 91297043 - 1 = (2 : ℕ)^1 * ((293 : ℕ)^1 * ((155797 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 91297043)^45648521 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 293 := Nat.prime_eq_prime_of_dvd_pow hq prime_293 hd
        subst q
        change (2 : ZMod 91297043)^311594 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 155797 := Nat.prime_eq_prime_of_dvd_pow hq prime_155797 hd
        subst q
        change (2 : ZMod 91297043)^586 ≠ 1
        reduce_mod_char
        decide

theorem prime_93798253 : Nat.Prime 93798253 := by
  apply lucas_primality 93798253 (2 : ZMod 93798253)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 93798253 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((199 : ℕ)^1 * ((13093 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 93798253)^46899126 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 93798253)^31266084 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 199 := Nat.prime_eq_prime_of_dvd_pow hq prime_199 hd
          subst q
          change (2 : ZMod 93798253)^471348 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13093 := Nat.prime_eq_prime_of_dvd_pow hq prime_13093 hd
          subst q
          change (2 : ZMod 93798253)^7164 ≠ 1
          reduce_mod_char
          decide

theorem prime_94125169 : Nat.Prime 94125169 := by
  apply lucas_primality 94125169 (7 : ZMod 94125169)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 94125169 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((653647 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 94125169)^47062584 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 94125169)^31375056 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 653647 := Nat.prime_eq_prime_of_dvd_pow hq prime_653647 hd
        subst q
        change (7 : ZMod 94125169)^144 ≠ 1
        reduce_mod_char
        decide

theorem prime_94129247 : Nat.Prime 94129247 := by
  apply lucas_primality 94129247 (5 : ZMod 94129247)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 94129247 - 1 = (2 : ℕ)^1 * ((1129 : ℕ)^1 * ((41687 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 94129247)^47064623 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1129 := Nat.prime_eq_prime_of_dvd_pow hq prime_1129 hd
        subst q
        change (5 : ZMod 94129247)^83374 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 41687 := Nat.prime_eq_prime_of_dvd_pow hq prime_41687 hd
        subst q
        change (5 : ZMod 94129247)^2258 ≠ 1
        reduce_mod_char
        decide

theorem prime_95240291 : Nat.Prime 95240291 := by
  apply lucas_primality 95240291 (2 : ZMod 95240291)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 95240291 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((560237 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 95240291)^47620145 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 95240291)^19048058 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 95240291)^5602370 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 560237 := Nat.prime_eq_prime_of_dvd_pow hq prime_560237 hd
          subst q
          change (2 : ZMod 95240291)^170 ≠ 1
          reduce_mod_char
          decide

theorem prime_95636159 : Nat.Prime 95636159 := by
  apply lucas_primality 95636159 (11 : ZMod 95636159)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 95636159 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((1259 : ℕ)^1 * ((1999 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 95636159)^47818079 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (11 : ZMod 95636159)^5033482 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1259 := Nat.prime_eq_prime_of_dvd_pow hq prime_1259 hd
          subst q
          change (11 : ZMod 95636159)^75962 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1999 := Nat.prime_eq_prime_of_dvd_pow hq prime_1999 hd
          subst q
          change (11 : ZMod 95636159)^47842 ≠ 1
          reduce_mod_char
          decide

theorem prime_96676499 : Nat.Prime 96676499 := by
  apply lucas_primality 96676499 (2 : ZMod 96676499)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 96676499 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((1237 : ℕ)^1 * ((1699 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 96676499)^48338249 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (2 : ZMod 96676499)^4203326 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1237 := Nat.prime_eq_prime_of_dvd_pow hq prime_1237 hd
          subst q
          change (2 : ZMod 96676499)^78154 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1699 := Nat.prime_eq_prime_of_dvd_pow hq prime_1699 hd
          subst q
          change (2 : ZMod 96676499)^56902 ≠ 1
          reduce_mod_char
          decide

theorem prime_98862707 : Nat.Prime 98862707 := by
  apply lucas_primality 98862707 (2 : ZMod 98862707)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 98862707 - 1 = (2 : ℕ)^1 * ((193 : ℕ)^1 * ((256121 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 98862707)^49431353 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
        subst q
        change (2 : ZMod 98862707)^512242 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 256121 := Nat.prime_eq_prime_of_dvd_pow hq prime_256121 hd
        subst q
        change (2 : ZMod 98862707)^386 ≠ 1
        reduce_mod_char
        decide

theorem prime_98990681 : Nat.Prime 98990681 := by
  apply lucas_primality 98990681 (3 : ZMod 98990681)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 98990681 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((281 : ℕ)^1 * ((8807 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 98990681)^49495340 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 98990681)^19798136 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 281 := Nat.prime_eq_prime_of_dvd_pow hq prime_281 hd
          subst q
          change (3 : ZMod 98990681)^352280 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 8807 := Nat.prime_eq_prime_of_dvd_pow hq prime_8807 hd
          subst q
          change (3 : ZMod 98990681)^11240 ≠ 1
          reduce_mod_char
          decide

theorem prime_100454281 : Nat.Prime 100454281 := by
  apply lucas_primality 100454281 (13 : ZMod 100454281)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 100454281 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((271 : ℕ)^1 * ((3089 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 100454281)^50227140 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 100454281)^33484760 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 100454281)^20090856 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 271 := Nat.prime_eq_prime_of_dvd_pow hq prime_271 hd
            subst q
            change (13 : ZMod 100454281)^370680 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3089 := Nat.prime_eq_prime_of_dvd_pow hq prime_3089 hd
            subst q
            change (13 : ZMod 100454281)^32520 ≠ 1
            reduce_mod_char
            decide

theorem prime_100653193 : Nat.Prime 100653193 := by
  apply lucas_primality 100653193 (5 : ZMod 100653193)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 100653193 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^4 * ((17 : ℕ)^1 * ((9137 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 100653193)^50326596 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 100653193)^33551064 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (5 : ZMod 100653193)^5920776 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 9137 := Nat.prime_eq_prime_of_dvd_pow hq prime_9137 hd
          subst q
          change (5 : ZMod 100653193)^11016 ≠ 1
          reduce_mod_char
          decide

theorem prime_100853297 : Nat.Prime 100853297 := by
  apply lucas_primality 100853297 (3 : ZMod 100853297)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 100853297 - 1 = (2 : ℕ)^4 * ((73 : ℕ)^1 * ((79 : ℕ)^1 * ((1093 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 100853297)^50426648 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
        subst q
        change (3 : ZMod 100853297)^1381552 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (3 : ZMod 100853297)^1276624 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1093 := Nat.prime_eq_prime_of_dvd_pow hq prime_1093 hd
          subst q
          change (3 : ZMod 100853297)^92272 ≠ 1
          reduce_mod_char
          decide

theorem prime_101044051 : Nat.Prime 101044051 := by
  apply lucas_primality 101044051 (2 : ZMod 101044051)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 101044051 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((733 : ℕ)^1 * ((919 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 101044051)^50522025 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 101044051)^33681350 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 101044051)^20208810 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 733 := Nat.prime_eq_prime_of_dvd_pow hq prime_733 hd
            subst q
            change (2 : ZMod 101044051)^137850 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 919 := Nat.prime_eq_prime_of_dvd_pow hq prime_919 hd
            subst q
            change (2 : ZMod 101044051)^109950 ≠ 1
            reduce_mod_char
            decide

theorem prime_101845291 : Nat.Prime 101845291 := by
  apply lucas_primality 101845291 (2 : ZMod 101845291)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 101845291 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((3394843 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 101845291)^50922645 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 101845291)^33948430 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 101845291)^20369058 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3394843 := Nat.prime_eq_prime_of_dvd_pow hq prime_3394843 hd
          subst q
          change (2 : ZMod 101845291)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_101942707 : Nat.Prime 101942707 := by
  apply lucas_primality 101942707 (2 : ZMod 101942707)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 101942707 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((79 : ℕ)^1 * ((431 : ℕ)^1 * ((499 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 101942707)^50971353 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 101942707)^33980902 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (2 : ZMod 101942707)^1290414 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 431 := Nat.prime_eq_prime_of_dvd_pow hq prime_431 hd
            subst q
            change (2 : ZMod 101942707)^236526 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 499 := Nat.prime_eq_prime_of_dvd_pow hq prime_499 hd
            subst q
            change (2 : ZMod 101942707)^204294 ≠ 1
            reduce_mod_char
            decide

theorem prime_102100951 : Nat.Prime 102100951 := by
  apply lucas_primality 102100951 (12 : ZMod 102100951)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 102100951 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^2 * ((7 : ℕ)^1 * ((32413 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (12 : ZMod 102100951)^51050475 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (12 : ZMod 102100951)^34033650 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (12 : ZMod 102100951)^20420190 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (12 : ZMod 102100951)^14585850 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 32413 := Nat.prime_eq_prime_of_dvd_pow hq prime_32413 hd
            subst q
            change (12 : ZMod 102100951)^3150 ≠ 1
            reduce_mod_char
            decide

theorem prime_102591721 : Nat.Prime 102591721 := by
  apply lucas_primality 102591721 (31 : ZMod 102591721)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 102591721 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((3701 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (31 : ZMod 102591721)^51295860 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (31 : ZMod 102591721)^34197240 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (31 : ZMod 102591721)^20518344 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (31 : ZMod 102591721)^14655960 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
              subst q
              change (31 : ZMod 102591721)^9326520 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 3701 := Nat.prime_eq_prime_of_dvd_pow hq prime_3701 hd
              subst q
              change (31 : ZMod 102591721)^27720 ≠ 1
              reduce_mod_char
              decide

theorem prime_102955891 : Nat.Prime 102955891 := by
  apply lucas_primality 102955891 (11 : ZMod 102955891)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 102955891 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((157 : ℕ)^1 * ((21859 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 102955891)^51477945 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 102955891)^34318630 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 102955891)^20591178 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
            subst q
            change (11 : ZMod 102955891)^655770 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 21859 := Nat.prime_eq_prime_of_dvd_pow hq prime_21859 hd
            subst q
            change (11 : ZMod 102955891)^4710 ≠ 1
            reduce_mod_char
            decide

theorem prime_103775407 : Nat.Prime 103775407 := by
  apply lucas_primality 103775407 (3 : ZMod 103775407)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 103775407 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((419 : ℕ)^1 * ((5897 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 103775407)^51887703 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 103775407)^34591802 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 103775407)^14825058 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 419 := Nat.prime_eq_prime_of_dvd_pow hq prime_419 hd
            subst q
            change (3 : ZMod 103775407)^247674 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 5897 := Nat.prime_eq_prime_of_dvd_pow hq prime_5897 hd
            subst q
            change (3 : ZMod 103775407)^17598 ≠ 1
            reduce_mod_char
            decide

theorem prime_104931949 : Nat.Prime 104931949 := by
  apply lucas_primality 104931949 (2 : ZMod 104931949)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 104931949 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((179 : ℕ)^1 * ((4441 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 104931949)^52465974 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 104931949)^34977316 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 104931949)^9539268 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 179 := Nat.prime_eq_prime_of_dvd_pow hq prime_179 hd
            subst q
            change (2 : ZMod 104931949)^586212 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 4441 := Nat.prime_eq_prime_of_dvd_pow hq prime_4441 hd
            subst q
            change (2 : ZMod 104931949)^23628 ≠ 1
            reduce_mod_char
            decide

theorem prime_105407297 : Nat.Prime 105407297 := by
  apply lucas_primality 105407297 (3 : ZMod 105407297)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 105407297 - 1 = (2 : ℕ)^6 * ((1646989 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 105407297)^52703648 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1646989 := Nat.prime_eq_prime_of_dvd_pow hq prime_1646989 hd
      subst q
      change (3 : ZMod 105407297)^64 ≠ 1
      reduce_mod_char
      decide

theorem prime_105499663 : Nat.Prime 105499663 := by
  apply lucas_primality 105499663 (3 : ZMod 105499663)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 105499663 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((127 : ℕ)^1 * ((138451 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 105499663)^52749831 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 105499663)^35166554 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
          subst q
          change (3 : ZMod 105499663)^830706 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 138451 := Nat.prime_eq_prime_of_dvd_pow hq prime_138451 hd
          subst q
          change (3 : ZMod 105499663)^762 ≠ 1
          reduce_mod_char
          decide

theorem prime_106473683 : Nat.Prime 106473683 := by
  apply lucas_primality 106473683 (2 : ZMod 106473683)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 106473683 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((19 : ℕ)^1 * ((400277 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 106473683)^53236841 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 106473683)^15210526 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 106473683)^5603878 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 400277 := Nat.prime_eq_prime_of_dvd_pow hq prime_400277 hd
          subst q
          change (2 : ZMod 106473683)^266 ≠ 1
          reduce_mod_char
          decide

theorem prime_106693969 : Nat.Prime 106693969 := by
  apply lucas_primality 106693969 (11 : ZMod 106693969)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 106693969 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((116989 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 106693969)^53346984 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 106693969)^35564656 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (11 : ZMod 106693969)^5615472 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 116989 := Nat.prime_eq_prime_of_dvd_pow hq prime_116989 hd
          subst q
          change (11 : ZMod 106693969)^912 ≠ 1
          reduce_mod_char
          decide

theorem prime_106845083 : Nat.Prime 106845083 := by
  apply lucas_primality 106845083 (2 : ZMod 106845083)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 106845083 - 1 = (2 : ℕ)^1 * ((53422541 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 106845083)^53422541 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 53422541 := Nat.prime_eq_prime_of_dvd_pow hq prime_53422541 hd
      subst q
      change (2 : ZMod 106845083)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_108058063 : Nat.Prime 108058063 := by
  apply lucas_primality 108058063 (3 : ZMod 108058063)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 108058063 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((2572811 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 108058063)^54029031 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 108058063)^36019354 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 108058063)^15436866 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2572811 := Nat.prime_eq_prime_of_dvd_pow hq prime_2572811 hd
          subst q
          change (3 : ZMod 108058063)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_109035607 : Nat.Prime 109035607 := by
  apply lucas_primality 109035607 (5 : ZMod 109035607)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 109035607 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((83 : ℕ)^1 * ((218947 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 109035607)^54517803 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 109035607)^36345202 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
          subst q
          change (5 : ZMod 109035607)^1313682 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 218947 := Nat.prime_eq_prime_of_dvd_pow hq prime_218947 hd
          subst q
          change (5 : ZMod 109035607)^498 ≠ 1
          reduce_mod_char
          decide

theorem prime_109227163 : Nat.Prime 109227163 := by
  apply lucas_primality 109227163 (3 : ZMod 109227163)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 109227163 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((19 : ℕ)^1 * ((87103 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 109227163)^54613581 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 109227163)^36409054 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 109227163)^9929742 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (3 : ZMod 109227163)^5748798 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 87103 := Nat.prime_eq_prime_of_dvd_pow hq prime_87103 hd
            subst q
            change (3 : ZMod 109227163)^1254 ≠ 1
            reduce_mod_char
            decide

theorem prime_109369801 : Nat.Prime 109369801 := by
  apply lucas_primality 109369801 (11 : ZMod 109369801)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 109369801 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((5 : ℕ)^2 * ((60761 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 109369801)^54684900 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 109369801)^36456600 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 109369801)^21873960 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 60761 := Nat.prime_eq_prime_of_dvd_pow hq prime_60761 hd
          subst q
          change (11 : ZMod 109369801)^1800 ≠ 1
          reduce_mod_char
          decide

theorem prime_110024413 : Nat.Prime 110024413 := by
  apply lucas_primality 110024413 (5 : ZMod 110024413)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 110024413 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((9168701 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 110024413)^55012206 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 110024413)^36674804 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 9168701 := Nat.prime_eq_prime_of_dvd_pow hq prime_9168701 hd
        subst q
        change (5 : ZMod 110024413)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_111186191 : Nat.Prime 111186191 := by
  apply lucas_primality 111186191 (7 : ZMod 111186191)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 111186191 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((307 : ℕ)^1 * ((36217 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 111186191)^55593095 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 111186191)^22237238 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 307 := Nat.prime_eq_prime_of_dvd_pow hq prime_307 hd
          subst q
          change (7 : ZMod 111186191)^362170 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 36217 := Nat.prime_eq_prime_of_dvd_pow hq prime_36217 hd
          subst q
          change (7 : ZMod 111186191)^3070 ≠ 1
          reduce_mod_char
          decide

theorem prime_111304829 : Nat.Prime 111304829 := by
  apply lucas_primality 111304829 (2 : ZMod 111304829)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 111304829 - 1 = (2 : ℕ)^2 * ((101 : ℕ)^1 * ((137 : ℕ)^1 * ((2011 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 111304829)^55652414 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
        subst q
        change (2 : ZMod 111304829)^1102028 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
          subst q
          change (2 : ZMod 111304829)^812444 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2011 := Nat.prime_eq_prime_of_dvd_pow hq prime_2011 hd
          subst q
          change (2 : ZMod 111304829)^55348 ≠ 1
          reduce_mod_char
          decide

theorem prime_112930057 : Nat.Prime 112930057 := by
  apply lucas_primality 112930057 (5 : ZMod 112930057)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 112930057 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((743 : ℕ)^1 * ((2111 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 112930057)^56465028 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 112930057)^37643352 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 743 := Nat.prime_eq_prime_of_dvd_pow hq prime_743 hd
          subst q
          change (5 : ZMod 112930057)^151992 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2111 := Nat.prime_eq_prime_of_dvd_pow hq prime_2111 hd
          subst q
          change (5 : ZMod 112930057)^53496 ≠ 1
          reduce_mod_char
          decide

theorem prime_113340673 : Nat.Prime 113340673 := by
  apply lucas_primality 113340673 (5 : ZMod 113340673)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 113340673 - 1 = (2 : ℕ)^8 * ((3 : ℕ)^2 * ((49193 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 113340673)^56670336 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 113340673)^37780224 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 49193 := Nat.prime_eq_prime_of_dvd_pow hq prime_49193 hd
        subst q
        change (5 : ZMod 113340673)^2304 ≠ 1
        reduce_mod_char
        decide

theorem prime_113379941 : Nat.Prime 113379941 := by
  apply lucas_primality 113379941 (2 : ZMod 113379941)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 113379941 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((5668997 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 113379941)^56689970 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 113379941)^22675988 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5668997 := Nat.prime_eq_prime_of_dvd_pow hq prime_5668997 hd
        subst q
        change (2 : ZMod 113379941)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_114118811 : Nat.Prime 114118811 := by
  apply lucas_primality 114118811 (2 : ZMod 114118811)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 114118811 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((877837 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 114118811)^57059405 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 114118811)^22823762 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 114118811)^8778370 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 877837 := Nat.prime_eq_prime_of_dvd_pow hq prime_877837 hd
          subst q
          change (2 : ZMod 114118811)^130 ≠ 1
          reduce_mod_char
          decide

theorem prime_114321269 : Nat.Prime 114321269 := by
  apply lucas_primality 114321269 (2 : ZMod 114321269)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 114321269 - 1 = (2 : ℕ)^2 * ((37 : ℕ)^1 * ((772441 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 114321269)^57160634 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (2 : ZMod 114321269)^3089764 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 772441 := Nat.prime_eq_prime_of_dvd_pow hq prime_772441 hd
        subst q
        change (2 : ZMod 114321269)^148 ≠ 1
        reduce_mod_char
        decide

theorem prime_120926161 : Nat.Prime 120926161 := by
  apply lucas_primality 120926161 (14 : ZMod 120926161)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 120926161 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((167953 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 120926161)^60463080 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 120926161)^40308720 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (14 : ZMod 120926161)^24185232 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 167953 := Nat.prime_eq_prime_of_dvd_pow hq prime_167953 hd
          subst q
          change (14 : ZMod 120926161)^720 ≠ 1
          reduce_mod_char
          decide

theorem prime_122489863 : Nat.Prime 122489863 := by
  apply lucas_primality 122489863 (6 : ZMod 122489863)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 122489863 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((109171 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 122489863)^61244931 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 122489863)^40829954 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (6 : ZMod 122489863)^11135442 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (6 : ZMod 122489863)^7205286 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 109171 := Nat.prime_eq_prime_of_dvd_pow hq prime_109171 hd
            subst q
            change (6 : ZMod 122489863)^1122 ≠ 1
            reduce_mod_char
            decide

theorem prime_124194937 : Nat.Prime 124194937 := by
  apply lucas_primality 124194937 (23 : ZMod 124194937)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 124194937 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((29 : ℕ)^1 * ((178441 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (23 : ZMod 124194937)^62097468 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (23 : ZMod 124194937)^41398312 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (23 : ZMod 124194937)^4282584 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 178441 := Nat.prime_eq_prime_of_dvd_pow hq prime_178441 hd
          subst q
          change (23 : ZMod 124194937)^696 ≠ 1
          reduce_mod_char
          decide

theorem prime_125128153 : Nat.Prime 125128153 := by
  apply lucas_primality 125128153 (7 : ZMod 125128153)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 125128153 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^4 * ((31 : ℕ)^1 * ((6229 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 125128153)^62564076 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 125128153)^41709384 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (7 : ZMod 125128153)^4036392 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 6229 := Nat.prime_eq_prime_of_dvd_pow hq prime_6229 hd
          subst q
          change (7 : ZMod 125128153)^20088 ≠ 1
          reduce_mod_char
          decide

theorem prime_125349691 : Nat.Prime 125349691 := by
  apply lucas_primality 125349691 (2 : ZMod 125349691)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 125349691 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((1321 : ℕ)^1 * ((3163 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 125349691)^62674845 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 125349691)^41783230 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 125349691)^25069938 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1321 := Nat.prime_eq_prime_of_dvd_pow hq prime_1321 hd
            subst q
            change (2 : ZMod 125349691)^94890 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3163 := Nat.prime_eq_prime_of_dvd_pow hq prime_3163 hd
            subst q
            change (2 : ZMod 125349691)^39630 ≠ 1
            reduce_mod_char
            decide

theorem prime_125700697 : Nat.Prime 125700697 := by
  apply lucas_primality 125700697 (7 : ZMod 125700697)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 125700697 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((43 : ℕ)^1 * ((3691 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 125700697)^62850348 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 125700697)^41900232 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (7 : ZMod 125700697)^11427336 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (7 : ZMod 125700697)^2923272 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3691 := Nat.prime_eq_prime_of_dvd_pow hq prime_3691 hd
            subst q
            change (7 : ZMod 125700697)^34056 ≠ 1
            reduce_mod_char
            decide

theorem prime_128412593 : Nat.Prime 128412593 := by
  apply lucas_primality 128412593 (3 : ZMod 128412593)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 128412593 - 1 = (2 : ℕ)^4 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((104231 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 128412593)^64206296 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 128412593)^18344656 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 128412593)^11673872 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 104231 := Nat.prime_eq_prime_of_dvd_pow hq prime_104231 hd
          subst q
          change (3 : ZMod 128412593)^1232 ≠ 1
          reduce_mod_char
          decide

theorem prime_129630433 : Nat.Prime 129630433 := by
  apply lucas_primality 129630433 (5 : ZMod 129630433)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 129630433 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((1350317 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 129630433)^64815216 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 129630433)^43210144 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1350317 := Nat.prime_eq_prime_of_dvd_pow hq prime_1350317 hd
        subst q
        change (5 : ZMod 129630433)^96 ≠ 1
        reduce_mod_char
        decide

theorem prime_130476043 : Nat.Prime 130476043 := by
  apply lucas_primality 130476043 (3 : ZMod 130476043)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 130476043 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((47 : ℕ)^1 * ((101 : ℕ)^1 * ((509 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 130476043)^65238021 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 130476043)^43492014 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (3 : ZMod 130476043)^2776086 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
            subst q
            change (3 : ZMod 130476043)^1291842 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 509 := Nat.prime_eq_prime_of_dvd_pow hq prime_509 hd
            subst q
            change (3 : ZMod 130476043)^256338 ≠ 1
            reduce_mod_char
            decide

theorem prime_131764219 : Nat.Prime 131764219 := by
  apply lucas_primality 131764219 (2 : ZMod 131764219)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 131764219 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((47 : ℕ)^1 * ((97 : ℕ)^1 * ((4817 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 131764219)^65882109 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 131764219)^43921406 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (2 : ZMod 131764219)^2803494 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
            subst q
            change (2 : ZMod 131764219)^1358394 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 4817 := Nat.prime_eq_prime_of_dvd_pow hq prime_4817 hd
            subst q
            change (2 : ZMod 131764219)^27354 ≠ 1
            reduce_mod_char
            decide

theorem prime_132273709 : Nat.Prime 132273709 := by
  apply lucas_primality 132273709 (2 : ZMod 132273709)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 132273709 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((41 : ℕ)^1 * ((193 : ℕ)^1 * ((199 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 132273709)^66136854 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 132273709)^44091236 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 132273709)^18896244 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (2 : ZMod 132273709)^3226188 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
              subst q
              change (2 : ZMod 132273709)^685356 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 199 := Nat.prime_eq_prime_of_dvd_pow hq prime_199 hd
              subst q
              change (2 : ZMod 132273709)^664692 ≠ 1
              reduce_mod_char
              decide

theorem prime_134402423 : Nat.Prime 134402423 := by
  apply lucas_primality 134402423 (5 : ZMod 134402423)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 134402423 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((31 : ℕ)^1 * ((47 : ℕ)^1 * ((599 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 134402423)^67201211 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 134402423)^19200346 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 134402423)^12218402 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (5 : ZMod 134402423)^4335562 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
              subst q
              change (5 : ZMod 134402423)^2859626 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 599 := Nat.prime_eq_prime_of_dvd_pow hq prime_599 hd
              subst q
              change (5 : ZMod 134402423)^224378 ≠ 1
              reduce_mod_char
              decide

theorem prime_135794977 : Nat.Prime 135794977 := by
  apply lucas_primality 135794977 (10 : ZMod 135794977)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 135794977 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((74449 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 135794977)^67897488 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 135794977)^45264992 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (10 : ZMod 135794977)^7147104 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 74449 := Nat.prime_eq_prime_of_dvd_pow hq prime_74449 hd
          subst q
          change (10 : ZMod 135794977)^1824 ≠ 1
          reduce_mod_char
          decide

theorem prime_136645973 : Nat.Prime 136645973 := by
  apply lucas_primality 136645973 (2 : ZMod 136645973)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 136645973 - 1 = (2 : ℕ)^2 * ((89 : ℕ)^1 * ((383837 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 136645973)^68322986 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
        subst q
        change (2 : ZMod 136645973)^1535348 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 383837 := Nat.prime_eq_prime_of_dvd_pow hq prime_383837 hd
        subst q
        change (2 : ZMod 136645973)^356 ≠ 1
        reduce_mod_char
        decide

theorem prime_138062857 : Nat.Prime 138062857 := by
  apply lucas_primality 138062857 (5 : ZMod 138062857)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 138062857 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((73 : ℕ)^1 * ((78803 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 138062857)^69031428 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 138062857)^46020952 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
          subst q
          change (5 : ZMod 138062857)^1891272 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 78803 := Nat.prime_eq_prime_of_dvd_pow hq prime_78803 hd
          subst q
          change (5 : ZMod 138062857)^1752 ≠ 1
          reduce_mod_char
          decide

theorem prime_141186713 : Nat.Prime 141186713 := by
  apply lucas_primality 141186713 (3 : ZMod 141186713)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 141186713 - 1 = (2 : ℕ)^3 * ((17648339 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 141186713)^70593356 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 17648339 := Nat.prime_eq_prime_of_dvd_pow hq prime_17648339 hd
      subst q
      change (3 : ZMod 141186713)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_141485551 : Nat.Prime 141485551 := by
  apply lucas_primality 141485551 (3 : ZMod 141485551)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 141485551 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((31 : ℕ)^1 * ((30427 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 141485551)^70742775 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 141485551)^47161850 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 141485551)^28297110 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (3 : ZMod 141485551)^4564050 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 30427 := Nat.prime_eq_prime_of_dvd_pow hq prime_30427 hd
            subst q
            change (3 : ZMod 141485551)^4650 ≠ 1
            reduce_mod_char
            decide

theorem prime_141772249 : Nat.Prime 141772249 := by
  apply lucas_primality 141772249 (14 : ZMod 141772249)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 141772249 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((17 : ℕ)^1 * ((38609 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 141772249)^70886124 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 141772249)^47257416 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (14 : ZMod 141772249)^8339544 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 38609 := Nat.prime_eq_prime_of_dvd_pow hq prime_38609 hd
          subst q
          change (14 : ZMod 141772249)^3672 ≠ 1
          reduce_mod_char
          decide

theorem prime_142381517 : Nat.Prime 142381517 := by
  apply lucas_primality 142381517 (2 : ZMod 142381517)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 142381517 - 1 = (2 : ℕ)^2 * ((19 : ℕ)^1 * ((1873441 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 142381517)^71190758 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 142381517)^7493764 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1873441 := Nat.prime_eq_prime_of_dvd_pow hq prime_1873441 hd
        subst q
        change (2 : ZMod 142381517)^76 ≠ 1
        reduce_mod_char
        decide

theorem prime_143480933 : Nat.Prime 143480933 := by
  apply lucas_primality 143480933 (2 : ZMod 143480933)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 143480933 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((19 : ℕ)^1 * ((269701 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 143480933)^71740466 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 143480933)^20497276 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 143480933)^7551628 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 269701 := Nat.prime_eq_prime_of_dvd_pow hq prime_269701 hd
          subst q
          change (2 : ZMod 143480933)^532 ≠ 1
          reduce_mod_char
          decide

theorem prime_146074787 : Nat.Prime 146074787 := by
  apply lucas_primality 146074787 (2 : ZMod 146074787)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 146074787 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((510751 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 146074787)^73037393 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 146074787)^13279526 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 146074787)^11236522 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 510751 := Nat.prime_eq_prime_of_dvd_pow hq prime_510751 hd
          subst q
          change (2 : ZMod 146074787)^286 ≠ 1
          reduce_mod_char
          decide

theorem prime_146304649 : Nat.Prime 146304649 := by
  apply lucas_primality 146304649 (22 : ZMod 146304649)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 146304649 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((331 : ℕ)^1 * ((877 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (22 : ZMod 146304649)^73152324 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (22 : ZMod 146304649)^48768216 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (22 : ZMod 146304649)^20900664 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 331 := Nat.prime_eq_prime_of_dvd_pow hq prime_331 hd
            subst q
            change (22 : ZMod 146304649)^442008 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 877 := Nat.prime_eq_prime_of_dvd_pow hq prime_877 hd
            subst q
            change (22 : ZMod 146304649)^166824 ≠ 1
            reduce_mod_char
            decide

theorem prime_148035893 : Nat.Prime 148035893 := by
  apply lucas_primality 148035893 (2 : ZMod 148035893)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 148035893 - 1 = (2 : ℕ)^2 * ((757 : ℕ)^1 * ((48889 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 148035893)^74017946 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 757 := Nat.prime_eq_prime_of_dvd_pow hq prime_757 hd
        subst q
        change (2 : ZMod 148035893)^195556 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 48889 := Nat.prime_eq_prime_of_dvd_pow hq prime_48889 hd
        subst q
        change (2 : ZMod 148035893)^3028 ≠ 1
        reduce_mod_char
        decide

theorem prime_148488661 : Nat.Prime 148488661 := by
  apply lucas_primality 148488661 (6 : ZMod 148488661)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 148488661 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((83 : ℕ)^1 * ((3313 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 148488661)^74244330 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 148488661)^49496220 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 148488661)^29697732 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
            subst q
            change (6 : ZMod 148488661)^1789020 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3313 := Nat.prime_eq_prime_of_dvd_pow hq prime_3313 hd
            subst q
            change (6 : ZMod 148488661)^44820 ≠ 1
            reduce_mod_char
            decide

theorem prime_149384467 : Nat.Prime 149384467 := by
  apply lucas_primality 149384467 (2 : ZMod 149384467)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 149384467 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((37 : ℕ)^1 * ((971 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 149384467)^74692233 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 149384467)^49794822 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 149384467)^21340638 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (2 : ZMod 149384467)^13580406 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
              subst q
              change (2 : ZMod 149384467)^4037418 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 971 := Nat.prime_eq_prime_of_dvd_pow hq prime_971 hd
              subst q
              change (2 : ZMod 149384467)^153846 ≠ 1
              reduce_mod_char
              decide

theorem prime_150841921 : Nat.Prime 150841921 := by
  apply lucas_primality 150841921 (7 : ZMod 150841921)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 150841921 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((157127 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 150841921)^75420960 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 150841921)^50280640 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 150841921)^30168384 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 157127 := Nat.prime_eq_prime_of_dvd_pow hq prime_157127 hd
          subst q
          change (7 : ZMod 150841921)^960 ≠ 1
          reduce_mod_char
          decide

theorem prime_152335591 : Nat.Prime 152335591 := by
  apply lucas_primality 152335591 (6 : ZMod 152335591)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 152335591 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((97 : ℕ)^1 * ((4759 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 152335591)^76167795 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 152335591)^50778530 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 152335591)^30467118 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (6 : ZMod 152335591)^13848690 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
              subst q
              change (6 : ZMod 152335591)^1570470 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 4759 := Nat.prime_eq_prime_of_dvd_pow hq prime_4759 hd
              subst q
              change (6 : ZMod 152335591)^32010 ≠ 1
              reduce_mod_char
              decide

theorem prime_152347603 : Nat.Prime 152347603 := by
  apply lucas_primality 152347603 (3 : ZMod 152347603)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 152347603 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((2308297 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 152347603)^76173801 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 152347603)^50782534 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 152347603)^13849782 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2308297 := Nat.prime_eq_prime_of_dvd_pow hq prime_2308297 hd
          subst q
          change (3 : ZMod 152347603)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_154317029 : Nat.Prime 154317029 := by
  apply lucas_primality 154317029 (2 : ZMod 154317029)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 154317029 - 1 = (2 : ℕ)^2 * ((23 : ℕ)^1 * ((1677359 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 154317029)^77158514 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (2 : ZMod 154317029)^6709436 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1677359 := Nat.prime_eq_prime_of_dvd_pow hq prime_1677359 hd
        subst q
        change (2 : ZMod 154317029)^92 ≠ 1
        reduce_mod_char
        decide

theorem prime_155706013 : Nat.Prime 155706013 := by
  apply lucas_primality 155706013 (2 : ZMod 155706013)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 155706013 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((56171 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 155706013)^77853006 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 155706013)^51902004 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 155706013)^22243716 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (2 : ZMod 155706013)^14155092 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 56171 := Nat.prime_eq_prime_of_dvd_pow hq prime_56171 hd
            subst q
            change (2 : ZMod 155706013)^2772 ≠ 1
            reduce_mod_char
            decide

theorem prime_157605187 : Nat.Prime 157605187 := by
  apply lucas_primality 157605187 (2 : ZMod 157605187)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 157605187 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((26267531 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 157605187)^78802593 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 157605187)^52535062 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 26267531 := Nat.prime_eq_prime_of_dvd_pow hq prime_26267531 hd
        subst q
        change (2 : ZMod 157605187)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_158014867 : Nat.Prime 158014867 := by
  apply lucas_primality 158014867 (2 : ZMod 158014867)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 158014867 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((26335811 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 158014867)^79007433 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 158014867)^52671622 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 26335811 := Nat.prime_eq_prime_of_dvd_pow hq prime_26335811 hd
        subst q
        change (2 : ZMod 158014867)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_159204917 : Nat.Prime 159204917 := by
  apply lucas_primality 159204917 (2 : ZMod 159204917)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 159204917 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((419 : ℕ)^1 * ((7307 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 159204917)^79602458 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 159204917)^12246532 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 419 := Nat.prime_eq_prime_of_dvd_pow hq prime_419 hd
          subst q
          change (2 : ZMod 159204917)^379964 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7307 := Nat.prime_eq_prime_of_dvd_pow hq prime_7307 hd
          subst q
          change (2 : ZMod 159204917)^21788 ≠ 1
          reduce_mod_char
          decide

theorem prime_160464613 : Nat.Prime 160464613 := by
  apply lucas_primality 160464613 (6 : ZMod 160464613)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 160464613 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((11 : ℕ)^1 * ((24809 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 160464613)^80232306 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 160464613)^53488204 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 160464613)^22923516 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (6 : ZMod 160464613)^14587692 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 24809 := Nat.prime_eq_prime_of_dvd_pow hq prime_24809 hd
            subst q
            change (6 : ZMod 160464613)^6468 ≠ 1
            reduce_mod_char
            decide

theorem prime_162789457 : Nat.Prime 162789457 := by
  apply lucas_primality 162789457 (7 : ZMod 162789457)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 162789457 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((367 : ℕ)^1 * ((9241 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 162789457)^81394728 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 162789457)^54263152 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 367 := Nat.prime_eq_prime_of_dvd_pow hq prime_367 hd
          subst q
          change (7 : ZMod 162789457)^443568 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 9241 := Nat.prime_eq_prime_of_dvd_pow hq prime_9241 hd
          subst q
          change (7 : ZMod 162789457)^17616 ≠ 1
          reduce_mod_char
          decide

theorem prime_164994793 : Nat.Prime 164994793 := by
  apply lucas_primality 164994793 (5 : ZMod 164994793)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 164994793 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((404399 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 164994793)^82497396 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 164994793)^54998264 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (5 : ZMod 164994793)^9705576 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 404399 := Nat.prime_eq_prime_of_dvd_pow hq prime_404399 hd
          subst q
          change (5 : ZMod 164994793)^408 ≠ 1
          reduce_mod_char
          decide

theorem prime_166905787 : Nat.Prime 166905787 := by
  apply lucas_primality 166905787 (3 : ZMod 166905787)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 166905787 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((4651 : ℕ)^1 * ((5981 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 166905787)^83452893 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 166905787)^55635262 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 4651 := Nat.prime_eq_prime_of_dvd_pow hq prime_4651 hd
          subst q
          change (3 : ZMod 166905787)^35886 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 5981 := Nat.prime_eq_prime_of_dvd_pow hq prime_5981 hd
          subst q
          change (3 : ZMod 166905787)^27906 ≠ 1
          reduce_mod_char
          decide

theorem prime_168465763 : Nat.Prime 168465763 := by
  apply lucas_primality 168465763 (2 : ZMod 168465763)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 168465763 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((79 : ℕ)^1 * ((118471 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 168465763)^84232881 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 168465763)^56155254 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (2 : ZMod 168465763)^2132478 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 118471 := Nat.prime_eq_prime_of_dvd_pow hq prime_118471 hd
          subst q
          change (2 : ZMod 168465763)^1422 ≠ 1
          reduce_mod_char
          decide

theorem prime_171266531 : Nat.Prime 171266531 := by
  apply lucas_primality 171266531 (2 : ZMod 171266531)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 171266531 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((17126653 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 171266531)^85633265 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 171266531)^34253306 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 17126653 := Nat.prime_eq_prime_of_dvd_pow hq prime_17126653 hd
        subst q
        change (2 : ZMod 171266531)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_172538251 : Nat.Prime 172538251 := by
  apply lucas_primality 172538251 (10 : ZMod 172538251)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 172538251 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^3 * ((31 : ℕ)^1 * ((41 : ℕ)^1 * ((181 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 172538251)^86269125 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 172538251)^57512750 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 172538251)^34507650 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (10 : ZMod 172538251)^5565750 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
              subst q
              change (10 : ZMod 172538251)^4208250 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 181 := Nat.prime_eq_prime_of_dvd_pow hq prime_181 hd
              subst q
              change (10 : ZMod 172538251)^953250 ≠ 1
              reduce_mod_char
              decide

theorem prime_176939197 : Nat.Prime 176939197 := by
  apply lucas_primality 176939197 (2 : ZMod 176939197)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 176939197 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((17 : ℕ)^1 * ((31 : ℕ)^1 * ((571 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 176939197)^88469598 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 176939197)^58979732 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 176939197)^25277028 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (2 : ZMod 176939197)^10408188 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
              subst q
              change (2 : ZMod 176939197)^5707716 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 571 := Nat.prime_eq_prime_of_dvd_pow hq prime_571 hd
              subst q
              change (2 : ZMod 176939197)^309876 ≠ 1
              reduce_mod_char
              decide

theorem prime_178453213 : Nat.Prime 178453213 := by
  apply lucas_primality 178453213 (15 : ZMod 178453213)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 178453213 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((2124443 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (15 : ZMod 178453213)^89226606 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (15 : ZMod 178453213)^59484404 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (15 : ZMod 178453213)^25493316 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2124443 := Nat.prime_eq_prime_of_dvd_pow hq prime_2124443 hd
          subst q
          change (15 : ZMod 178453213)^84 ≠ 1
          reduce_mod_char
          decide

theorem prime_183745999 : Nat.Prime 183745999 := by
  apply lucas_primality 183745999 (6 : ZMod 183745999)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 183745999 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((19 : ℕ)^1 * ((537269 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 183745999)^91872999 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 183745999)^61248666 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (6 : ZMod 183745999)^9670842 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 537269 := Nat.prime_eq_prime_of_dvd_pow hq prime_537269 hd
          subst q
          change (6 : ZMod 183745999)^342 ≠ 1
          reduce_mod_char
          decide

theorem prime_185165837 : Nat.Prime 185165837 := by
  apply lucas_primality 185165837 (2 : ZMod 185165837)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 185165837 - 1 = (2 : ℕ)^2 * ((17 : ℕ)^1 * ((59 : ℕ)^1 * ((46153 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 185165837)^92582918 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 185165837)^10892108 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (2 : ZMod 185165837)^3138404 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 46153 := Nat.prime_eq_prime_of_dvd_pow hq prime_46153 hd
          subst q
          change (2 : ZMod 185165837)^4012 ≠ 1
          reduce_mod_char
          decide

theorem prime_186195587 : Nat.Prime 186195587 := by
  apply lucas_primality 186195587 (2 : ZMod 186195587)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 186195587 - 1 = (2 : ℕ)^1 * ((191 : ℕ)^1 * ((487423 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 186195587)^93097793 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
        subst q
        change (2 : ZMod 186195587)^974846 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 487423 := Nat.prime_eq_prime_of_dvd_pow hq prime_487423 hd
        subst q
        change (2 : ZMod 186195587)^382 ≠ 1
        reduce_mod_char
        decide

theorem prime_186771731 : Nat.Prime 186771731 := by
  apply lucas_primality 186771731 (6 : ZMod 186771731)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 186771731 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((23 : ℕ)^1 * ((812051 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 186771731)^93385865 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 186771731)^37354346 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (6 : ZMod 186771731)^8120510 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 812051 := Nat.prime_eq_prime_of_dvd_pow hq prime_812051 hd
          subst q
          change (6 : ZMod 186771731)^230 ≠ 1
          reduce_mod_char
          decide

theorem prime_190833787 : Nat.Prime 190833787 := by
  apply lucas_primality 190833787 (2 : ZMod 190833787)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 190833787 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((11 : ℕ)^1 * ((13 : ℕ)^2 * ((1901 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 190833787)^95416893 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 190833787)^63611262 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 190833787)^17348526 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (2 : ZMod 190833787)^14679522 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1901 := Nat.prime_eq_prime_of_dvd_pow hq prime_1901 hd
            subst q
            change (2 : ZMod 190833787)^100386 ≠ 1
            reduce_mod_char
            decide

theorem prime_191102981 : Nat.Prime 191102981 := by
  apply lucas_primality 191102981 (2 : ZMod 191102981)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 191102981 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((269 : ℕ)^1 * ((35521 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 191102981)^95551490 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 191102981)^38220596 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
          subst q
          change (2 : ZMod 191102981)^710420 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 35521 := Nat.prime_eq_prime_of_dvd_pow hq prime_35521 hd
          subst q
          change (2 : ZMod 191102981)^5380 ≠ 1
          reduce_mod_char
          decide

theorem prime_197981363 : Nat.Prime 197981363 := by
  apply lucas_primality 197981363 (2 : ZMod 197981363)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 197981363 - 1 = (2 : ℕ)^1 * ((98990681 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 197981363)^98990681 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 98990681 := Nat.prime_eq_prime_of_dvd_pow hq prime_98990681 hd
      subst q
      change (2 : ZMod 197981363)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_198049321 : Nat.Prime 198049321 := by
  apply lucas_primality 198049321 (11 : ZMod 198049321)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 198049321 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((17 : ℕ)^1 * ((23 : ℕ)^1 * ((67 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 198049321)^99024660 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 198049321)^66016440 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 198049321)^39609864 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (11 : ZMod 198049321)^28292760 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
              subst q
              change (11 : ZMod 198049321)^11649960 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
                subst q
                change (11 : ZMod 198049321)^8610840 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
                subst q
                change (11 : ZMod 198049321)^2955960 ≠ 1
                reduce_mod_char
                decide

theorem prime_198789791 : Nat.Prime 198789791 := by
  apply lucas_primality 198789791 (7 : ZMod 198789791)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 198789791 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((47 : ℕ)^1 * ((479 : ℕ)^1 * ((883 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 198789791)^99394895 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 198789791)^39757958 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (7 : ZMod 198789791)^4229570 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 479 := Nat.prime_eq_prime_of_dvd_pow hq prime_479 hd
            subst q
            change (7 : ZMod 198789791)^415010 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 883 := Nat.prime_eq_prime_of_dvd_pow hq prime_883 hd
            subst q
            change (7 : ZMod 198789791)^225130 ≠ 1
            reduce_mod_char
            decide

theorem prime_200943731 : Nat.Prime 200943731 := by
  apply lucas_primality 200943731 (6 : ZMod 200943731)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 200943731 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((43 : ℕ)^1 * ((103 : ℕ)^1 * ((349 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 200943731)^100471865 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 200943731)^40188746 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (6 : ZMod 200943731)^15457210 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (6 : ZMod 200943731)^4673110 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
              subst q
              change (6 : ZMod 200943731)^1950910 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 349 := Nat.prime_eq_prime_of_dvd_pow hq prime_349 hd
              subst q
              change (6 : ZMod 200943731)^575770 ≠ 1
              reduce_mod_char
              decide

theorem prime_202482757 : Nat.Prime 202482757 := by
  apply lucas_primality 202482757 (5 : ZMod 202482757)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 202482757 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((29 : ℕ)^1 * ((103 : ℕ)^1 * ((269 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 202482757)^101241378 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 202482757)^67494252 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 202482757)^28926108 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (5 : ZMod 202482757)^6982164 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
              subst q
              change (5 : ZMod 202482757)^1965852 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
              subst q
              change (5 : ZMod 202482757)^752724 ≠ 1
              reduce_mod_char
              decide

theorem prime_204722437 : Nat.Prime 204722437 := by
  apply lucas_primality 204722437 (2 : ZMod 204722437)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 204722437 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((17060203 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 204722437)^102361218 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 204722437)^68240812 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 17060203 := Nat.prime_eq_prime_of_dvd_pow hq prime_17060203 hd
        subst q
        change (2 : ZMod 204722437)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_208585921 : Nat.Prime 208585921 := by
  apply lucas_primality 208585921 (26 : ZMod 208585921)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 208585921 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((12781 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (26 : ZMod 208585921)^104292960 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (26 : ZMod 208585921)^69528640 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (26 : ZMod 208585921)^41717184 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (26 : ZMod 208585921)^12269760 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 12781 := Nat.prime_eq_prime_of_dvd_pow hq prime_12781 hd
            subst q
            change (26 : ZMod 208585921)^16320 ≠ 1
            reduce_mod_char
            decide

theorem prime_208790077 : Nat.Prime 208790077 := by
  apply lucas_primality 208790077 (6 : ZMod 208790077)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 208790077 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((1581743 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 208790077)^104395038 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 208790077)^69596692 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (6 : ZMod 208790077)^18980916 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1581743 := Nat.prime_eq_prime_of_dvd_pow hq prime_1581743 hd
          subst q
          change (6 : ZMod 208790077)^132 ≠ 1
          reduce_mod_char
          decide

theorem prime_211407023 : Nat.Prime 211407023 := by
  apply lucas_primality 211407023 (5 : ZMod 211407023)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 211407023 - 1 = (2 : ℕ)^1 * ((1013 : ℕ)^1 * ((104347 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 211407023)^105703511 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1013 := Nat.prime_eq_prime_of_dvd_pow hq prime_1013 hd
        subst q
        change (5 : ZMod 211407023)^208694 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 104347 := Nat.prime_eq_prime_of_dvd_pow hq prime_104347 hd
        subst q
        change (5 : ZMod 211407023)^2026 ≠ 1
        reduce_mod_char
        decide

theorem prime_217085023 : Nat.Prime 217085023 := by
  apply lucas_primality 217085023 (3 : ZMod 217085023)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 217085023 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^5 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((5801 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 217085023)^108542511 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 217085023)^72361674 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 217085023)^31012146 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (3 : ZMod 217085023)^19735002 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 5801 := Nat.prime_eq_prime_of_dvd_pow hq prime_5801 hd
            subst q
            change (3 : ZMod 217085023)^37422 ≠ 1
            reduce_mod_char
            decide

theorem prime_217539649 : Nat.Prime 217539649 := by
  apply lucas_primality 217539649 (11 : ZMod 217539649)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 217539649 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^3 * ((31 : ℕ)^2 * ((131 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 217539649)^108769824 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 217539649)^72513216 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (11 : ZMod 217539649)^7017408 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
          subst q
          change (11 : ZMod 217539649)^1660608 ≠ 1
          reduce_mod_char
          decide

theorem prime_217966219 : Nat.Prime 217966219 := by
  apply lucas_primality 217966219 (2 : ZMod 217966219)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 217966219 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((36327703 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 217966219)^108983109 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 217966219)^72655406 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 36327703 := Nat.prime_eq_prime_of_dvd_pow hq prime_36327703 hd
        subst q
        change (2 : ZMod 217966219)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_222372383 : Nat.Prime 222372383 := by
  apply lucas_primality 222372383 (5 : ZMod 222372383)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 222372383 - 1 = (2 : ℕ)^1 * ((111186191 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 222372383)^111186191 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 111186191 := Nat.prime_eq_prime_of_dvd_pow hq prime_111186191 hd
      subst q
      change (5 : ZMod 222372383)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_222817601 : Nat.Prime 222817601 := by
  apply lucas_primality 222817601 (6 : ZMod 222817601)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 222817601 - 1 = (2 : ℕ)^6 * ((5 : ℕ)^2 * ((47 : ℕ)^1 * ((2963 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 222817601)^111408800 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 222817601)^44563520 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (6 : ZMod 222817601)^4740800 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2963 := Nat.prime_eq_prime_of_dvd_pow hq prime_2963 hd
          subst q
          change (6 : ZMod 222817601)^75200 ≠ 1
          reduce_mod_char
          decide

theorem prime_224930107 : Nat.Prime 224930107 := by
  apply lucas_primality 224930107 (2 : ZMod 224930107)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 224930107 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((12496117 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 224930107)^112465053 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 224930107)^74976702 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 12496117 := Nat.prime_eq_prime_of_dvd_pow hq prime_12496117 hd
        subst q
        change (2 : ZMod 224930107)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_225403301 : Nat.Prime 225403301 := by
  apply lucas_primality 225403301 (3 : ZMod 225403301)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 225403301 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((2254033 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 225403301)^112701650 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 225403301)^45080660 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2254033 := Nat.prime_eq_prime_of_dvd_pow hq prime_2254033 hd
        subst q
        change (3 : ZMod 225403301)^100 ≠ 1
        reduce_mod_char
        decide

theorem prime_225426767 : Nat.Prime 225426767 := by
  apply lucas_primality 225426767 (5 : ZMod 225426767)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 225426767 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((659 : ℕ)^1 * ((10061 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 225426767)^112713383 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (5 : ZMod 225426767)^13260398 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 659 := Nat.prime_eq_prime_of_dvd_pow hq prime_659 hd
          subst q
          change (5 : ZMod 225426767)^342074 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 10061 := Nat.prime_eq_prime_of_dvd_pow hq prime_10061 hd
          subst q
          change (5 : ZMod 225426767)^22406 ≠ 1
          reduce_mod_char
          decide

theorem prime_227358563 : Nat.Prime 227358563 := by
  apply lucas_primality 227358563 (2 : ZMod 227358563)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 227358563 - 1 = (2 : ℕ)^1 * ((37 : ℕ)^1 * ((3072413 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 227358563)^113679281 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (2 : ZMod 227358563)^6144826 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3072413 := Nat.prime_eq_prime_of_dvd_pow hq prime_3072413 hd
        subst q
        change (2 : ZMod 227358563)^74 ≠ 1
        reduce_mod_char
        decide

theorem prime_228003883 : Nat.Prime 228003883 := by
  apply lucas_primality 228003883 (3 : ZMod 228003883)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 228003883 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((251 : ℕ)^1 * ((151397 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 228003883)^114001941 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 228003883)^76001294 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 251 := Nat.prime_eq_prime_of_dvd_pow hq prime_251 hd
          subst q
          change (3 : ZMod 228003883)^908382 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 151397 := Nat.prime_eq_prime_of_dvd_pow hq prime_151397 hd
          subst q
          change (3 : ZMod 228003883)^1506 ≠ 1
          reduce_mod_char
          decide

theorem prime_228286951 : Nat.Prime 228286951 := by
  apply lucas_primality 228286951 (6 : ZMod 228286951)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 228286951 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((1521913 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 228286951)^114143475 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 228286951)^76095650 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 228286951)^45657390 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1521913 := Nat.prime_eq_prime_of_dvd_pow hq prime_1521913 hd
          subst q
          change (6 : ZMod 228286951)^150 ≠ 1
          reduce_mod_char
          decide

theorem prime_229029391 : Nat.Prime 229029391 := by
  apply lucas_primality 229029391 (13 : ZMod 229029391)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 229029391 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((149 : ℕ)^1 * ((5693 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 229029391)^114514695 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 229029391)^76343130 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 229029391)^45805878 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
            subst q
            change (13 : ZMod 229029391)^1537110 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 5693 := Nat.prime_eq_prime_of_dvd_pow hq prime_5693 hd
            subst q
            change (13 : ZMod 229029391)^40230 ≠ 1
            reduce_mod_char
            decide

theorem prime_230309929 : Nat.Prime 230309929 := by
  apply lucas_primality 230309929 (14 : ZMod 230309929)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 230309929 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((89 : ℕ)^1 * ((127 : ℕ)^1 * ((283 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 230309929)^115154964 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 230309929)^76769976 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (14 : ZMod 230309929)^2587752 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
            subst q
            change (14 : ZMod 230309929)^1813464 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 283 := Nat.prime_eq_prime_of_dvd_pow hq prime_283 hd
            subst q
            change (14 : ZMod 230309929)^813816 ≠ 1
            reduce_mod_char
            decide

theorem prime_234500951 : Nat.Prime 234500951 := by
  apply lucas_primality 234500951 (17 : ZMod 234500951)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 234500951 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((1031 : ℕ)^1 * ((4549 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 234500951)^117250475 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (17 : ZMod 234500951)^46900190 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1031 := Nat.prime_eq_prime_of_dvd_pow hq prime_1031 hd
          subst q
          change (17 : ZMod 234500951)^227450 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4549 := Nat.prime_eq_prime_of_dvd_pow hq prime_4549 hd
          subst q
          change (17 : ZMod 234500951)^51550 ≠ 1
          reduce_mod_char
          decide

theorem prime_237891361 : Nat.Prime 237891361 := by
  apply lucas_primality 237891361 (19 : ZMod 237891361)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 237891361 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((101 : ℕ)^1 * ((701 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 237891361)^118945680 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 237891361)^79297120 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (19 : ZMod 237891361)^47578272 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (19 : ZMod 237891361)^33984480 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
              subst q
              change (19 : ZMod 237891361)^2355360 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 701 := Nat.prime_eq_prime_of_dvd_pow hq prime_701 hd
              subst q
              change (19 : ZMod 237891361)^339360 ≠ 1
              reduce_mod_char
              decide

theorem prime_239233777 : Nat.Prime 239233777 := by
  apply lucas_primality 239233777 (5 : ZMod 239233777)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 239233777 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((4984037 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 239233777)^119616888 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 239233777)^79744592 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4984037 := Nat.prime_eq_prime_of_dvd_pow hq prime_4984037 hd
        subst q
        change (5 : ZMod 239233777)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_240247727 : Nat.Prime 240247727 := by
  apply lucas_primality 240247727 (5 : ZMod 240247727)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 240247727 - 1 = (2 : ℕ)^1 * ((397 : ℕ)^1 * ((302579 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 240247727)^120123863 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 397 := Nat.prime_eq_prime_of_dvd_pow hq prime_397 hd
        subst q
        change (5 : ZMod 240247727)^605158 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 302579 := Nat.prime_eq_prime_of_dvd_pow hq prime_302579 hd
        subst q
        change (5 : ZMod 240247727)^794 ≠ 1
        reduce_mod_char
        decide

theorem prime_243375481 : Nat.Prime 243375481 := by
  apply lucas_primality 243375481 (11 : ZMod 243375481)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 243375481 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((676043 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 243375481)^121687740 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 243375481)^81125160 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 243375481)^48675096 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 676043 := Nat.prime_eq_prime_of_dvd_pow hq prime_676043 hd
          subst q
          change (11 : ZMod 243375481)^360 ≠ 1
          reduce_mod_char
          decide

theorem prime_244140683 : Nat.Prime 244140683 := by
  apply lucas_primality 244140683 (2 : ZMod 244140683)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 244140683 - 1 = (2 : ℕ)^1 * ((83 : ℕ)^1 * ((1470727 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 244140683)^122070341 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
        subst q
        change (2 : ZMod 244140683)^2941454 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1470727 := Nat.prime_eq_prime_of_dvd_pow hq prime_1470727 hd
        subst q
        change (2 : ZMod 244140683)^166 ≠ 1
        reduce_mod_char
        decide

theorem prime_247139647 : Nat.Prime 247139647 := by
  apply lucas_primality 247139647 (3 : ZMod 247139647)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 247139647 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((23 : ℕ)^1 * ((347 : ℕ)^1 * ((397 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 247139647)^123569823 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 247139647)^82379882 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 247139647)^19010742 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (3 : ZMod 247139647)^10745202 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 347 := Nat.prime_eq_prime_of_dvd_pow hq prime_347 hd
              subst q
              change (3 : ZMod 247139647)^712218 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 397 := Nat.prime_eq_prime_of_dvd_pow hq prime_397 hd
              subst q
              change (3 : ZMod 247139647)^622518 ≠ 1
              reduce_mod_char
              decide

theorem prime_249445111 : Nat.Prime 249445111 := by
  apply lucas_primality 249445111 (3 : ZMod 249445111)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 249445111 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((19 : ℕ)^1 * ((499 : ℕ)^1 * ((877 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 249445111)^124722555 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 249445111)^83148370 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 249445111)^49889022 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (3 : ZMod 249445111)^13128690 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 499 := Nat.prime_eq_prime_of_dvd_pow hq prime_499 hd
              subst q
              change (3 : ZMod 249445111)^499890 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 877 := Nat.prime_eq_prime_of_dvd_pow hq prime_877 hd
              subst q
              change (3 : ZMod 249445111)^284430 ≠ 1
              reduce_mod_char
              decide

theorem prime_249770263 : Nat.Prime 249770263 := by
  apply lucas_primality 249770263 (3 : ZMod 249770263)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 249770263 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((103 : ℕ)^1 * ((57737 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 249770263)^124885131 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 249770263)^83256754 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 249770263)^35681466 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
            subst q
            change (3 : ZMod 249770263)^2424954 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 57737 := Nat.prime_eq_prime_of_dvd_pow hq prime_57737 hd
            subst q
            change (3 : ZMod 249770263)^4326 ≠ 1
            reduce_mod_char
            decide

theorem prime_252647917 : Nat.Prime 252647917 := by
  apply lucas_primality 252647917 (2 : ZMod 252647917)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 252647917 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((915391 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 252647917)^126323958 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 252647917)^84215972 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 252647917)^10984692 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 915391 := Nat.prime_eq_prime_of_dvd_pow hq prime_915391 hd
          subst q
          change (2 : ZMod 252647917)^276 ≠ 1
          reduce_mod_char
          decide

theorem prime_256431841 : Nat.Prime 256431841 := by
  apply lucas_primality 256431841 (22 : ZMod 256431841)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 256431841 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((167 : ℕ)^1 * ((457 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (22 : ZMod 256431841)^128215920 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (22 : ZMod 256431841)^85477280 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (22 : ZMod 256431841)^51286368 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (22 : ZMod 256431841)^36633120 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
              subst q
              change (22 : ZMod 256431841)^1535520 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 457 := Nat.prime_eq_prime_of_dvd_pow hq prime_457 hd
              subst q
              change (22 : ZMod 256431841)^561120 ≠ 1
              reduce_mod_char
              decide

theorem prime_259637017 : Nat.Prime 259637017 := by
  apply lucas_primality 259637017 (10 : ZMod 259637017)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 259637017 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((173 : ℕ)^1 * ((62533 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 259637017)^129818508 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 259637017)^86545672 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
          subst q
          change (10 : ZMod 259637017)^1500792 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 62533 := Nat.prime_eq_prime_of_dvd_pow hq prime_62533 hd
          subst q
          change (10 : ZMod 259637017)^4152 ≠ 1
          reduce_mod_char
          decide

theorem prime_261170057 : Nat.Prime 261170057 := by
  apply lucas_primality 261170057 (3 : ZMod 261170057)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 261170057 - 1 = (2 : ℕ)^3 * ((7 : ℕ)^1 * ((29 : ℕ)^1 * ((73 : ℕ)^1 * ((2203 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 261170057)^130585028 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 261170057)^37310008 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (3 : ZMod 261170057)^9005864 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
            subst q
            change (3 : ZMod 261170057)^3577672 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2203 := Nat.prime_eq_prime_of_dvd_pow hq prime_2203 hd
            subst q
            change (3 : ZMod 261170057)^118552 ≠ 1
            reduce_mod_char
            decide

theorem prime_261808949 : Nat.Prime 261808949 := by
  apply lucas_primality 261808949 (2 : ZMod 261808949)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 261808949 - 1 = (2 : ℕ)^2 * ((2339 : ℕ)^1 * ((27983 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 261808949)^130904474 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 2339 := Nat.prime_eq_prime_of_dvd_pow hq prime_2339 hd
        subst q
        change (2 : ZMod 261808949)^111932 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 27983 := Nat.prime_eq_prime_of_dvd_pow hq prime_27983 hd
        subst q
        change (2 : ZMod 261808949)^9356 ≠ 1
        reduce_mod_char
        decide

theorem prime_262105673 : Nat.Prime 262105673 := by
  apply lucas_primality 262105673 (3 : ZMod 262105673)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 262105673 - 1 = (2 : ℕ)^3 * ((32763209 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 262105673)^131052836 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 32763209 := Nat.prime_eq_prime_of_dvd_pow hq prime_32763209 hd
      subst q
      change (3 : ZMod 262105673)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_263251757 : Nat.Prime 263251757 := by
  apply lucas_primality 263251757 (2 : ZMod 263251757)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 263251757 - 1 = (2 : ℕ)^2 * ((1913 : ℕ)^1 * ((34403 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 263251757)^131625878 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1913 := Nat.prime_eq_prime_of_dvd_pow hq prime_1913 hd
        subst q
        change (2 : ZMod 263251757)^137612 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 34403 := Nat.prime_eq_prime_of_dvd_pow hq prime_34403 hd
        subst q
        change (2 : ZMod 263251757)^7652 ≠ 1
        reduce_mod_char
        decide

theorem prime_265066301 : Nat.Prime 265066301 := by
  apply lucas_primality 265066301 (2 : ZMod 265066301)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 265066301 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((2650663 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 265066301)^132533150 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 265066301)^53013260 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2650663 := Nat.prime_eq_prime_of_dvd_pow hq prime_2650663 hd
        subst q
        change (2 : ZMod 265066301)^100 ≠ 1
        reduce_mod_char
        decide

theorem prime_266873653 : Nat.Prime 266873653 := by
  apply lucas_primality 266873653 (2 : ZMod 266873653)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 266873653 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((43 : ℕ)^1 * ((172399 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 266873653)^133436826 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 266873653)^88957884 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (2 : ZMod 266873653)^6206364 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 172399 := Nat.prime_eq_prime_of_dvd_pow hq prime_172399 hd
          subst q
          change (2 : ZMod 266873653)^1548 ≠ 1
          reduce_mod_char
          decide

theorem prime_273084961 : Nat.Prime 273084961 := by
  apply lucas_primality 273084961 (11 : ZMod 273084961)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 273084961 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((139 : ℕ)^1 * ((4093 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 273084961)^136542480 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 273084961)^91028320 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 273084961)^54616992 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
            subst q
            change (11 : ZMod 273084961)^1964640 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 4093 := Nat.prime_eq_prime_of_dvd_pow hq prime_4093 hd
            subst q
            change (11 : ZMod 273084961)^66720 ≠ 1
            reduce_mod_char
            decide

theorem prime_273291947 : Nat.Prime 273291947 := by
  apply lucas_primality 273291947 (2 : ZMod 273291947)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 273291947 - 1 = (2 : ℕ)^1 * ((136645973 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 273291947)^136645973 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 136645973 := Nat.prime_eq_prime_of_dvd_pow hq prime_136645973 hd
      subst q
      change (2 : ZMod 273291947)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_282844349 : Nat.Prime 282844349 := by
  apply lucas_primality 282844349 (2 : ZMod 282844349)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 282844349 - 1 = (2 : ℕ)^2 * ((59 : ℕ)^1 * ((241 : ℕ)^1 * ((4973 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 282844349)^141422174 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
        subst q
        change (2 : ZMod 282844349)^4793972 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 241 := Nat.prime_eq_prime_of_dvd_pow hq prime_241 hd
          subst q
          change (2 : ZMod 282844349)^1173628 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4973 := Nat.prime_eq_prime_of_dvd_pow hq prime_4973 hd
          subst q
          change (2 : ZMod 282844349)^56876 ≠ 1
          reduce_mod_char
          decide

theorem prime_288395641 : Nat.Prime 288395641 := by
  apply lucas_primality 288395641 (23 : ZMod 288395641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 288395641 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^4 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((41 : ℕ)^1 * ((167 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (23 : ZMod 288395641)^144197820 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (23 : ZMod 288395641)^96131880 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (23 : ZMod 288395641)^57679128 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (23 : ZMod 288395641)^22184280 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
              subst q
              change (23 : ZMod 288395641)^7034040 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
              subst q
              change (23 : ZMod 288395641)^1726920 ≠ 1
              reduce_mod_char
              decide

theorem prime_288588173 : Nat.Prime 288588173 := by
  apply lucas_primality 288588173 (2 : ZMod 288588173)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 288588173 - 1 = (2 : ℕ)^2 * ((72147043 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 288588173)^144294086 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 72147043 := Nat.prime_eq_prime_of_dvd_pow hq prime_72147043 hd
      subst q
      change (2 : ZMod 288588173)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_290786467 : Nat.Prime 290786467 := by
  apply lucas_primality 290786467 (14 : ZMod 290786467)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 290786467 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((48464411 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 290786467)^145393233 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 290786467)^96928822 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 48464411 := Nat.prime_eq_prime_of_dvd_pow hq prime_48464411 hd
        subst q
        change (14 : ZMod 290786467)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_291179243 : Nat.Prime 291179243 := by
  apply lucas_primality 291179243 (2 : ZMod 291179243)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 291179243 - 1 = (2 : ℕ)^1 * ((4507 : ℕ)^1 * ((32303 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 291179243)^145589621 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 4507 := Nat.prime_eq_prime_of_dvd_pow hq prime_4507 hd
        subst q
        change (2 : ZMod 291179243)^64606 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 32303 := Nat.prime_eq_prime_of_dvd_pow hq prime_32303 hd
        subst q
        change (2 : ZMod 291179243)^9014 ≠ 1
        reduce_mod_char
        decide

theorem prime_292940509 : Nat.Prime 292940509 := by
  apply lucas_primality 292940509 (2 : ZMod 292940509)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 292940509 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((3487387 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 292940509)^146470254 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 292940509)^97646836 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 292940509)^41848644 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3487387 := Nat.prime_eq_prime_of_dvd_pow hq prime_3487387 hd
          subst q
          change (2 : ZMod 292940509)^84 ≠ 1
          reduce_mod_char
          decide

theorem prime_296224333 : Nat.Prime 296224333 := by
  apply lucas_primality 296224333 (2 : ZMod 296224333)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 296224333 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((24685361 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 296224333)^148112166 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 296224333)^98741444 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 24685361 := Nat.prime_eq_prime_of_dvd_pow hq prime_24685361 hd
        subst q
        change (2 : ZMod 296224333)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_299554693 : Nat.Prime 299554693 := by
  apply lucas_primality 299554693 (2 : ZMod 299554693)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 299554693 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((41 : ℕ)^1 * ((608851 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 299554693)^149777346 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 299554693)^99851564 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (2 : ZMod 299554693)^7306212 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 608851 := Nat.prime_eq_prime_of_dvd_pow hq prime_608851 hd
          subst q
          change (2 : ZMod 299554693)^492 ≠ 1
          reduce_mod_char
          decide

theorem prime_302614969 : Nat.Prime 302614969 := by
  apply lucas_primality 302614969 (11 : ZMod 302614969)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 302614969 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((12608957 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 302614969)^151307484 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 302614969)^100871656 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 12608957 := Nat.prime_eq_prime_of_dvd_pow hq prime_12608957 hd
        subst q
        change (11 : ZMod 302614969)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_305935789 : Nat.Prime 305935789 := by
  apply lucas_primality 305935789 (2 : ZMod 305935789)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 305935789 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((1108463 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 305935789)^152967894 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 305935789)^101978596 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 305935789)^13301556 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1108463 := Nat.prime_eq_prime_of_dvd_pow hq prime_1108463 hd
          subst q
          change (2 : ZMod 305935789)^276 ≠ 1
          reduce_mod_char
          decide

theorem prime_308634059 : Nat.Prime 308634059 := by
  apply lucas_primality 308634059 (2 : ZMod 308634059)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 308634059 - 1 = (2 : ℕ)^1 * ((154317029 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 308634059)^154317029 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 154317029 := Nat.prime_eq_prime_of_dvd_pow hq prime_154317029 hd
      subst q
      change (2 : ZMod 308634059)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_308915797 : Nat.Prime 308915797 := by
  apply lucas_primality 308915797 (2 : ZMod 308915797)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 308915797 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((89 : ℕ)^1 * ((5903 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 308915797)^154457898 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 308915797)^102971932 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 308915797)^44130828 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
            subst q
            change (2 : ZMod 308915797)^3470964 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 5903 := Nat.prime_eq_prime_of_dvd_pow hq prime_5903 hd
            subst q
            change (2 : ZMod 308915797)^52332 ≠ 1
            reduce_mod_char
            decide

theorem prime_315385601 : Nat.Prime 315385601 := by
  apply lucas_primality 315385601 (3 : ZMod 315385601)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 315385601 - 1 = (2 : ℕ)^8 * ((5 : ℕ)^2 * ((49279 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 315385601)^157692800 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 315385601)^63077120 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 49279 := Nat.prime_eq_prime_of_dvd_pow hq prime_49279 hd
        subst q
        change (3 : ZMod 315385601)^6400 ≠ 1
        reduce_mod_char
        decide

theorem prime_318128297 : Nat.Prime 318128297 := by
  apply lucas_primality 318128297 (5 : ZMod 318128297)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 318128297 - 1 = (2 : ℕ)^3 * ((659 : ℕ)^1 * ((60343 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 318128297)^159064148 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 659 := Nat.prime_eq_prime_of_dvd_pow hq prime_659 hd
        subst q
        change (5 : ZMod 318128297)^482744 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 60343 := Nat.prime_eq_prime_of_dvd_pow hq prime_60343 hd
        subst q
        change (5 : ZMod 318128297)^5272 ≠ 1
        reduce_mod_char
        decide

theorem prime_325773109 : Nat.Prime 325773109 := by
  apply lucas_primality 325773109 (2 : ZMod 325773109)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 325773109 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((17 : ℕ)^1 * ((89 : ℕ)^1 * ((5981 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 325773109)^162886554 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 325773109)^108591036 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 325773109)^19163124 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
            subst q
            change (2 : ZMod 325773109)^3660372 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 5981 := Nat.prime_eq_prime_of_dvd_pow hq prime_5981 hd
            subst q
            change (2 : ZMod 325773109)^54468 ≠ 1
            reduce_mod_char
            decide

theorem prime_333353107 : Nat.Prime 333353107 := by
  apply lucas_primality 333353107 (5 : ZMod 333353107)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 333353107 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((31 : ℕ)^1 * ((597407 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 333353107)^166676553 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 333353107)^111117702 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (5 : ZMod 333353107)^10753326 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 597407 := Nat.prime_eq_prime_of_dvd_pow hq prime_597407 hd
          subst q
          change (5 : ZMod 333353107)^558 ≠ 1
          reduce_mod_char
          decide

theorem prime_333365363 : Nat.Prime 333365363 := by
  apply lucas_primality 333365363 (2 : ZMod 333365363)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 333365363 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((15152971 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 333365363)^166682681 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 333365363)^30305942 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 15152971 := Nat.prime_eq_prime_of_dvd_pow hq prime_15152971 hd
        subst q
        change (2 : ZMod 333365363)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_334147501 : Nat.Prime 334147501 := by
  apply lucas_primality 334147501 (10 : ZMod 334147501)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 334147501 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^4 * ((14851 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 334147501)^167073750 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 334147501)^111382500 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 334147501)^66829500 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 14851 := Nat.prime_eq_prime_of_dvd_pow hq prime_14851 hd
          subst q
          change (10 : ZMod 334147501)^22500 ≠ 1
          reduce_mod_char
          decide

theorem prime_336942259 : Nat.Prime 336942259 := by
  apply lucas_primality 336942259 (11 : ZMod 336942259)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 336942259 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1091 : ℕ)^1 * ((51473 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 336942259)^168471129 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 336942259)^112314086 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1091 := Nat.prime_eq_prime_of_dvd_pow hq prime_1091 hd
          subst q
          change (11 : ZMod 336942259)^308838 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 51473 := Nat.prime_eq_prime_of_dvd_pow hq prime_51473 hd
          subst q
          change (11 : ZMod 336942259)^6546 ≠ 1
          reduce_mod_char
          decide

theorem prime_346348369 : Nat.Prime 346348369 := by
  apply lucas_primality 346348369 (7 : ZMod 346348369)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 346348369 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((31 : ℕ)^1 * ((77587 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 346348369)^173174184 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 346348369)^115449456 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (7 : ZMod 346348369)^11172528 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 77587 := Nat.prime_eq_prime_of_dvd_pow hq prime_77587 hd
          subst q
          change (7 : ZMod 346348369)^4464 ≠ 1
          reduce_mod_char
          decide

theorem prime_360519931 : Nat.Prime 360519931 := by
  apply lucas_primality 360519931 (7 : ZMod 360519931)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 360519931 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((1335259 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 360519931)^180259965 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 360519931)^120173310 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 360519931)^72103986 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1335259 := Nat.prime_eq_prime_of_dvd_pow hq prime_1335259 hd
          subst q
          change (7 : ZMod 360519931)^270 ≠ 1
          reduce_mod_char
          decide

theorem prime_360756593 : Nat.Prime 360756593 := by
  apply lucas_primality 360756593 (3 : ZMod 360756593)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 360756593 - 1 = (2 : ℕ)^4 * ((7 : ℕ)^1 * ((17 : ℕ)^1 * ((189473 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 360756593)^180378296 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 360756593)^51536656 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (3 : ZMod 360756593)^21220976 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 189473 := Nat.prime_eq_prime_of_dvd_pow hq prime_189473 hd
          subst q
          change (3 : ZMod 360756593)^1904 ≠ 1
          reduce_mod_char
          decide

theorem prime_363959641 : Nat.Prime 363959641 := by
  apply lucas_primality 363959641 (14 : ZMod 363959641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 363959641 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((91909 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 363959641)^181979820 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 363959641)^121319880 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (14 : ZMod 363959641)^72791928 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (14 : ZMod 363959641)^33087240 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 91909 := Nat.prime_eq_prime_of_dvd_pow hq prime_91909 hd
            subst q
            change (14 : ZMod 363959641)^3960 ≠ 1
            reduce_mod_char
            decide

theorem prime_368058469 : Nat.Prime 368058469 := by
  apply lucas_primality 368058469 (6 : ZMod 368058469)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 368058469 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((30671539 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 368058469)^184029234 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 368058469)^122686156 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 30671539 := Nat.prime_eq_prime_of_dvd_pow hq prime_30671539 hd
        subst q
        change (6 : ZMod 368058469)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_376785499 : Nat.Prime 376785499 := by
  apply lucas_primality 376785499 (3 : ZMod 376785499)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 376785499 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((71 : ℕ)^1 * ((563 : ℕ)^1 * ((1571 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 376785499)^188392749 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 376785499)^125595166 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
          subst q
          change (3 : ZMod 376785499)^5306838 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 563 := Nat.prime_eq_prime_of_dvd_pow hq prime_563 hd
            subst q
            change (3 : ZMod 376785499)^669246 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1571 := Nat.prime_eq_prime_of_dvd_pow hq prime_1571 hd
            subst q
            change (3 : ZMod 376785499)^239838 ≠ 1
            reduce_mod_char
            decide

theorem prime_377745947 : Nat.Prime 377745947 := by
  apply lucas_primality 377745947 (2 : ZMod 377745947)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 377745947 - 1 = (2 : ℕ)^1 * ((53 : ℕ)^1 * ((73 : ℕ)^1 * ((48817 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 377745947)^188872973 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
        subst q
        change (2 : ZMod 377745947)^7127282 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
          subst q
          change (2 : ZMod 377745947)^5174602 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 48817 := Nat.prime_eq_prime_of_dvd_pow hq prime_48817 hd
          subst q
          change (2 : ZMod 377745947)^7738 ≠ 1
          reduce_mod_char
          decide

theorem prime_383706383 : Nat.Prime 383706383 := by
  apply lucas_primality 383706383 (5 : ZMod 383706383)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 383706383 - 1 = (2 : ℕ)^1 * ((59 : ℕ)^1 * ((3251749 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 383706383)^191853191 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
        subst q
        change (5 : ZMod 383706383)^6503498 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3251749 := Nat.prime_eq_prime_of_dvd_pow hq prime_3251749 hd
        subst q
        change (5 : ZMod 383706383)^118 ≠ 1
        reduce_mod_char
        decide

theorem prime_387420499 : Nat.Prime 387420499 := by
  apply lucas_primality 387420499 (11 : ZMod 387420499)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 387420499 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((21523361 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 387420499)^193710249 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 387420499)^129140166 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 21523361 := Nat.prime_eq_prime_of_dvd_pow hq prime_21523361 hd
        subst q
        change (11 : ZMod 387420499)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_388666753 : Nat.Prime 388666753 := by
  apply lucas_primality 388666753 (7 : ZMod 388666753)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 388666753 - 1 = (2 : ℕ)^7 * ((3 : ℕ)^1 * ((151 : ℕ)^1 * ((6703 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 388666753)^194333376 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 388666753)^129555584 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
          subst q
          change (7 : ZMod 388666753)^2573952 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 6703 := Nat.prime_eq_prime_of_dvd_pow hq prime_6703 hd
          subst q
          change (7 : ZMod 388666753)^57984 ≠ 1
          reduce_mod_char
          decide

theorem prime_388968089 : Nat.Prime 388968089 := by
  apply lucas_primality 388968089 (3 : ZMod 388968089)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 388968089 - 1 = (2 : ℕ)^3 * ((23 : ℕ)^1 * ((2113957 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 388968089)^194484044 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (3 : ZMod 388968089)^16911656 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2113957 := Nat.prime_eq_prime_of_dvd_pow hq prime_2113957 hd
        subst q
        change (3 : ZMod 388968089)^184 ≠ 1
        reduce_mod_char
        decide

theorem prime_391223099 : Nat.Prime 391223099 := by
  apply lucas_primality 391223099 (2 : ZMod 391223099)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 391223099 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((4549 : ℕ)^1 * ((6143 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 391223099)^195611549 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 391223099)^55889014 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 4549 := Nat.prime_eq_prime_of_dvd_pow hq prime_4549 hd
          subst q
          change (2 : ZMod 391223099)^86002 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 6143 := Nat.prime_eq_prime_of_dvd_pow hq prime_6143 hd
          subst q
          change (2 : ZMod 391223099)^63686 ≠ 1
          reduce_mod_char
          decide

theorem prime_393935489 : Nat.Prime 393935489 := by
  apply lucas_primality 393935489 (3 : ZMod 393935489)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 393935489 - 1 = (2 : ℕ)^7 * ((3077621 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 393935489)^196967744 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3077621 := Nat.prime_eq_prime_of_dvd_pow hq prime_3077621 hd
      subst q
      change (3 : ZMod 393935489)^128 ≠ 1
      reduce_mod_char
      decide

theorem prime_402341081 : Nat.Prime 402341081 := by
  apply lucas_primality 402341081 (3 : ZMod 402341081)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 402341081 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((127 : ℕ)^1 * ((79201 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 402341081)^201170540 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 402341081)^80468216 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
          subst q
          change (3 : ZMod 402341081)^3168040 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 79201 := Nat.prime_eq_prime_of_dvd_pow hq prime_79201 hd
          subst q
          change (3 : ZMod 402341081)^5080 ≠ 1
          reduce_mod_char
          decide

theorem prime_418722769 : Nat.Prime 418722769 := by
  apply lucas_primality 418722769 (7 : ZMod 418722769)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 418722769 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((157 : ℕ)^1 * ((18521 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 418722769)^209361384 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 418722769)^139574256 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
          subst q
          change (7 : ZMod 418722769)^2667024 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 18521 := Nat.prime_eq_prime_of_dvd_pow hq prime_18521 hd
          subst q
          change (7 : ZMod 418722769)^22608 ≠ 1
          reduce_mod_char
          decide

theorem prime_419780479 : Nat.Prime 419780479 := by
  apply lucas_primality 419780479 (3 : ZMod 419780479)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 419780479 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((947 : ℕ)^1 * ((5683 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 419780479)^209890239 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 419780479)^139926826 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 419780479)^32290806 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 947 := Nat.prime_eq_prime_of_dvd_pow hq prime_947 hd
            subst q
            change (3 : ZMod 419780479)^443274 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 5683 := Nat.prime_eq_prime_of_dvd_pow hq prime_5683 hd
            subst q
            change (3 : ZMod 419780479)^73866 ≠ 1
            reduce_mod_char
            decide

theorem prime_420823649 : Nat.Prime 420823649 := by
  apply lucas_primality 420823649 (6 : ZMod 420823649)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 420823649 - 1 = (2 : ℕ)^5 * ((7 : ℕ)^1 * ((1878677 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 420823649)^210411824 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (6 : ZMod 420823649)^60117664 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1878677 := Nat.prime_eq_prime_of_dvd_pow hq prime_1878677 hd
        subst q
        change (6 : ZMod 420823649)^224 ≠ 1
        reduce_mod_char
        decide

theorem prime_421758541 : Nat.Prime 421758541 := by
  apply lucas_primality 421758541 (6 : ZMod 421758541)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 421758541 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((89 : ℕ)^1 * ((3761 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 421758541)^210879270 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 421758541)^140586180 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 421758541)^84351708 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (6 : ZMod 421758541)^60251220 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
              subst q
              change (6 : ZMod 421758541)^4738860 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 3761 := Nat.prime_eq_prime_of_dvd_pow hq prime_3761 hd
              subst q
              change (6 : ZMod 421758541)^112140 ≠ 1
              reduce_mod_char
              decide

theorem prime_423026843 : Nat.Prime 423026843 := by
  apply lucas_primality 423026843 (2 : ZMod 423026843)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 423026843 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((30216203 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 423026843)^211513421 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 423026843)^60432406 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 30216203 := Nat.prime_eq_prime_of_dvd_pow hq prime_30216203 hd
        subst q
        change (2 : ZMod 423026843)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_425310761 : Nat.Prime 425310761 := by
  apply lucas_primality 425310761 (3 : ZMod 425310761)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 425310761 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((17 : ℕ)^1 * ((199 : ℕ)^1 * ((449 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 425310761)^212655380 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 425310761)^85062152 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 425310761)^60758680 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (3 : ZMod 425310761)^25018280 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 199 := Nat.prime_eq_prime_of_dvd_pow hq prime_199 hd
              subst q
              change (3 : ZMod 425310761)^2137240 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 449 := Nat.prime_eq_prime_of_dvd_pow hq prime_449 hd
              subst q
              change (3 : ZMod 425310761)^947240 ≠ 1
              reduce_mod_char
              decide

theorem prime_432232253 : Nat.Prime 432232253 := by
  apply lucas_primality 432232253 (2 : ZMod 432232253)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 432232253 - 1 = (2 : ℕ)^2 * ((108058063 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 432232253)^216116126 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 108058063 := Nat.prime_eq_prime_of_dvd_pow hq prime_108058063 hd
      subst q
      change (2 : ZMod 432232253)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_438522941 : Nat.Prime 438522941 := by
  apply lucas_primality 438522941 (2 : ZMod 438522941)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 438522941 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((1193 : ℕ)^1 * ((18379 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 438522941)^219261470 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 438522941)^87704588 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1193 := Nat.prime_eq_prime_of_dvd_pow hq prime_1193 hd
          subst q
          change (2 : ZMod 438522941)^367580 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 18379 := Nat.prime_eq_prime_of_dvd_pow hq prime_18379 hd
          subst q
          change (2 : ZMod 438522941)^23860 ≠ 1
          reduce_mod_char
          decide

theorem prime_440750759 : Nat.Prime 440750759 := by
  apply lucas_primality 440750759 (7 : ZMod 440750759)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 440750759 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((29 : ℕ)^1 * ((557 : ℕ)^1 * ((1949 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 440750759)^220375379 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 440750759)^62964394 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (7 : ZMod 440750759)^15198302 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 557 := Nat.prime_eq_prime_of_dvd_pow hq prime_557 hd
            subst q
            change (7 : ZMod 440750759)^791294 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1949 := Nat.prime_eq_prime_of_dvd_pow hq prime_1949 hd
            subst q
            change (7 : ZMod 440750759)^226142 ≠ 1
            reduce_mod_char
            decide

theorem prime_451996009 : Nat.Prime 451996009 := by
  apply lucas_primality 451996009 (14 : ZMod 451996009)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 451996009 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((101 : ℕ)^1 * ((263 : ℕ)^1 * ((709 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 451996009)^225998004 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 451996009)^150665336 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
          subst q
          change (14 : ZMod 451996009)^4475208 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 263 := Nat.prime_eq_prime_of_dvd_pow hq prime_263 hd
            subst q
            change (14 : ZMod 451996009)^1718616 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 709 := Nat.prime_eq_prime_of_dvd_pow hq prime_709 hd
            subst q
            change (14 : ZMod 451996009)^637512 ≠ 1
            reduce_mod_char
            decide

theorem prime_455016127 : Nat.Prime 455016127 := by
  apply lucas_primality 455016127 (3 : ZMod 455016127)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 455016127 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((83 : ℕ)^1 * ((913687 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 455016127)^227508063 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 455016127)^151672042 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
          subst q
          change (3 : ZMod 455016127)^5482122 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 913687 := Nat.prime_eq_prime_of_dvd_pow hq prime_913687 hd
          subst q
          change (3 : ZMod 455016127)^498 ≠ 1
          reduce_mod_char
          decide

theorem prime_455016943 : Nat.Prime 455016943 := by
  apply lucas_primality 455016943 (6 : ZMod 455016943)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 455016943 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((25278719 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 455016943)^227508471 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 455016943)^151672314 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 25278719 := Nat.prime_eq_prime_of_dvd_pow hq prime_25278719 hd
        subst q
        change (6 : ZMod 455016943)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_460789741 : Nat.Prime 460789741 := by
  apply lucas_primality 460789741 (6 : ZMod 460789741)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 460789741 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((167 : ℕ)^1 * ((15329 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 460789741)^230394870 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 460789741)^153596580 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 460789741)^92157948 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
            subst q
            change (6 : ZMod 460789741)^2759220 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 15329 := Nat.prime_eq_prime_of_dvd_pow hq prime_15329 hd
            subst q
            change (6 : ZMod 460789741)^30060 ≠ 1
            reduce_mod_char
            decide

theorem prime_468545747 : Nat.Prime 468545747 := by
  apply lucas_primality 468545747 (2 : ZMod 468545747)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 468545747 - 1 = (2 : ℕ)^1 * ((179 : ℕ)^1 * ((223 : ℕ)^1 * ((5869 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 468545747)^234272873 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 179 := Nat.prime_eq_prime_of_dvd_pow hq prime_179 hd
        subst q
        change (2 : ZMod 468545747)^2617574 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 223 := Nat.prime_eq_prime_of_dvd_pow hq prime_223 hd
          subst q
          change (2 : ZMod 468545747)^2101102 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 5869 := Nat.prime_eq_prime_of_dvd_pow hq prime_5869 hd
          subst q
          change (2 : ZMod 468545747)^79834 ≠ 1
          reduce_mod_char
          decide

theorem prime_468925481 : Nat.Prime 468925481 := by
  apply lucas_primality 468925481 (3 : ZMod 468925481)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 468925481 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((11723137 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 468925481)^234462740 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 468925481)^93785096 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 11723137 := Nat.prime_eq_prime_of_dvd_pow hq prime_11723137 hd
        subst q
        change (3 : ZMod 468925481)^40 ≠ 1
        reduce_mod_char
        decide

theorem prime_478637591 : Nat.Prime 478637591 := by
  apply lucas_primality 478637591 (11 : ZMod 478637591)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 478637591 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((23 : ℕ)^1 * ((2081033 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 478637591)^239318795 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 478637591)^95727518 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (11 : ZMod 478637591)^20810330 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2081033 := Nat.prime_eq_prime_of_dvd_pow hq prime_2081033 hd
          subst q
          change (11 : ZMod 478637591)^230 ≠ 1
          reduce_mod_char
          decide

theorem prime_481890307 : Nat.Prime 481890307 := by
  apply lucas_primality 481890307 (2 : ZMod 481890307)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 481890307 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((80315051 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 481890307)^240945153 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 481890307)^160630102 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 80315051 := Nat.prime_eq_prime_of_dvd_pow hq prime_80315051 hd
        subst q
        change (2 : ZMod 481890307)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_486160009 : Nat.Prime 486160009 := by
  apply lucas_primality 486160009 (14 : ZMod 486160009)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 486160009 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((89 : ℕ)^1 * ((227603 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 486160009)^243080004 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 486160009)^162053336 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (14 : ZMod 486160009)^5462472 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 227603 := Nat.prime_eq_prime_of_dvd_pow hq prime_227603 hd
          subst q
          change (14 : ZMod 486160009)^2136 ≠ 1
          reduce_mod_char
          decide

theorem prime_494102381 : Nat.Prime 494102381 := by
  apply lucas_primality 494102381 (2 : ZMod 494102381)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 494102381 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((24705119 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 494102381)^247051190 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 494102381)^98820476 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 24705119 := Nat.prime_eq_prime_of_dvd_pow hq prime_24705119 hd
        subst q
        change (2 : ZMod 494102381)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_495506653 : Nat.Prime 495506653 := by
  apply lucas_primality 495506653 (2 : ZMod 495506653)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 495506653 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((97 : ℕ)^1 * ((149 : ℕ)^1 * ((2857 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 495506653)^247753326 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 495506653)^165168884 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
          subst q
          change (2 : ZMod 495506653)^5108316 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
            subst q
            change (2 : ZMod 495506653)^3325548 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2857 := Nat.prime_eq_prime_of_dvd_pow hq prime_2857 hd
            subst q
            change (2 : ZMod 495506653)^173436 ≠ 1
            reduce_mod_char
            decide

theorem prime_497779939 : Nat.Prime 497779939 := by
  apply lucas_primality 497779939 (2 : ZMod 497779939)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 497779939 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((23 : ℕ)^1 * ((457 : ℕ)^1 * ((877 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 497779939)^248889969 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 497779939)^165926646 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 497779939)^21642606 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 457 := Nat.prime_eq_prime_of_dvd_pow hq prime_457 hd
            subst q
            change (2 : ZMod 497779939)^1089234 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 877 := Nat.prime_eq_prime_of_dvd_pow hq prime_877 hd
            subst q
            change (2 : ZMod 497779939)^567594 ≠ 1
            reduce_mod_char
            decide

theorem prime_500904661 : Nat.Prime 500904661 := by
  apply lucas_primality 500904661 (7 : ZMod 500904661)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 500904661 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((491083 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 500904661)^250452330 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 500904661)^166968220 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 500904661)^100180932 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (7 : ZMod 500904661)^29464980 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 491083 := Nat.prime_eq_prime_of_dvd_pow hq prime_491083 hd
            subst q
            change (7 : ZMod 500904661)^1020 ≠ 1
            reduce_mod_char
            decide

theorem prime_502802789 : Nat.Prime 502802789 := by
  apply lucas_primality 502802789 (2 : ZMod 502802789)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 502802789 - 1 = (2 : ℕ)^2 * ((125700697 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 502802789)^251401394 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 125700697 := Nat.prime_eq_prime_of_dvd_pow hq prime_125700697 hd
      subst q
      change (2 : ZMod 502802789)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_506612023 : Nat.Prime 506612023 := by
  apply lucas_primality 506612023 (6 : ZMod 506612023)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 506612023 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((12062191 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 506612023)^253306011 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 506612023)^168870674 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 506612023)^72373146 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 12062191 := Nat.prime_eq_prime_of_dvd_pow hq prime_12062191 hd
          subst q
          change (6 : ZMod 506612023)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_507144961 : Nat.Prime 507144961 := by
  apply lucas_primality 507144961 (23 : ZMod 507144961)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 507144961 - 1 = (2 : ℕ)^8 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((19 : ℕ)^1 * ((331 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (23 : ZMod 507144961)^253572480 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (23 : ZMod 507144961)^169048320 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (23 : ZMod 507144961)^101428992 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (23 : ZMod 507144961)^72449280 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
              subst q
              change (23 : ZMod 507144961)^26691840 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 331 := Nat.prime_eq_prime_of_dvd_pow hq prime_331 hd
              subst q
              change (23 : ZMod 507144961)^1532160 ≠ 1
              reduce_mod_char
              decide

theorem prime_509054113 : Nat.Prime 509054113 := by
  apply lucas_primality 509054113 (5 : ZMod 509054113)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 509054113 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((73 : ℕ)^1 * ((1153 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 509054113)^254527056 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 509054113)^169684704 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 509054113)^72722016 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
            subst q
            change (5 : ZMod 509054113)^6973344 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1153 := Nat.prime_eq_prime_of_dvd_pow hq prime_1153 hd
            subst q
            change (5 : ZMod 509054113)^441504 ≠ 1
            reduce_mod_char
            decide

theorem prime_522892091 : Nat.Prime 522892091 := by
  apply lucas_primality 522892091 (6 : ZMod 522892091)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 522892091 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((7469887 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 522892091)^261446045 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 522892091)^104578418 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 522892091)^74698870 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7469887 := Nat.prime_eq_prime_of_dvd_pow hq prime_7469887 hd
          subst q
          change (6 : ZMod 522892091)^70 ≠ 1
          reduce_mod_char
          decide

theorem prime_523545559 : Nat.Prime 523545559 := by
  apply lucas_primality 523545559 (3 : ZMod 523545559)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 523545559 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((87257593 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 523545559)^261772779 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 523545559)^174515186 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 87257593 := Nat.prime_eq_prime_of_dvd_pow hq prime_87257593 hd
        subst q
        change (3 : ZMod 523545559)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_526578841 : Nat.Prime 526578841 := by
  apply lucas_primality 526578841 (11 : ZMod 526578841)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 526578841 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((61 : ℕ)^1 * ((7993 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 526578841)^263289420 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 526578841)^175526280 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 526578841)^105315768 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
            subst q
            change (11 : ZMod 526578841)^8632440 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 7993 := Nat.prime_eq_prime_of_dvd_pow hq prime_7993 hd
            subst q
            change (11 : ZMod 526578841)^65880 ≠ 1
            reduce_mod_char
            decide

theorem prime_527056877 : Nat.Prime 527056877 := by
  apply lucas_primality 527056877 (2 : ZMod 527056877)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 527056877 - 1 = (2 : ℕ)^2 * ((131764219 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 527056877)^263528438 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 131764219 := Nat.prime_eq_prime_of_dvd_pow hq prime_131764219 hd
      subst q
      change (2 : ZMod 527056877)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_528099227 : Nat.Prime 528099227 := by
  apply lucas_primality 528099227 (2 : ZMod 528099227)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 528099227 - 1 = (2 : ℕ)^1 * ((67 : ℕ)^1 * ((3941039 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 528099227)^264049613 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
        subst q
        change (2 : ZMod 528099227)^7882078 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3941039 := Nat.prime_eq_prime_of_dvd_pow hq prime_3941039 hd
        subst q
        change (2 : ZMod 528099227)^134 ≠ 1
        reduce_mod_char
        decide

theorem prime_529513861 : Nat.Prime 529513861 := by
  apply lucas_primality 529513861 (6 : ZMod 529513861)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 529513861 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((8825231 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 529513861)^264756930 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 529513861)^176504620 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 529513861)^105902772 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 8825231 := Nat.prime_eq_prime_of_dvd_pow hq prime_8825231 hd
          subst q
          change (6 : ZMod 529513861)^60 ≠ 1
          reduce_mod_char
          decide

end LegendreK6.Pratt
