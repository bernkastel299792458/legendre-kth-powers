import LegendreK6.Pratt.Block016

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LegendreK6.Pratt

theorem prime_5016264769 : Nat.Prime 5016264769 := by
  apply lucas_primality 5016264769 (7 : ZMod 5016264769)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5016264769 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^3 * ((2902931 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 5016264769)^2508132384 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 5016264769)^1672088256 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2902931 := Nat.prime_eq_prime_of_dvd_pow hq prime_2902931 hd
        subst q
        change (7 : ZMod 5016264769)^1728 ≠ 1
        reduce_mod_char
        decide

theorem prime_5059942561 : Nat.Prime 5059942561 := by
  apply lucas_primality 5059942561 (26 : ZMod 5059942561)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5059942561 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((68899 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (26 : ZMod 5059942561)^2529971280 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (26 : ZMod 5059942561)^1686647520 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (26 : ZMod 5059942561)^1011988512 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (26 : ZMod 5059942561)^297643680 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 68899 := Nat.prime_eq_prime_of_dvd_pow hq prime_68899 hd
            subst q
            change (26 : ZMod 5059942561)^73440 ≠ 1
            reduce_mod_char
            decide

theorem prime_5125399991 : Nat.Prime 5125399991 := by
  apply lucas_primality 5125399991 (29 : ZMod 5125399991)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5125399991 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((563 : ℕ)^1 * ((883 : ℕ)^1 * ((1031 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (29 : ZMod 5125399991)^2562699995 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (29 : ZMod 5125399991)^1025079998 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 563 := Nat.prime_eq_prime_of_dvd_pow hq prime_563 hd
          subst q
          change (29 : ZMod 5125399991)^9103730 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 883 := Nat.prime_eq_prime_of_dvd_pow hq prime_883 hd
            subst q
            change (29 : ZMod 5125399991)^5804530 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1031 := Nat.prime_eq_prime_of_dvd_pow hq prime_1031 hd
            subst q
            change (29 : ZMod 5125399991)^4971290 ≠ 1
            reduce_mod_char
            decide

theorem prime_5260256789 : Nat.Prime 5260256789 := by
  apply lucas_primality 5260256789 (2 : ZMod 5260256789)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5260256789 - 1 = (2 : ℕ)^2 * ((1399 : ℕ)^1 * ((940003 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5260256789)^2630128394 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1399 := Nat.prime_eq_prime_of_dvd_pow hq prime_1399 hd
        subst q
        change (2 : ZMod 5260256789)^3760012 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 940003 := Nat.prime_eq_prime_of_dvd_pow hq prime_940003 hd
        subst q
        change (2 : ZMod 5260256789)^5596 ≠ 1
        reduce_mod_char
        decide

theorem prime_5264016389 : Nat.Prime 5264016389 := by
  apply lucas_primality 5264016389 (2 : ZMod 5264016389)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5264016389 - 1 = (2 : ℕ)^2 * ((1316004097 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5264016389)^2632008194 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1316004097 := Nat.prime_eq_prime_of_dvd_pow hq prime_1316004097 hd
      subst q
      change (2 : ZMod 5264016389)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_5327862457 : Nat.Prime 5327862457 := by
  apply lucas_primality 5327862457 (5 : ZMod 5327862457)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5327862457 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((167 : ℕ)^1 * ((189901 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 5327862457)^2663931228 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 5327862457)^1775954152 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 5327862457)^761123208 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
            subst q
            change (5 : ZMod 5327862457)^31903368 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 189901 := Nat.prime_eq_prime_of_dvd_pow hq prime_189901 hd
            subst q
            change (5 : ZMod 5327862457)^28056 ≠ 1
            reduce_mod_char
            decide

theorem prime_5389607669 : Nat.Prime 5389607669 := by
  apply lucas_primality 5389607669 (2 : ZMod 5389607669)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5389607669 - 1 = (2 : ℕ)^2 * ((1347401917 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5389607669)^2694803834 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1347401917 := Nat.prime_eq_prime_of_dvd_pow hq prime_1347401917 hd
      subst q
      change (2 : ZMod 5389607669)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_5410906651 : Nat.Prime 5410906651 := by
  apply lucas_primality 5410906651 (2 : ZMod 5410906651)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5410906651 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((5 : ℕ)^2 * ((331 : ℕ)^1 * ((12109 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5410906651)^2705453325 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 5410906651)^1803635550 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 5410906651)^1082181330 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 331 := Nat.prime_eq_prime_of_dvd_pow hq prime_331 hd
            subst q
            change (2 : ZMod 5410906651)^16347150 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 12109 := Nat.prime_eq_prime_of_dvd_pow hq prime_12109 hd
            subst q
            change (2 : ZMod 5410906651)^446850 ≠ 1
            reduce_mod_char
            decide

theorem prime_5446311499 : Nat.Prime 5446311499 := by
  apply lucas_primality 5446311499 (2 : ZMod 5446311499)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5446311499 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((11719 : ℕ)^1 * ((25819 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5446311499)^2723155749 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 5446311499)^1815437166 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11719 := Nat.prime_eq_prime_of_dvd_pow hq prime_11719 hd
          subst q
          change (2 : ZMod 5446311499)^464742 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 25819 := Nat.prime_eq_prime_of_dvd_pow hq prime_25819 hd
          subst q
          change (2 : ZMod 5446311499)^210942 ≠ 1
          reduce_mod_char
          decide

theorem prime_5452123949 : Nat.Prime 5452123949 := by
  apply lucas_primality 5452123949 (2 : ZMod 5452123949)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5452123949 - 1 = (2 : ℕ)^2 * ((19 : ℕ)^1 * ((71738473 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5452123949)^2726061974 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 5452123949)^286953892 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 71738473 := Nat.prime_eq_prime_of_dvd_pow hq prime_71738473 hd
        subst q
        change (2 : ZMod 5452123949)^76 ≠ 1
        reduce_mod_char
        decide

theorem prime_5489031767 : Nat.Prime 5489031767 := by
  apply lucas_primality 5489031767 (5 : ZMod 5489031767)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5489031767 - 1 = (2 : ℕ)^1 * ((11149 : ℕ)^1 * ((246167 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 5489031767)^2744515883 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11149 := Nat.prime_eq_prime_of_dvd_pow hq prime_11149 hd
        subst q
        change (5 : ZMod 5489031767)^492334 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 246167 := Nat.prime_eq_prime_of_dvd_pow hq prime_246167 hd
        subst q
        change (5 : ZMod 5489031767)^22298 ≠ 1
        reduce_mod_char
        decide

theorem prime_5561951543 : Nat.Prime 5561951543 := by
  apply lucas_primality 5561951543 (5 : ZMod 5561951543)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5561951543 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((229 : ℕ)^1 * ((307 : ℕ)^1 * ((5651 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 5561951543)^2780975771 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 5561951543)^794564506 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 229 := Nat.prime_eq_prime_of_dvd_pow hq prime_229 hd
          subst q
          change (5 : ZMod 5561951543)^24287998 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 307 := Nat.prime_eq_prime_of_dvd_pow hq prime_307 hd
            subst q
            change (5 : ZMod 5561951543)^18117106 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 5651 := Nat.prime_eq_prime_of_dvd_pow hq prime_5651 hd
            subst q
            change (5 : ZMod 5561951543)^984242 ≠ 1
            reduce_mod_char
            decide

theorem prime_5628387067 : Nat.Prime 5628387067 := by
  apply lucas_primality 5628387067 (5 : ZMod 5628387067)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5628387067 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((163 : ℕ)^1 * ((5754997 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 5628387067)^2814193533 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 5628387067)^1876129022 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
          subst q
          change (5 : ZMod 5628387067)^34529982 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 5754997 := Nat.prime_eq_prime_of_dvd_pow hq prime_5754997 hd
          subst q
          change (5 : ZMod 5628387067)^978 ≠ 1
          reduce_mod_char
          decide

theorem prime_5757957893 : Nat.Prime 5757957893 := by
  apply lucas_primality 5757957893 (2 : ZMod 5757957893)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5757957893 - 1 = (2 : ℕ)^2 * ((1439489473 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5757957893)^2878978946 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1439489473 := Nat.prime_eq_prime_of_dvd_pow hq prime_1439489473 hd
      subst q
      change (2 : ZMod 5757957893)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_5863915963 : Nat.Prime 5863915963 := by
  apply lucas_primality 5863915963 (3 : ZMod 5863915963)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5863915963 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((325773109 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 5863915963)^2931957981 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 5863915963)^1954638654 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 325773109 := Nat.prime_eq_prime_of_dvd_pow hq prime_325773109 hd
        subst q
        change (3 : ZMod 5863915963)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_5919353201 : Nat.Prime 5919353201 := by
  apply lucas_primality 5919353201 (7 : ZMod 5919353201)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5919353201 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^2 * ((3301 : ℕ)^1 * ((4483 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 5919353201)^2959676600 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 5919353201)^1183870640 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 3301 := Nat.prime_eq_prime_of_dvd_pow hq prime_3301 hd
          subst q
          change (7 : ZMod 5919353201)^1793200 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4483 := Nat.prime_eq_prime_of_dvd_pow hq prime_4483 hd
          subst q
          change (7 : ZMod 5919353201)^1320400 ≠ 1
          reduce_mod_char
          decide

theorem prime_6001737451 : Nat.Prime 6001737451 := by
  apply lucas_primality 6001737451 (10 : ZMod 6001737451)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6001737451 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((40011583 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 6001737451)^3000868725 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 6001737451)^2000579150 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 6001737451)^1200347490 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 40011583 := Nat.prime_eq_prime_of_dvd_pow hq prime_40011583 hd
          subst q
          change (10 : ZMod 6001737451)^150 ≠ 1
          reduce_mod_char
          decide

theorem prime_6126654389 : Nat.Prime 6126654389 := by
  apply lucas_primality 6126654389 (2 : ZMod 6126654389)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6126654389 - 1 = (2 : ℕ)^2 * ((1531663597 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6126654389)^3063327194 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1531663597 := Nat.prime_eq_prime_of_dvd_pow hq prime_1531663597 hd
      subst q
      change (2 : ZMod 6126654389)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_6265465081 : Nat.Prime 6265465081 := by
  apply lucas_primality 6265465081 (13 : ZMod 6265465081)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6265465081 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((19 : ℕ)^1 * ((29 : ℕ)^1 * ((13537 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 6265465081)^3132732540 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 6265465081)^2088488360 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 6265465081)^1253093016 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (13 : ZMod 6265465081)^895066440 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
              subst q
              change (13 : ZMod 6265465081)^329761320 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
                subst q
                change (13 : ZMod 6265465081)^216050520 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 13537 := Nat.prime_eq_prime_of_dvd_pow hq prime_13537 hd
                subst q
                change (13 : ZMod 6265465081)^462840 ≠ 1
                reduce_mod_char
                decide

theorem prime_6284907553 : Nat.Prime 6284907553 := by
  apply lucas_primality 6284907553 (5 : ZMod 6284907553)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6284907553 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((19 : ℕ)^1 * ((73 : ℕ)^1 * ((613 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 6284907553)^3142453776 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 6284907553)^2094969184 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 6284907553)^897843936 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (5 : ZMod 6284907553)^571355232 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
              subst q
              change (5 : ZMod 6284907553)^330784608 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
                subst q
                change (5 : ZMod 6284907553)^86094624 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 613 := Nat.prime_eq_prime_of_dvd_pow hq prime_613 hd
                subst q
                change (5 : ZMod 6284907553)^10252704 ≠ 1
                reduce_mod_char
                decide

theorem prime_6321363077 : Nat.Prime 6321363077 := by
  apply lucas_primality 6321363077 (2 : ZMod 6321363077)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6321363077 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((283 : ℕ)^1 * ((463 : ℕ)^1 * ((1723 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6321363077)^3160681538 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 6321363077)^903051868 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 283 := Nat.prime_eq_prime_of_dvd_pow hq prime_283 hd
          subst q
          change (2 : ZMod 6321363077)^22336972 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 463 := Nat.prime_eq_prime_of_dvd_pow hq prime_463 hd
            subst q
            change (2 : ZMod 6321363077)^13653052 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1723 := Nat.prime_eq_prime_of_dvd_pow hq prime_1723 hd
            subst q
            change (2 : ZMod 6321363077)^3668812 ≠ 1
            reduce_mod_char
            decide

theorem prime_6364500521 : Nat.Prime 6364500521 := by
  apply lucas_primality 6364500521 (6 : ZMod 6364500521)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6364500521 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((41 : ℕ)^1 * ((43 : ℕ)^1 * ((12893 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 6364500521)^3182250260 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 6364500521)^1272900104 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 6364500521)^909214360 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (6 : ZMod 6364500521)^155231720 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
              subst q
              change (6 : ZMod 6364500521)^148011640 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 12893 := Nat.prime_eq_prime_of_dvd_pow hq prime_12893 hd
              subst q
              change (6 : ZMod 6364500521)^493640 ≠ 1
              reduce_mod_char
              decide

theorem prime_6390795121 : Nat.Prime 6390795121 := by
  apply lucas_primality 6390795121 (23 : ZMod 6390795121)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6390795121 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((53 : ℕ)^1 * ((502421 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (23 : ZMod 6390795121)^3195397560 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (23 : ZMod 6390795121)^2130265040 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (23 : ZMod 6390795121)^1278159024 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
            subst q
            change (23 : ZMod 6390795121)^120581040 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 502421 := Nat.prime_eq_prime_of_dvd_pow hq prime_502421 hd
            subst q
            change (23 : ZMod 6390795121)^12720 ≠ 1
            reduce_mod_char
            decide

theorem prime_6635121901 : Nat.Prime 6635121901 := by
  apply lucas_primality 6635121901 (10 : ZMod 6635121901)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6635121901 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((11 : ℕ)^1 * ((1409 : ℕ)^1 * ((1427 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 6635121901)^3317560950 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 6635121901)^2211707300 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 6635121901)^1327024380 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (10 : ZMod 6635121901)^603192900 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1409 := Nat.prime_eq_prime_of_dvd_pow hq prime_1409 hd
              subst q
              change (10 : ZMod 6635121901)^4709100 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1427 := Nat.prime_eq_prime_of_dvd_pow hq prime_1427 hd
              subst q
              change (10 : ZMod 6635121901)^4649700 ≠ 1
              reduce_mod_char
              decide

theorem prime_6746219017 : Nat.Prime 6746219017 := by
  apply lucas_primality 6746219017 (5 : ZMod 6746219017)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6746219017 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((103 : ℕ)^1 * ((317 : ℕ)^1 * ((8609 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 6746219017)^3373109508 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 6746219017)^2248739672 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
          subst q
          change (5 : ZMod 6746219017)^65497272 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 317 := Nat.prime_eq_prime_of_dvd_pow hq prime_317 hd
            subst q
            change (5 : ZMod 6746219017)^21281448 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 8609 := Nat.prime_eq_prime_of_dvd_pow hq prime_8609 hd
            subst q
            change (5 : ZMod 6746219017)^783624 ≠ 1
            reduce_mod_char
            decide

theorem prime_6762024649 : Nat.Prime 6762024649 := by
  apply lucas_primality 6762024649 (17 : ZMod 6762024649)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6762024649 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((5641 : ℕ)^1 * ((16649 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 6762024649)^3381012324 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 6762024649)^2254008216 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5641 := Nat.prime_eq_prime_of_dvd_pow hq prime_5641 hd
          subst q
          change (17 : ZMod 6762024649)^1198728 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 16649 := Nat.prime_eq_prime_of_dvd_pow hq prime_16649 hd
          subst q
          change (17 : ZMod 6762024649)^406152 ≠ 1
          reduce_mod_char
          decide

theorem prime_6848718439 : Nat.Prime 6848718439 := by
  apply lucas_primality 6848718439 (3 : ZMod 6848718439)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6848718439 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((431 : ℕ)^1 * ((2648383 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 6848718439)^3424359219 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 6848718439)^2282906146 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 431 := Nat.prime_eq_prime_of_dvd_pow hq prime_431 hd
          subst q
          change (3 : ZMod 6848718439)^15890298 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2648383 := Nat.prime_eq_prime_of_dvd_pow hq prime_2648383 hd
          subst q
          change (3 : ZMod 6848718439)^2586 ≠ 1
          reduce_mod_char
          decide

theorem prime_7036301807 : Nat.Prime 7036301807 := by
  apply lucas_primality 7036301807 (5 : ZMod 7036301807)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7036301807 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((185165837 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 7036301807)^3518150903 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (5 : ZMod 7036301807)^370331674 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 185165837 := Nat.prime_eq_prime_of_dvd_pow hq prime_185165837 hd
        subst q
        change (5 : ZMod 7036301807)^38 ≠ 1
        reduce_mod_char
        decide

theorem prime_7256313877 : Nat.Prime 7256313877 := by
  apply lucas_primality 7256313877 (6 : ZMod 7256313877)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7256313877 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((86384689 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 7256313877)^3628156938 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 7256313877)^2418771292 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 7256313877)^1036616268 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 86384689 := Nat.prime_eq_prime_of_dvd_pow hq prime_86384689 hd
          subst q
          change (6 : ZMod 7256313877)^84 ≠ 1
          reduce_mod_char
          decide

theorem prime_7258164751 : Nat.Prime 7258164751 := by
  apply lucas_primality 7258164751 (3 : ZMod 7258164751)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7258164751 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^3 * ((911 : ℕ)^1 * ((3541 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 7258164751)^3629082375 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 7258164751)^2419388250 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 7258164751)^1451632950 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 911 := Nat.prime_eq_prime_of_dvd_pow hq prime_911 hd
            subst q
            change (3 : ZMod 7258164751)^7967250 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3541 := Nat.prime_eq_prime_of_dvd_pow hq prime_3541 hd
            subst q
            change (3 : ZMod 7258164751)^2049750 ≠ 1
            reduce_mod_char
            decide

theorem prime_7412801153 : Nat.Prime 7412801153 := by
  apply lucas_primality 7412801153 (3 : ZMod 7412801153)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7412801153 - 1 = (2 : ℕ)^7 * ((57912509 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 7412801153)^3706400576 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 57912509 := Nat.prime_eq_prime_of_dvd_pow hq prime_57912509 hd
      subst q
      change (3 : ZMod 7412801153)^128 ≠ 1
      reduce_mod_char
      decide

theorem prime_7549290143 : Nat.Prime 7549290143 := by
  apply lucas_primality 7549290143 (5 : ZMod 7549290143)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7549290143 - 1 = (2 : ℕ)^1 * ((3774645071 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 7549290143)^3774645071 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3774645071 := Nat.prime_eq_prime_of_dvd_pow hq prime_3774645071 hd
      subst q
      change (5 : ZMod 7549290143)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_7554566881 : Nat.Prime 7554566881 := by
  apply lucas_primality 7554566881 (23 : ZMod 7554566881)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7554566881 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((749461 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (23 : ZMod 7554566881)^3777283440 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (23 : ZMod 7554566881)^2518188960 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (23 : ZMod 7554566881)^1510913376 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (23 : ZMod 7554566881)^1079223840 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 749461 := Nat.prime_eq_prime_of_dvd_pow hq prime_749461 hd
            subst q
            change (23 : ZMod 7554566881)^10080 ≠ 1
            reduce_mod_char
            decide

theorem prime_7681965769 : Nat.Prime 7681965769 := by
  apply lucas_primality 7681965769 (17 : ZMod 7681965769)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7681965769 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((106693969 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 7681965769)^3840982884 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 7681965769)^2560655256 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 106693969 := Nat.prime_eq_prime_of_dvd_pow hq prime_106693969 hd
        subst q
        change (17 : ZMod 7681965769)^72 ≠ 1
        reduce_mod_char
        decide

theorem prime_7714780069 : Nat.Prime 7714780069 := by
  apply lucas_primality 7714780069 (7 : ZMod 7714780069)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7714780069 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((642898339 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 7714780069)^3857390034 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 7714780069)^2571593356 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 642898339 := Nat.prime_eq_prime_of_dvd_pow hq prime_642898339 hd
        subst q
        change (7 : ZMod 7714780069)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_7868030089 : Nat.Prime 7868030089 := by
  apply lucas_primality 7868030089 (7 : ZMod 7868030089)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7868030089 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((101 : ℕ)^1 * ((1451 : ℕ)^1 * ((2237 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 7868030089)^3934015044 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 7868030089)^2622676696 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
          subst q
          change (7 : ZMod 7868030089)^77901288 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1451 := Nat.prime_eq_prime_of_dvd_pow hq prime_1451 hd
            subst q
            change (7 : ZMod 7868030089)^5422488 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2237 := Nat.prime_eq_prime_of_dvd_pow hq prime_2237 hd
            subst q
            change (7 : ZMod 7868030089)^3517224 ≠ 1
            reduce_mod_char
            decide

theorem prime_8090531329 : Nat.Prime 8090531329 := by
  apply lucas_primality 8090531329 (7 : ZMod 8090531329)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8090531329 - 1 = (2 : ℕ)^9 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((478843 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 8090531329)^4045265664 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 8090531329)^2696843776 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (7 : ZMod 8090531329)^735502848 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 478843 := Nat.prime_eq_prime_of_dvd_pow hq prime_478843 hd
          subst q
          change (7 : ZMod 8090531329)^16896 ≠ 1
          reduce_mod_char
          decide

theorem prime_8097531553 : Nat.Prime 8097531553 := by
  apply lucas_primality 8097531553 (5 : ZMod 8097531553)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8097531553 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^3 * ((11 : ℕ)^1 * ((852013 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 8097531553)^4048765776 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 8097531553)^2699177184 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 8097531553)^736139232 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 852013 := Nat.prime_eq_prime_of_dvd_pow hq prime_852013 hd
          subst q
          change (5 : ZMod 8097531553)^9504 ≠ 1
          reduce_mod_char
          decide

theorem prime_8159599519 : Nat.Prime 8159599519 := by
  apply lucas_primality 8159599519 (3 : ZMod 8159599519)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8159599519 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((1013 : ℕ)^1 * ((191783 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 8159599519)^4079799759 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 8159599519)^2719866506 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 8159599519)^1165657074 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1013 := Nat.prime_eq_prime_of_dvd_pow hq prime_1013 hd
            subst q
            change (3 : ZMod 8159599519)^8054886 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 191783 := Nat.prime_eq_prime_of_dvd_pow hq prime_191783 hd
            subst q
            change (3 : ZMod 8159599519)^42546 ≠ 1
            reduce_mod_char
            decide

theorem prime_8235796181 : Nat.Prime 8235796181 := by
  apply lucas_primality 8235796181 (2 : ZMod 8235796181)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8235796181 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((83 : ℕ)^1 * ((4961323 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8235796181)^4117898090 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 8235796181)^1647159236 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
          subst q
          change (2 : ZMod 8235796181)^99226460 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4961323 := Nat.prime_eq_prime_of_dvd_pow hq prime_4961323 hd
          subst q
          change (2 : ZMod 8235796181)^1660 ≠ 1
          reduce_mod_char
          decide

theorem prime_8303765653 : Nat.Prime 8303765653 := by
  apply lucas_primality 8303765653 (2 : ZMod 8303765653)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8303765653 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((13 : ℕ)^2 * ((103 : ℕ)^1 * ((631 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8303765653)^4151882826 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 8303765653)^2767921884 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 8303765653)^1186252236 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (2 : ZMod 8303765653)^638751204 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
              subst q
              change (2 : ZMod 8303765653)^80619084 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 631 := Nat.prime_eq_prime_of_dvd_pow hq prime_631 hd
              subst q
              change (2 : ZMod 8303765653)^13159692 ≠ 1
              reduce_mod_char
              decide

theorem prime_8584827859 : Nat.Prime 8584827859 := by
  apply lucas_primality 8584827859 (2 : ZMod 8584827859)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8584827859 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((17 : ℕ)^1 * ((28054993 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8584827859)^4292413929 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 8584827859)^2861609286 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 8584827859)^504989874 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 28054993 := Nat.prime_eq_prime_of_dvd_pow hq prime_28054993 hd
          subst q
          change (2 : ZMod 8584827859)^306 ≠ 1
          reduce_mod_char
          decide

theorem prime_8740842787 : Nat.Prime 8740842787 := by
  apply lucas_primality 8740842787 (2 : ZMod 8740842787)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8740842787 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((13 : ℕ)^1 * ((53 : ℕ)^1 * ((234931 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8740842787)^4370421393 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 8740842787)^2913614262 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 8740842787)^672372522 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
            subst q
            change (2 : ZMod 8740842787)^164921562 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 234931 := Nat.prime_eq_prime_of_dvd_pow hq prime_234931 hd
            subst q
            change (2 : ZMod 8740842787)^37206 ≠ 1
            reduce_mod_char
            decide

theorem prime_9052615483 : Nat.Prime 9052615483 := by
  apply lucas_primality 9052615483 (5 : ZMod 9052615483)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9052615483 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((4219 : ℕ)^1 * ((357613 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 9052615483)^4526307741 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 9052615483)^3017538494 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 4219 := Nat.prime_eq_prime_of_dvd_pow hq prime_4219 hd
          subst q
          change (5 : ZMod 9052615483)^2145678 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 357613 := Nat.prime_eq_prime_of_dvd_pow hq prime_357613 hd
          subst q
          change (5 : ZMod 9052615483)^25314 ≠ 1
          reduce_mod_char
          decide

theorem prime_9062967097 : Nat.Prime 9062967097 := by
  apply lucas_primality 9062967097 (5 : ZMod 9062967097)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9062967097 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((41958181 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 9062967097)^4531483548 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 9062967097)^3020989032 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 41958181 := Nat.prime_eq_prime_of_dvd_pow hq prime_41958181 hd
        subst q
        change (5 : ZMod 9062967097)^216 ≠ 1
        reduce_mod_char
        decide

theorem prime_9073704203 : Nat.Prime 9073704203 := by
  apply lucas_primality 9073704203 (2 : ZMod 9073704203)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9073704203 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((266873653 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9073704203)^4536852101 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 9073704203)^533747306 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 266873653 := Nat.prime_eq_prime_of_dvd_pow hq prime_266873653 hd
        subst q
        change (2 : ZMod 9073704203)^34 ≠ 1
        reduce_mod_char
        decide

theorem prime_9299637287 : Nat.Prime 9299637287 := by
  apply lucas_primality 9299637287 (5 : ZMod 9299637287)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9299637287 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((107 : ℕ)^1 * ((2287171 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 9299637287)^4649818643 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (5 : ZMod 9299637287)^489454594 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
          subst q
          change (5 : ZMod 9299637287)^86912498 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2287171 := Nat.prime_eq_prime_of_dvd_pow hq prime_2287171 hd
          subst q
          change (5 : ZMod 9299637287)^4066 ≠ 1
          reduce_mod_char
          decide

theorem prime_9474296903 : Nat.Prime 9474296903 := by
  apply lucas_primality 9474296903 (7 : ZMod 9474296903)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9474296903 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^2 * ((96676499 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 9474296903)^4737148451 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 9474296903)^1353470986 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 96676499 := Nat.prime_eq_prime_of_dvd_pow hq prime_96676499 hd
        subst q
        change (7 : ZMod 9474296903)^98 ≠ 1
        reduce_mod_char
        decide

theorem prime_9698063521 : Nat.Prime 9698063521 := by
  apply lucas_primality 9698063521 (7 : ZMod 9698063521)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9698063521 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((20204299 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 9698063521)^4849031760 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 9698063521)^3232687840 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 9698063521)^1939612704 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 20204299 := Nat.prime_eq_prime_of_dvd_pow hq prime_20204299 hd
          subst q
          change (7 : ZMod 9698063521)^480 ≠ 1
          reduce_mod_char
          decide

theorem prime_9746104129 : Nat.Prime 9746104129 := by
  apply lucas_primality 9746104129 (7 : ZMod 9746104129)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9746104129 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^1 * ((50760959 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 9746104129)^4873052064 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 9746104129)^3248701376 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 50760959 := Nat.prime_eq_prime_of_dvd_pow hq prime_50760959 hd
        subst q
        change (7 : ZMod 9746104129)^192 ≠ 1
        reduce_mod_char
        decide

theorem prime_9810566587 : Nat.Prime 9810566587 := by
  apply lucas_primality 9810566587 (2 : ZMod 9810566587)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9810566587 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^5 * ((20186351 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9810566587)^4905283293 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 9810566587)^3270188862 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 20186351 := Nat.prime_eq_prime_of_dvd_pow hq prime_20186351 hd
        subst q
        change (2 : ZMod 9810566587)^486 ≠ 1
        reduce_mod_char
        decide

theorem prime_9909938693 : Nat.Prime 9909938693 := by
  apply lucas_primality 9909938693 (2 : ZMod 9909938693)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9909938693 - 1 = (2 : ℕ)^2 * ((2477484673 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9909938693)^4954969346 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 2477484673 := Nat.prime_eq_prime_of_dvd_pow hq prime_2477484673 hd
      subst q
      change (2 : ZMod 9909938693)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_10037162953 : Nat.Prime 10037162953 := by
  apply lucas_primality 10037162953 (7 : ZMod 10037162953)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10037162953 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^4 * ((103 : ℕ)^1 * ((150383 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 10037162953)^5018581476 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 10037162953)^3345720984 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
          subst q
          change (7 : ZMod 10037162953)^97448184 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 150383 := Nat.prime_eq_prime_of_dvd_pow hq prime_150383 hd
          subst q
          change (7 : ZMod 10037162953)^66744 ≠ 1
          reduce_mod_char
          decide

theorem prime_10099767577 : Nat.Prime 10099767577 := by
  apply lucas_primality 10099767577 (5 : ZMod 10099767577)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10099767577 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((420823649 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 10099767577)^5049883788 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 10099767577)^3366589192 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 420823649 := Nat.prime_eq_prime_of_dvd_pow hq prime_420823649 hd
        subst q
        change (5 : ZMod 10099767577)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_10260350993 : Nat.Prime 10260350993 := by
  apply lucas_primality 10260350993 (3 : ZMod 10260350993)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10260350993 - 1 = (2 : ℕ)^4 * ((8669 : ℕ)^1 * ((73973 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 10260350993)^5130175496 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 8669 := Nat.prime_eq_prime_of_dvd_pow hq prime_8669 hd
        subst q
        change (3 : ZMod 10260350993)^1183568 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 73973 := Nat.prime_eq_prime_of_dvd_pow hq prime_73973 hd
        subst q
        change (3 : ZMod 10260350993)^138704 ≠ 1
        reduce_mod_char
        decide

theorem prime_10363950841 : Nat.Prime 10363950841 := by
  apply lucas_primality 10363950841 (11 : ZMod 10363950841)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10363950841 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((86366257 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 10363950841)^5181975420 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 10363950841)^3454650280 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 10363950841)^2072790168 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 86366257 := Nat.prime_eq_prime_of_dvd_pow hq prime_86366257 hd
          subst q
          change (11 : ZMod 10363950841)^120 ≠ 1
          reduce_mod_char
          decide

theorem prime_10743230893 : Nat.Prime 10743230893 := by
  apply lucas_primality 10743230893 (2 : ZMod 10743230893)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10743230893 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((895269241 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 10743230893)^5371615446 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 10743230893)^3581076964 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 895269241 := Nat.prime_eq_prime_of_dvd_pow hq prime_895269241 hd
        subst q
        change (2 : ZMod 10743230893)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_10779215339 : Nat.Prime 10779215339 := by
  apply lucas_primality 10779215339 (2 : ZMod 10779215339)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10779215339 - 1 = (2 : ℕ)^1 * ((5389607669 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 10779215339)^5389607669 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 5389607669 := Nat.prime_eq_prime_of_dvd_pow hq prime_5389607669 hd
      subst q
      change (2 : ZMod 10779215339)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_10880032477 : Nat.Prime 10880032477 := by
  apply lucas_primality 10880032477 (5 : ZMod 10880032477)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10880032477 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((2467 : ℕ)^1 * ((367519 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 10880032477)^5440016238 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 10880032477)^3626677492 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2467 := Nat.prime_eq_prime_of_dvd_pow hq prime_2467 hd
          subst q
          change (5 : ZMod 10880032477)^4410228 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 367519 := Nat.prime_eq_prime_of_dvd_pow hq prime_367519 hd
          subst q
          change (5 : ZMod 10880032477)^29604 ≠ 1
          reduce_mod_char
          decide

theorem prime_10886222531 : Nat.Prime 10886222531 := by
  apply lucas_primality 10886222531 (7 : ZMod 10886222531)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10886222531 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((31181 : ℕ)^1 * ((34913 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 10886222531)^5443111265 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 10886222531)^2177244506 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31181 := Nat.prime_eq_prime_of_dvd_pow hq prime_31181 hd
          subst q
          change (7 : ZMod 10886222531)^349130 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 34913 := Nat.prime_eq_prime_of_dvd_pow hq prime_34913 hd
          subst q
          change (7 : ZMod 10886222531)^311810 ≠ 1
          reduce_mod_char
          decide

theorem prime_11114884871 : Nat.Prime 11114884871 := by
  apply lucas_primality 11114884871 (19 : ZMod 11114884871)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11114884871 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((467 : ℕ)^1 * ((557 : ℕ)^1 * ((4273 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 11114884871)^5557442435 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (19 : ZMod 11114884871)^2222976974 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 467 := Nat.prime_eq_prime_of_dvd_pow hq prime_467 hd
          subst q
          change (19 : ZMod 11114884871)^23800610 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 557 := Nat.prime_eq_prime_of_dvd_pow hq prime_557 hd
            subst q
            change (19 : ZMod 11114884871)^19954910 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 4273 := Nat.prime_eq_prime_of_dvd_pow hq prime_4273 hd
            subst q
            change (19 : ZMod 11114884871)^2601190 ≠ 1
            reduce_mod_char
            decide

theorem prime_11176251511 : Nat.Prime 11176251511 := by
  apply lucas_primality 11176251511 (21 : ZMod 11176251511)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11176251511 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((53 : ℕ)^1 * ((7029089 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (21 : ZMod 11176251511)^5588125755 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (21 : ZMod 11176251511)^3725417170 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (21 : ZMod 11176251511)^2235250302 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
            subst q
            change (21 : ZMod 11176251511)^210872670 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 7029089 := Nat.prime_eq_prime_of_dvd_pow hq prime_7029089 hd
            subst q
            change (21 : ZMod 11176251511)^1590 ≠ 1
            reduce_mod_char
            decide

theorem prime_11462227039 : Nat.Prime 11462227039 := by
  apply lucas_primality 11462227039 (6 : ZMod 11462227039)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11462227039 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((4241 : ℕ)^1 * ((150151 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 11462227039)^5731113519 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 11462227039)^3820742346 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 4241 := Nat.prime_eq_prime_of_dvd_pow hq prime_4241 hd
          subst q
          change (6 : ZMod 11462227039)^2702718 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 150151 := Nat.prime_eq_prime_of_dvd_pow hq prime_150151 hd
          subst q
          change (6 : ZMod 11462227039)^76338 ≠ 1
          reduce_mod_char
          decide

theorem prime_11629163177 : Nat.Prime 11629163177 := by
  apply lucas_primality 11629163177 (3 : ZMod 11629163177)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11629163177 - 1 = (2 : ℕ)^3 * ((31 : ℕ)^1 * ((107 : ℕ)^1 * ((438241 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 11629163177)^5814581588 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (3 : ZMod 11629163177)^375134296 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
          subst q
          change (3 : ZMod 11629163177)^108683768 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 438241 := Nat.prime_eq_prime_of_dvd_pow hq prime_438241 hd
          subst q
          change (3 : ZMod 11629163177)^26536 ≠ 1
          reduce_mod_char
          decide

theorem prime_11737870057 : Nat.Prime 11737870057 := by
  apply lucas_primality 11737870057 (29 : ZMod 11737870057)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11737870057 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^5 * ((11 : ℕ)^1 * ((548909 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (29 : ZMod 11737870057)^5868935028 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (29 : ZMod 11737870057)^3912623352 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (29 : ZMod 11737870057)^1067079096 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 548909 := Nat.prime_eq_prime_of_dvd_pow hq prime_548909 hd
          subst q
          change (29 : ZMod 11737870057)^21384 ≠ 1
          reduce_mod_char
          decide

theorem prime_11823851497 : Nat.Prime 11823851497 := by
  apply lucas_primality 11823851497 (5 : ZMod 11823851497)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11823851497 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((89 : ℕ)^1 * ((5535511 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 11823851497)^5911925748 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 11823851497)^3941283832 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (5 : ZMod 11823851497)^132852264 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 5535511 := Nat.prime_eq_prime_of_dvd_pow hq prime_5535511 hd
          subst q
          change (5 : ZMod 11823851497)^2136 ≠ 1
          reduce_mod_char
          decide

theorem prime_11838706403 : Nat.Prime 11838706403 := by
  apply lucas_primality 11838706403 (2 : ZMod 11838706403)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11838706403 - 1 = (2 : ℕ)^1 * ((5919353201 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 11838706403)^5919353201 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 5919353201 := Nat.prime_eq_prime_of_dvd_pow hq prime_5919353201 hd
      subst q
      change (2 : ZMod 11838706403)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_11905617601 : Nat.Prime 11905617601 := by
  apply lucas_primality 11905617601 (13 : ZMod 11905617601)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11905617601 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^3 * ((5 : ℕ)^2 * ((275593 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 11905617601)^5952808800 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 11905617601)^3968539200 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 11905617601)^2381123520 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 275593 := Nat.prime_eq_prime_of_dvd_pow hq prime_275593 hd
          subst q
          change (13 : ZMod 11905617601)^43200 ≠ 1
          reduce_mod_char
          decide

theorem prime_12188961277 : Nat.Prime 12188961277 := by
  apply lucas_primality 12188961277 (5 : ZMod 12188961277)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12188961277 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((59 : ℕ)^1 * ((1373 : ℕ)^1 * ((12539 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 12188961277)^6094480638 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 12188961277)^4062987092 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (5 : ZMod 12188961277)^206592564 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1373 := Nat.prime_eq_prime_of_dvd_pow hq prime_1373 hd
            subst q
            change (5 : ZMod 12188961277)^8877612 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 12539 := Nat.prime_eq_prime_of_dvd_pow hq prime_12539 hd
            subst q
            change (5 : ZMod 12188961277)^972084 ≠ 1
            reduce_mod_char
            decide

theorem prime_12230590481 : Nat.Prime 12230590481 := by
  apply lucas_primality 12230590481 (3 : ZMod 12230590481)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12230590481 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((6389 : ℕ)^1 * ((23929 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 12230590481)^6115295240 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 12230590481)^2446118096 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 6389 := Nat.prime_eq_prime_of_dvd_pow hq prime_6389 hd
          subst q
          change (3 : ZMod 12230590481)^1914320 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 23929 := Nat.prime_eq_prime_of_dvd_pow hq prime_23929 hd
          subst q
          change (3 : ZMod 12230590481)^511120 ≠ 1
          reduce_mod_char
          decide

theorem prime_12264341933 : Nat.Prime 12264341933 := by
  apply lucas_primality 12264341933 (2 : ZMod 12264341933)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12264341933 - 1 = (2 : ℕ)^2 * ((73 : ℕ)^1 * ((42001171 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 12264341933)^6132170966 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
        subst q
        change (2 : ZMod 12264341933)^168004684 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 42001171 := Nat.prime_eq_prime_of_dvd_pow hq prime_42001171 hd
        subst q
        change (2 : ZMod 12264341933)^292 ≠ 1
        reduce_mod_char
        decide

theorem prime_12306271897 : Nat.Prime 12306271897 := by
  apply lucas_primality 12306271897 (11 : ZMod 12306271897)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12306271897 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((56973481 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 12306271897)^6153135948 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 12306271897)^4102090632 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 56973481 := Nat.prime_eq_prime_of_dvd_pow hq prime_56973481 hd
        subst q
        change (11 : ZMod 12306271897)^216 ≠ 1
        reduce_mod_char
        decide

theorem prime_12327608929 : Nat.Prime 12327608929 := by
  apply lucas_primality 12327608929 (7 : ZMod 12327608929)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12327608929 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((128412593 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 12327608929)^6163804464 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 12327608929)^4109202976 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 128412593 := Nat.prime_eq_prime_of_dvd_pow hq prime_128412593 hd
        subst q
        change (7 : ZMod 12327608929)^96 ≠ 1
        reduce_mod_char
        decide

theorem prime_12400871831 : Nat.Prime 12400871831 := by
  apply lucas_primality 12400871831 (31 : ZMod 12400871831)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12400871831 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((29 : ℕ)^1 * ((42761627 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (31 : ZMod 12400871831)^6200435915 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (31 : ZMod 12400871831)^2480174366 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (31 : ZMod 12400871831)^427616270 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 42761627 := Nat.prime_eq_prime_of_dvd_pow hq prime_42761627 hd
          subst q
          change (31 : ZMod 12400871831)^290 ≠ 1
          reduce_mod_char
          decide

theorem prime_12631036199 : Nat.Prime 12631036199 := by
  apply lucas_primality 12631036199 (11 : ZMod 12631036199)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12631036199 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((881 : ℕ)^1 * ((651689 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 12631036199)^6315518099 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (11 : ZMod 12631036199)^1148276018 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 881 := Nat.prime_eq_prime_of_dvd_pow hq prime_881 hd
          subst q
          change (11 : ZMod 12631036199)^14337158 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 651689 := Nat.prime_eq_prime_of_dvd_pow hq prime_651689 hd
          subst q
          change (11 : ZMod 12631036199)^19382 ≠ 1
          reduce_mod_char
          decide

theorem prime_12653479133 : Nat.Prime 12653479133 := by
  apply lucas_primality 12653479133 (3 : ZMod 12653479133)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12653479133 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^2 * ((59 : ℕ)^1 * ((449 : ℕ)^1 * ((2437 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 12653479133)^6326739566 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 12653479133)^1807639876 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (3 : ZMod 12653479133)^214465748 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 449 := Nat.prime_eq_prime_of_dvd_pow hq prime_449 hd
            subst q
            change (3 : ZMod 12653479133)^28181468 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2437 := Nat.prime_eq_prime_of_dvd_pow hq prime_2437 hd
            subst q
            change (3 : ZMod 12653479133)^5192236 ≠ 1
            reduce_mod_char
            decide

theorem prime_12676012873 : Nat.Prime 12676012873 := by
  apply lucas_primality 12676012873 (7 : ZMod 12676012873)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12676012873 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((229 : ℕ)^1 * ((135671 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 12676012873)^6338006436 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 12676012873)^4225337624 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (7 : ZMod 12676012873)^745647816 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 229 := Nat.prime_eq_prime_of_dvd_pow hq prime_229 hd
            subst q
            change (7 : ZMod 12676012873)^55353768 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 135671 := Nat.prime_eq_prime_of_dvd_pow hq prime_135671 hd
            subst q
            change (7 : ZMod 12676012873)^93432 ≠ 1
            reduce_mod_char
            decide

theorem prime_12973326577 : Nat.Prime 12973326577 := by
  apply lucas_primality 12973326577 (15 : ZMod 12973326577)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12973326577 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((37 : ℕ)^1 * ((1043543 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (15 : ZMod 12973326577)^6486663288 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (15 : ZMod 12973326577)^4324442192 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (15 : ZMod 12973326577)^1853332368 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
            subst q
            change (15 : ZMod 12973326577)^350630448 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1043543 := Nat.prime_eq_prime_of_dvd_pow hq prime_1043543 hd
            subst q
            change (15 : ZMod 12973326577)^12432 ≠ 1
            reduce_mod_char
            decide

theorem prime_13222522771 : Nat.Prime 13222522771 := by
  apply lucas_primality 13222522771 (3 : ZMod 13222522771)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13222522771 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((440750759 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 13222522771)^6611261385 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 13222522771)^4407507590 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 13222522771)^2644504554 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 440750759 := Nat.prime_eq_prime_of_dvd_pow hq prime_440750759 hd
          subst q
          change (3 : ZMod 13222522771)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_13255541231 : Nat.Prime 13255541231 := by
  apply lucas_primality 13255541231 (7 : ZMod 13255541231)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13255541231 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((109 : ℕ)^1 * ((12161047 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 13255541231)^6627770615 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 13255541231)^2651108246 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
          subst q
          change (7 : ZMod 13255541231)^121610470 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 12161047 := Nat.prime_eq_prime_of_dvd_pow hq prime_12161047 hd
          subst q
          change (7 : ZMod 13255541231)^1090 ≠ 1
          reduce_mod_char
          decide

theorem prime_13555867441 : Nat.Prime 13555867441 := by
  apply lucas_primality 13555867441 (11 : ZMod 13555867441)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13555867441 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((251 : ℕ)^1 * ((307 : ℕ)^1 * ((733 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 13555867441)^6777933720 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 13555867441)^4518622480 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 13555867441)^2711173488 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 251 := Nat.prime_eq_prime_of_dvd_pow hq prime_251 hd
            subst q
            change (11 : ZMod 13555867441)^54007440 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 307 := Nat.prime_eq_prime_of_dvd_pow hq prime_307 hd
              subst q
              change (11 : ZMod 13555867441)^44155920 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 733 := Nat.prime_eq_prime_of_dvd_pow hq prime_733 hd
              subst q
              change (11 : ZMod 13555867441)^18493680 ≠ 1
              reduce_mod_char
              decide

theorem prime_13705927009 : Nat.Prime 13705927009 := by
  apply lucas_primality 13705927009 (14 : ZMod 13705927009)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13705927009 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((61 : ℕ)^1 * ((2340493 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 13705927009)^6852963504 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 13705927009)^4568642336 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (14 : ZMod 13705927009)^224687328 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2340493 := Nat.prime_eq_prime_of_dvd_pow hq prime_2340493 hd
          subst q
          change (14 : ZMod 13705927009)^5856 ≠ 1
          reduce_mod_char
          decide

theorem prime_13799563699 : Nat.Prime 13799563699 := by
  apply lucas_primality 13799563699 (2 : ZMod 13799563699)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13799563699 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((43 : ℕ)^1 * ((1039 : ℕ)^1 * ((51479 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 13799563699)^6899781849 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 13799563699)^4599854566 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (2 : ZMod 13799563699)^320920086 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1039 := Nat.prime_eq_prime_of_dvd_pow hq prime_1039 hd
            subst q
            change (2 : ZMod 13799563699)^13281582 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 51479 := Nat.prime_eq_prime_of_dvd_pow hq prime_51479 hd
            subst q
            change (2 : ZMod 13799563699)^268062 ≠ 1
            reduce_mod_char
            decide

theorem prime_13841287217 : Nat.Prime 13841287217 := by
  apply lucas_primality 13841287217 (3 : ZMod 13841287217)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13841287217 - 1 = (2 : ℕ)^4 * ((31 : ℕ)^1 * ((27905821 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 13841287217)^6920643608 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (3 : ZMod 13841287217)^446493136 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 27905821 := Nat.prime_eq_prime_of_dvd_pow hq prime_27905821 hd
        subst q
        change (3 : ZMod 13841287217)^496 ≠ 1
        reduce_mod_char
        decide

theorem prime_13842990769 : Nat.Prime 13842990769 := by
  apply lucas_primality 13842990769 (7 : ZMod 13842990769)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13842990769 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((288395641 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 13842990769)^6921495384 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 13842990769)^4614330256 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 288395641 := Nat.prime_eq_prime_of_dvd_pow hq prime_288395641 hd
        subst q
        change (7 : ZMod 13842990769)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_13889004847 : Nat.Prime 13889004847 := by
  apply lucas_primality 13889004847 (3 : ZMod 13889004847)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13889004847 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((953 : ℕ)^1 * ((2428997 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 13889004847)^6944502423 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 13889004847)^4629668282 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 953 := Nat.prime_eq_prime_of_dvd_pow hq prime_953 hd
          subst q
          change (3 : ZMod 13889004847)^14573982 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2428997 := Nat.prime_eq_prime_of_dvd_pow hq prime_2428997 hd
          subst q
          change (3 : ZMod 13889004847)^5718 ≠ 1
          reduce_mod_char
          decide

theorem prime_14951184307 : Nat.Prime 14951184307 := by
  apply lucas_primality 14951184307 (2 : ZMod 14951184307)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14951184307 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((313 : ℕ)^1 * ((7961227 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 14951184307)^7475592153 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 14951184307)^4983728102 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 313 := Nat.prime_eq_prime_of_dvd_pow hq prime_313 hd
          subst q
          change (2 : ZMod 14951184307)^47767362 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7961227 := Nat.prime_eq_prime_of_dvd_pow hq prime_7961227 hd
          subst q
          change (2 : ZMod 14951184307)^1878 ≠ 1
          reduce_mod_char
          decide

theorem prime_14968331731 : Nat.Prime 14968331731 := by
  apply lucas_primality 14968331731 (11 : ZMod 14968331731)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14968331731 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((29 : ℕ)^1 * ((521363 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 14968331731)^7484165865 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 14968331731)^4989443910 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 14968331731)^2993666346 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (11 : ZMod 14968331731)^1360757430 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
              subst q
              change (11 : ZMod 14968331731)^516149370 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 521363 := Nat.prime_eq_prime_of_dvd_pow hq prime_521363 hd
              subst q
              change (11 : ZMod 14968331731)^28710 ≠ 1
              reduce_mod_char
              decide

theorem prime_15073018861 : Nat.Prime 15073018861 := by
  apply lucas_primality 15073018861 (6 : ZMod 15073018861)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15073018861 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((1291 : ℕ)^1 * ((194591 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 15073018861)^7536509430 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 15073018861)^5024339620 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 15073018861)^3014603772 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1291 := Nat.prime_eq_prime_of_dvd_pow hq prime_1291 hd
            subst q
            change (6 : ZMod 15073018861)^11675460 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 194591 := Nat.prime_eq_prime_of_dvd_pow hq prime_194591 hd
            subst q
            change (6 : ZMod 15073018861)^77460 ≠ 1
            reduce_mod_char
            decide

theorem prime_15458455699 : Nat.Prime 15458455699 := by
  apply lucas_primality 15458455699 (2 : ZMod 15458455699)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15458455699 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((368058469 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 15458455699)^7729227849 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 15458455699)^5152818566 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 15458455699)^2208350814 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 368058469 := Nat.prime_eq_prime_of_dvd_pow hq prime_368058469 hd
          subst q
          change (2 : ZMod 15458455699)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_15530665343 : Nat.Prime 15530665343 := by
  apply lucas_primality 15530665343 (5 : ZMod 15530665343)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15530665343 - 1 = (2 : ℕ)^1 * ((6679 : ℕ)^1 * ((1162649 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 15530665343)^7765332671 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 6679 := Nat.prime_eq_prime_of_dvd_pow hq prime_6679 hd
        subst q
        change (5 : ZMod 15530665343)^2325298 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1162649 := Nat.prime_eq_prime_of_dvd_pow hq prime_1162649 hd
        subst q
        change (5 : ZMod 15530665343)^13358 ≠ 1
        reduce_mod_char
        decide

theorem prime_15533696041 : Nat.Prime 15533696041 := by
  apply lucas_primality 15533696041 (11 : ZMod 15533696041)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15533696041 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((10781 : ℕ)^1 * ((12007 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 15533696041)^7766848020 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 15533696041)^5177898680 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 15533696041)^3106739208 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 10781 := Nat.prime_eq_prime_of_dvd_pow hq prime_10781 hd
            subst q
            change (11 : ZMod 15533696041)^1440840 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 12007 := Nat.prime_eq_prime_of_dvd_pow hq prime_12007 hd
            subst q
            change (11 : ZMod 15533696041)^1293720 ≠ 1
            reduce_mod_char
            decide

theorem prime_15573796829 : Nat.Prime 15573796829 := by
  apply lucas_primality 15573796829 (2 : ZMod 15573796829)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15573796829 - 1 = (2 : ℕ)^2 * ((1019 : ℕ)^1 * ((3820853 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 15573796829)^7786898414 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1019 := Nat.prime_eq_prime_of_dvd_pow hq prime_1019 hd
        subst q
        change (2 : ZMod 15573796829)^15283412 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3820853 := Nat.prime_eq_prime_of_dvd_pow hq prime_3820853 hd
        subst q
        change (2 : ZMod 15573796829)^4076 ≠ 1
        reduce_mod_char
        decide

theorem prime_15593168287 : Nat.Prime 15593168287 := by
  apply lucas_primality 15593168287 (5 : ZMod 15593168287)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15593168287 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((47 : ℕ)^1 * ((617 : ℕ)^1 * ((29873 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 15593168287)^7796584143 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 15593168287)^5197722762 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (5 : ZMod 15593168287)^331769538 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 617 := Nat.prime_eq_prime_of_dvd_pow hq prime_617 hd
            subst q
            change (5 : ZMod 15593168287)^25272558 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 29873 := Nat.prime_eq_prime_of_dvd_pow hq prime_29873 hd
            subst q
            change (5 : ZMod 15593168287)^521982 ≠ 1
            reduce_mod_char
            decide

theorem prime_15625000007 : Nat.Prime 15625000007 := by
  apply lucas_primality 15625000007 (5 : ZMod 15625000007)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15625000007 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((409 : ℕ)^1 * ((248071 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 15625000007)^7812500003 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 15625000007)^2232142858 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 15625000007)^1420454546 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 409 := Nat.prime_eq_prime_of_dvd_pow hq prime_409 hd
            subst q
            change (5 : ZMod 15625000007)^38202934 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 248071 := Nat.prime_eq_prime_of_dvd_pow hq prime_248071 hd
            subst q
            change (5 : ZMod 15625000007)^62986 ≠ 1
            reduce_mod_char
            decide

theorem prime_16126393981 : Nat.Prime 16126393981 := by
  apply lucas_primality 16126393981 (6 : ZMod 16126393981)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16126393981 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((269 : ℕ)^1 * ((821 : ℕ)^1 * ((1217 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 16126393981)^8063196990 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 16126393981)^5375464660 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 16126393981)^3225278796 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
            subst q
            change (6 : ZMod 16126393981)^59949420 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 821 := Nat.prime_eq_prime_of_dvd_pow hq prime_821 hd
              subst q
              change (6 : ZMod 16126393981)^19642380 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1217 := Nat.prime_eq_prime_of_dvd_pow hq prime_1217 hd
              subst q
              change (6 : ZMod 16126393981)^13250940 ≠ 1
              reduce_mod_char
              decide

theorem prime_17462328833 : Nat.Prime 17462328833 := by
  apply lucas_primality 17462328833 (3 : ZMod 17462328833)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17462328833 - 1 = (2 : ℕ)^9 * ((13 : ℕ)^1 * ((73 : ℕ)^1 * ((83 : ℕ)^1 * ((433 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 17462328833)^8731164416 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 17462328833)^1343256064 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
          subst q
          change (3 : ZMod 17462328833)^239209984 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
            subst q
            change (3 : ZMod 17462328833)^210389504 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 433 := Nat.prime_eq_prime_of_dvd_pow hq prime_433 hd
            subst q
            change (3 : ZMod 17462328833)^40328704 ≠ 1
            reduce_mod_char
            decide

theorem prime_17470062769 : Nat.Prime 17470062769 := by
  apply lucas_primality 17470062769 (7 : ZMod 17470062769)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17470062769 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((363959641 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 17470062769)^8735031384 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 17470062769)^5823354256 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 363959641 := Nat.prime_eq_prime_of_dvd_pow hq prime_363959641 hd
        subst q
        change (7 : ZMod 17470062769)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_17596287803 : Nat.Prime 17596287803 := by
  apply lucas_primality 17596287803 (2 : ZMod 17596287803)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17596287803 - 1 = (2 : ℕ)^1 * ((37 : ℕ)^1 * ((1301 : ℕ)^1 * ((182773 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 17596287803)^8798143901 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (2 : ZMod 17596287803)^475575346 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1301 := Nat.prime_eq_prime_of_dvd_pow hq prime_1301 hd
          subst q
          change (2 : ZMod 17596287803)^13525202 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 182773 := Nat.prime_eq_prime_of_dvd_pow hq prime_182773 hd
          subst q
          change (2 : ZMod 17596287803)^96274 ≠ 1
          reduce_mod_char
          decide

theorem prime_17892466727 : Nat.Prime 17892466727 := by
  apply lucas_primality 17892466727 (5 : ZMod 17892466727)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17892466727 - 1 = (2 : ℕ)^1 * ((31 : ℕ)^1 * ((288588173 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 17892466727)^8946233363 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (5 : ZMod 17892466727)^577176346 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 288588173 := Nat.prime_eq_prime_of_dvd_pow hq prime_288588173 hd
        subst q
        change (5 : ZMod 17892466727)^62 ≠ 1
        reduce_mod_char
        decide

theorem prime_18392925029 : Nat.Prime 18392925029 := by
  apply lucas_primality 18392925029 (2 : ZMod 18392925029)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18392925029 - 1 = (2 : ℕ)^2 * ((59 : ℕ)^1 * ((2027 : ℕ)^1 * ((38449 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 18392925029)^9196462514 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
        subst q
        change (2 : ZMod 18392925029)^311744492 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2027 := Nat.prime_eq_prime_of_dvd_pow hq prime_2027 hd
          subst q
          change (2 : ZMod 18392925029)^9073964 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 38449 := Nat.prime_eq_prime_of_dvd_pow hq prime_38449 hd
          subst q
          change (2 : ZMod 18392925029)^478372 ≠ 1
          reduce_mod_char
          decide

theorem prime_18724571429 : Nat.Prime 18724571429 := by
  apply lucas_primality 18724571429 (2 : ZMod 18724571429)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18724571429 - 1 = (2 : ℕ)^2 * ((457 : ℕ)^1 * ((10243201 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 18724571429)^9362285714 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 457 := Nat.prime_eq_prime_of_dvd_pow hq prime_457 hd
        subst q
        change (2 : ZMod 18724571429)^40972804 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 10243201 := Nat.prime_eq_prime_of_dvd_pow hq prime_10243201 hd
        subst q
        change (2 : ZMod 18724571429)^1828 ≠ 1
        reduce_mod_char
        decide

theorem prime_18985324777 : Nat.Prime 18985324777 := by
  apply lucas_primality 18985324777 (5 : ZMod 18985324777)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18985324777 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((71914109 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 18985324777)^9492662388 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 18985324777)^6328441592 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 18985324777)^1725938616 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 71914109 := Nat.prime_eq_prime_of_dvd_pow hq prime_71914109 hd
          subst q
          change (5 : ZMod 18985324777)^264 ≠ 1
          reduce_mod_char
          decide

theorem prime_19253805133 : Nat.Prime 19253805133 := by
  apply lucas_primality 19253805133 (2 : ZMod 19253805133)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19253805133 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((1604483761 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 19253805133)^9626902566 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 19253805133)^6417935044 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1604483761 := Nat.prime_eq_prime_of_dvd_pow hq prime_1604483761 hd
        subst q
        change (2 : ZMod 19253805133)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_19566662923 : Nat.Prime 19566662923 := by
  apply lucas_primality 19566662923 (5 : ZMod 19566662923)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19566662923 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((1087036829 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 19566662923)^9783331461 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 19566662923)^6522220974 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1087036829 := Nat.prime_eq_prime_of_dvd_pow hq prime_1087036829 hd
        subst q
        change (5 : ZMod 19566662923)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_19681509293 : Nat.Prime 19681509293 := by
  apply lucas_primality 19681509293 (2 : ZMod 19681509293)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19681509293 - 1 = (2 : ℕ)^2 * ((41 : ℕ)^1 * ((2741 : ℕ)^1 * ((43783 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 19681509293)^9840754646 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
        subst q
        change (2 : ZMod 19681509293)^480036812 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2741 := Nat.prime_eq_prime_of_dvd_pow hq prime_2741 hd
          subst q
          change (2 : ZMod 19681509293)^7180412 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 43783 := Nat.prime_eq_prime_of_dvd_pow hq prime_43783 hd
          subst q
          change (2 : ZMod 19681509293)^449524 ≠ 1
          reduce_mod_char
          decide

theorem prime_19770609739 : Nat.Prime 19770609739 := by
  apply lucas_primality 19770609739 (2 : ZMod 19770609739)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19770609739 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((299554693 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 19770609739)^9885304869 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 19770609739)^6590203246 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 19770609739)^1797328158 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 299554693 := Nat.prime_eq_prime_of_dvd_pow hq prime_299554693 hd
          subst q
          change (2 : ZMod 19770609739)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_20162503541 : Nat.Prime 20162503541 := by
  apply lucas_primality 20162503541 (2 : ZMod 20162503541)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20162503541 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((31 : ℕ)^1 * ((1912951 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 20162503541)^10081251770 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 20162503541)^4032500708 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 20162503541)^1186029620 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (2 : ZMod 20162503541)^650403340 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1912951 := Nat.prime_eq_prime_of_dvd_pow hq prime_1912951 hd
            subst q
            change (2 : ZMod 20162503541)^10540 ≠ 1
            reduce_mod_char
            decide

theorem prime_20332189309 : Nat.Prime 20332189309 := by
  apply lucas_primality 20332189309 (6 : ZMod 20332189309)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20332189309 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((1694349109 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 20332189309)^10166094654 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 20332189309)^6777396436 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1694349109 := Nat.prime_eq_prime_of_dvd_pow hq prime_1694349109 hd
        subst q
        change (6 : ZMod 20332189309)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_20449732201 : Nat.Prime 20449732201 := by
  apply lucas_primality 20449732201 (14 : ZMod 20449732201)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20449732201 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((34082887 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 20449732201)^10224866100 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 20449732201)^6816577400 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (14 : ZMod 20449732201)^4089946440 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 34082887 := Nat.prime_eq_prime_of_dvd_pow hq prime_34082887 hd
          subst q
          change (14 : ZMod 20449732201)^600 ≠ 1
          reduce_mod_char
          decide

theorem prime_20702092577 : Nat.Prime 20702092577 := by
  apply lucas_primality 20702092577 (3 : ZMod 20702092577)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20702092577 - 1 = (2 : ℕ)^5 * ((11 : ℕ)^1 * ((58812763 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 20702092577)^10351046288 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 20702092577)^1882008416 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 58812763 := Nat.prime_eq_prime_of_dvd_pow hq prime_58812763 hd
        subst q
        change (3 : ZMod 20702092577)^352 ≠ 1
        reduce_mod_char
        decide

theorem prime_20763514897 : Nat.Prime 20763514897 := by
  apply lucas_primality 20763514897 (7 : ZMod 20763514897)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20763514897 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((53 : ℕ)^1 * ((467 : ℕ)^1 * ((17477 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 20763514897)^10381757448 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 20763514897)^6921171632 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (7 : ZMod 20763514897)^391764432 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 467 := Nat.prime_eq_prime_of_dvd_pow hq prime_467 hd
            subst q
            change (7 : ZMod 20763514897)^44461488 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 17477 := Nat.prime_eq_prime_of_dvd_pow hq prime_17477 hd
            subst q
            change (7 : ZMod 20763514897)^1188048 ≠ 1
            reduce_mod_char
            decide

theorem prime_20828260667 : Nat.Prime 20828260667 := by
  apply lucas_primality 20828260667 (2 : ZMod 20828260667)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20828260667 - 1 = (2 : ℕ)^1 * ((3547 : ℕ)^1 * ((2936039 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 20828260667)^10414130333 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3547 := Nat.prime_eq_prime_of_dvd_pow hq prime_3547 hd
        subst q
        change (2 : ZMod 20828260667)^5872078 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2936039 := Nat.prime_eq_prime_of_dvd_pow hq prime_2936039 hd
        subst q
        change (2 : ZMod 20828260667)^7094 ≠ 1
        reduce_mod_char
        decide

theorem prime_20925758387 : Nat.Prime 20925758387 := by
  apply lucas_primality 20925758387 (5 : ZMod 20925758387)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20925758387 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((23 : ℕ)^1 * ((3967 : ℕ)^1 * ((8821 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 20925758387)^10462879193 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (5 : ZMod 20925758387)^1609673722 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (5 : ZMod 20925758387)^909815582 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3967 := Nat.prime_eq_prime_of_dvd_pow hq prime_3967 hd
            subst q
            change (5 : ZMod 20925758387)^5274958 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 8821 := Nat.prime_eq_prime_of_dvd_pow hq prime_8821 hd
            subst q
            change (5 : ZMod 20925758387)^2372266 ≠ 1
            reduce_mod_char
            decide

theorem prime_21090266831 : Nat.Prime 21090266831 := by
  apply lucas_primality 21090266831 (7 : ZMod 21090266831)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21090266831 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((2109026683 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 21090266831)^10545133415 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 21090266831)^4218053366 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2109026683 := Nat.prime_eq_prime_of_dvd_pow hq prime_2109026683 hd
        subst q
        change (7 : ZMod 21090266831)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_21503466671 : Nat.Prime 21503466671 := by
  apply lucas_primality 21503466671 (7 : ZMod 21503466671)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21503466671 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((607 : ℕ)^1 * ((506083 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 21503466671)^10751733335 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 21503466671)^4300693334 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 21503466671)^3071923810 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 607 := Nat.prime_eq_prime_of_dvd_pow hq prime_607 hd
            subst q
            change (7 : ZMod 21503466671)^35425810 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 506083 := Nat.prime_eq_prime_of_dvd_pow hq prime_506083 hd
            subst q
            change (7 : ZMod 21503466671)^42490 ≠ 1
            reduce_mod_char
            decide

theorem prime_21777949931 : Nat.Prime 21777949931 := by
  apply lucas_primality 21777949931 (2 : ZMod 21777949931)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21777949931 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((197981363 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 21777949931)^10888974965 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 21777949931)^4355589986 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 21777949931)^1979813630 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 197981363 := Nat.prime_eq_prime_of_dvd_pow hq prime_197981363 hd
          subst q
          change (2 : ZMod 21777949931)^110 ≠ 1
          reduce_mod_char
          decide

theorem prime_21921276967 : Nat.Prime 21921276967 := by
  apply lucas_primality 21921276967 (3 : ZMod 21921276967)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21921276967 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((3653546161 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 21921276967)^10960638483 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 21921276967)^7307092322 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3653546161 := Nat.prime_eq_prime_of_dvd_pow hq prime_3653546161 hd
        subst q
        change (3 : ZMod 21921276967)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_22007035649 : Nat.Prime 22007035649 := by
  apply lucas_primality 22007035649 (3 : ZMod 22007035649)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22007035649 - 1 = (2 : ℕ)^8 * ((13 : ℕ)^1 * ((6612691 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 22007035649)^11003517824 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 22007035649)^1692848896 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 6612691 := Nat.prime_eq_prime_of_dvd_pow hq prime_6612691 hd
        subst q
        change (3 : ZMod 22007035649)^3328 ≠ 1
        reduce_mod_char
        decide

theorem prime_22164361147 : Nat.Prime 22164361147 := by
  apply lucas_primality 22164361147 (2 : ZMod 22164361147)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22164361147 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((137 : ℕ)^1 * ((8987981 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 22164361147)^11082180573 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 22164361147)^7388120382 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
          subst q
          change (2 : ZMod 22164361147)^161783658 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 8987981 := Nat.prime_eq_prime_of_dvd_pow hq prime_8987981 hd
          subst q
          change (2 : ZMod 22164361147)^2466 ≠ 1
          reduce_mod_char
          decide

theorem prime_22995659369 : Nat.Prime 22995659369 := by
  apply lucas_primality 22995659369 (3 : ZMod 22995659369)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22995659369 - 1 = (2 : ℕ)^3 * ((11 : ℕ)^1 * ((43 : ℕ)^1 * ((109 : ℕ)^1 * ((127 : ℕ)^1 * ((439 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 22995659369)^11497829684 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 22995659369)^2090514488 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (3 : ZMod 22995659369)^534782776 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
            subst q
            change (3 : ZMod 22995659369)^210969352 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
              subst q
              change (3 : ZMod 22995659369)^181068184 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 439 := Nat.prime_eq_prime_of_dvd_pow hq prime_439 hd
              subst q
              change (3 : ZMod 22995659369)^52381912 ≠ 1
              reduce_mod_char
              decide

theorem prime_23189279501 : Nat.Prime 23189279501 := by
  apply lucas_primality 23189279501 (2 : ZMod 23189279501)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23189279501 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^3 * ((269 : ℕ)^1 * ((172411 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 23189279501)^11594639750 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 23189279501)^4637855900 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
          subst q
          change (2 : ZMod 23189279501)^86205500 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 172411 := Nat.prime_eq_prime_of_dvd_pow hq prime_172411 hd
          subst q
          change (2 : ZMod 23189279501)^134500 ≠ 1
          reduce_mod_char
          decide

theorem prime_23306046611 : Nat.Prime 23306046611 := by
  apply lucas_primality 23306046611 (2 : ZMod 23306046611)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23306046611 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((30267593 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 23306046611)^11653023305 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 23306046611)^4661209322 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 23306046611)^3329435230 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (2 : ZMod 23306046611)^2118731510 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 30267593 := Nat.prime_eq_prime_of_dvd_pow hq prime_30267593 hd
            subst q
            change (2 : ZMod 23306046611)^770 ≠ 1
            reduce_mod_char
            decide

theorem prime_23504771357 : Nat.Prime 23504771357 := by
  apply lucas_primality 23504771357 (3 : ZMod 23504771357)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23504771357 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((53 : ℕ)^1 * ((10079233 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 23504771357)^11752385678 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 23504771357)^2136797396 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (3 : ZMod 23504771357)^443486252 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 10079233 := Nat.prime_eq_prime_of_dvd_pow hq prime_10079233 hd
          subst q
          change (3 : ZMod 23504771357)^2332 ≠ 1
          reduce_mod_char
          decide

theorem prime_23649132103 : Nat.Prime 23649132103 := by
  apply lucas_primality 23649132103 (3 : ZMod 23649132103)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23649132103 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((3941522017 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 23649132103)^11824566051 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 23649132103)^7883044034 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3941522017 := Nat.prime_eq_prime_of_dvd_pow hq prime_3941522017 hd
        subst q
        change (3 : ZMod 23649132103)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_23665112017 : Nat.Prime 23665112017 := by
  apply lucas_primality 23665112017 (5 : ZMod 23665112017)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23665112017 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((61 : ℕ)^1 * ((88817 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 23665112017)^11832556008 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 23665112017)^7888370672 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 23665112017)^3380730288 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (5 : ZMod 23665112017)^1820393232 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
              subst q
              change (5 : ZMod 23665112017)^387952656 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 88817 := Nat.prime_eq_prime_of_dvd_pow hq prime_88817 hd
              subst q
              change (5 : ZMod 23665112017)^266448 ≠ 1
              reduce_mod_char
              decide

theorem prime_23951806621 : Nat.Prime 23951806621 := by
  apply lucas_primality 23951806621 (6 : ZMod 23951806621)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23951806621 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^3 * ((73 : ℕ)^1 * ((107 : ℕ)^1 * ((149 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 23951806621)^11975903310 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 23951806621)^7983935540 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 23951806621)^4790361324 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (6 : ZMod 23951806621)^3421686660 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
              subst q
              change (6 : ZMod 23951806621)^328106940 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
                subst q
                change (6 : ZMod 23951806621)^223848660 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
                subst q
                change (6 : ZMod 23951806621)^160750380 ≠ 1
                reduce_mod_char
                decide

theorem prime_24624590087 : Nat.Prime 24624590087 := by
  apply lucas_primality 24624590087 (5 : ZMod 24624590087)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24624590087 - 1 = (2 : ℕ)^1 * ((4219 : ℕ)^1 * ((2918297 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 24624590087)^12312295043 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 4219 := Nat.prime_eq_prime_of_dvd_pow hq prime_4219 hd
        subst q
        change (5 : ZMod 24624590087)^5836594 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2918297 := Nat.prime_eq_prime_of_dvd_pow hq prime_2918297 hd
        subst q
        change (5 : ZMod 24624590087)^8438 ≠ 1
        reduce_mod_char
        decide

theorem prime_24794911303 : Nat.Prime 24794911303 := by
  apply lucas_primality 24794911303 (3 : ZMod 24794911303)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24794911303 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((84336433 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 24794911303)^12397455651 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 24794911303)^8264970434 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 24794911303)^3542130186 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 84336433 := Nat.prime_eq_prime_of_dvd_pow hq prime_84336433 hd
          subst q
          change (3 : ZMod 24794911303)^294 ≠ 1
          reduce_mod_char
          decide

theorem prime_24935794033 : Nat.Prime 24935794033 := by
  apply lucas_primality 24935794033 (5 : ZMod 24935794033)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24935794033 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((2833 : ℕ)^1 * ((183373 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 24935794033)^12467897016 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 24935794033)^8311931344 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2833 := Nat.prime_eq_prime_of_dvd_pow hq prime_2833 hd
          subst q
          change (5 : ZMod 24935794033)^8801904 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 183373 := Nat.prime_eq_prime_of_dvd_pow hq prime_183373 hd
          subst q
          change (5 : ZMod 24935794033)^135984 ≠ 1
          reduce_mod_char
          decide

theorem prime_25003446563 : Nat.Prime 25003446563 := by
  apply lucas_primality 25003446563 (2 : ZMod 25003446563)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 25003446563 - 1 = (2 : ℕ)^1 * ((37 : ℕ)^1 * ((109 : ℕ)^1 * ((733 : ℕ)^1 * ((4229 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 25003446563)^12501723281 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (2 : ZMod 25003446563)^675768826 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
          subst q
          change (2 : ZMod 25003446563)^229389418 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 733 := Nat.prime_eq_prime_of_dvd_pow hq prime_733 hd
            subst q
            change (2 : ZMod 25003446563)^34111114 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 4229 := Nat.prime_eq_prime_of_dvd_pow hq prime_4229 hd
            subst q
            change (2 : ZMod 25003446563)^5912378 ≠ 1
            reduce_mod_char
            decide

theorem prime_26057661803 : Nat.Prime 26057661803 := by
  apply lucas_primality 26057661803 (2 : ZMod 26057661803)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26057661803 - 1 = (2 : ℕ)^1 * ((727 : ℕ)^1 * ((17921363 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 26057661803)^13028830901 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 727 := Nat.prime_eq_prime_of_dvd_pow hq prime_727 hd
        subst q
        change (2 : ZMod 26057661803)^35842726 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 17921363 := Nat.prime_eq_prime_of_dvd_pow hq prime_17921363 hd
        subst q
        change (2 : ZMod 26057661803)^1454 ≠ 1
        reduce_mod_char
        decide

theorem prime_26353014697 : Nat.Prime 26353014697 := by
  apply lucas_primality 26353014697 (19 : ZMod 26353014697)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26353014697 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((41 : ℕ)^1 * ((881 : ℕ)^1 * ((10133 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 26353014697)^13176507348 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 26353014697)^8784338232 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (19 : ZMod 26353014697)^642756456 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 881 := Nat.prime_eq_prime_of_dvd_pow hq prime_881 hd
            subst q
            change (19 : ZMod 26353014697)^29912616 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 10133 := Nat.prime_eq_prime_of_dvd_pow hq prime_10133 hd
            subst q
            change (19 : ZMod 26353014697)^2600712 ≠ 1
            reduce_mod_char
            decide

theorem prime_26954221597 : Nat.Prime 26954221597 := by
  apply lucas_primality 26954221597 (2 : ZMod 26954221597)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26954221597 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((12721 : ℕ)^1 * ((176573 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 26954221597)^13477110798 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 26954221597)^8984740532 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 12721 := Nat.prime_eq_prime_of_dvd_pow hq prime_12721 hd
          subst q
          change (2 : ZMod 26954221597)^2118876 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 176573 := Nat.prime_eq_prime_of_dvd_pow hq prime_176573 hd
          subst q
          change (2 : ZMod 26954221597)^152652 ≠ 1
          reduce_mod_char
          decide

theorem prime_27203325397 : Nat.Prime 27203325397 := by
  apply lucas_primality 27203325397 (2 : ZMod 27203325397)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 27203325397 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((12119 : ℕ)^1 * ((14389 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 27203325397)^13601662698 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 27203325397)^9067775132 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 27203325397)^2092563492 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 12119 := Nat.prime_eq_prime_of_dvd_pow hq prime_12119 hd
            subst q
            change (2 : ZMod 27203325397)^2244684 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 14389 := Nat.prime_eq_prime_of_dvd_pow hq prime_14389 hd
            subst q
            change (2 : ZMod 27203325397)^1890564 ≠ 1
            reduce_mod_char
            decide

theorem prime_27212477713 : Nat.Prime 27212477713 := by
  apply lucas_primality 27212477713 (10 : ZMod 27212477713)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 27212477713 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((61 : ℕ)^1 * ((189671 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 27212477713)^13606238856 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 27212477713)^9070825904 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (10 : ZMod 27212477713)^3887496816 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
            subst q
            change (10 : ZMod 27212477713)^446106192 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 189671 := Nat.prime_eq_prime_of_dvd_pow hq prime_189671 hd
            subst q
            change (10 : ZMod 27212477713)^143472 ≠ 1
            reduce_mod_char
            decide

theorem prime_27394873757 : Nat.Prime 27394873757 := by
  apply lucas_primality 27394873757 (2 : ZMod 27394873757)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 27394873757 - 1 = (2 : ℕ)^2 * ((6848718439 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 27394873757)^13697436878 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 6848718439 := Nat.prime_eq_prime_of_dvd_pow hq prime_6848718439 hd
      subst q
      change (2 : ZMod 27394873757)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_27423302539 : Nat.Prime 27423302539 := by
  apply lucas_primality 27423302539 (2 : ZMod 27423302539)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 27423302539 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((29 : ℕ)^1 * ((157605187 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 27423302539)^13711651269 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 27423302539)^9141100846 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (2 : ZMod 27423302539)^945631122 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 157605187 := Nat.prime_eq_prime_of_dvd_pow hq prime_157605187 hd
          subst q
          change (2 : ZMod 27423302539)^174 ≠ 1
          reduce_mod_char
          decide

theorem prime_27680640653 : Nat.Prime 27680640653 := by
  apply lucas_primality 27680640653 (2 : ZMod 27680640653)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 27680640653 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((31 : ℕ)^1 * ((103 : ℕ)^1 * ((409 : ℕ)^1 * ((757 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 27680640653)^13840320326 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 27680640653)^3954377236 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (2 : ZMod 27680640653)^892923892 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
            subst q
            change (2 : ZMod 27680640653)^268744084 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 409 := Nat.prime_eq_prime_of_dvd_pow hq prime_409 hd
              subst q
              change (2 : ZMod 27680640653)^67678828 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 757 := Nat.prime_eq_prime_of_dvd_pow hq prime_757 hd
              subst q
              change (2 : ZMod 27680640653)^36566236 ≠ 1
              reduce_mod_char
              decide

theorem prime_28173650203 : Nat.Prime 28173650203 := by
  apply lucas_primality 28173650203 (2 : ZMod 28173650203)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 28173650203 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((47 : ℕ)^1 * ((191 : ℕ)^1 * ((19373 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 28173650203)^14086825101 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 28173650203)^9391216734 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (2 : ZMod 28173650203)^599439366 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
            subst q
            change (2 : ZMod 28173650203)^147506022 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 19373 := Nat.prime_eq_prime_of_dvd_pow hq prime_19373 hd
            subst q
            change (2 : ZMod 28173650203)^1454274 ≠ 1
            reduce_mod_char
            decide

theorem prime_28493951329 : Nat.Prime 28493951329 := by
  apply lucas_primality 28493951329 (33 : ZMod 28493951329)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 28493951329 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^2 * ((17 : ℕ)^1 * ((683 : ℕ)^1 * ((8521 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (33 : ZMod 28493951329)^14246975664 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (33 : ZMod 28493951329)^9497983776 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (33 : ZMod 28493951329)^1676114784 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 683 := Nat.prime_eq_prime_of_dvd_pow hq prime_683 hd
            subst q
            change (33 : ZMod 28493951329)^41718816 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 8521 := Nat.prime_eq_prime_of_dvd_pow hq prime_8521 hd
            subst q
            change (33 : ZMod 28493951329)^3343968 ≠ 1
            reduce_mod_char
            decide

theorem prime_29014524901 : Nat.Prime 29014524901 := by
  apply lucas_primality 29014524901 (6 : ZMod 29014524901)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 29014524901 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^2 * ((32238361 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 29014524901)^14507262450 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 29014524901)^9671508300 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 29014524901)^5802904980 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 32238361 := Nat.prime_eq_prime_of_dvd_pow hq prime_32238361 hd
          subst q
          change (6 : ZMod 29014524901)^900 ≠ 1
          reduce_mod_char
          decide

theorem prime_30027556921 : Nat.Prime 30027556921 := by
  apply lucas_primality 30027556921 (7 : ZMod 30027556921)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 30027556921 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((89 : ℕ)^1 * ((2811569 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 30027556921)^15013778460 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 30027556921)^10009185640 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 30027556921)^6005511384 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
            subst q
            change (7 : ZMod 30027556921)^337388280 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2811569 := Nat.prime_eq_prime_of_dvd_pow hq prime_2811569 hd
            subst q
            change (7 : ZMod 30027556921)^10680 ≠ 1
            reduce_mod_char
            decide

theorem prime_30237210433 : Nat.Prime 30237210433 := by
  apply lucas_primality 30237210433 (5 : ZMod 30237210433)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 30237210433 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((19 : ℕ)^1 * ((139 : ℕ)^2))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 30237210433)^15118605216 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 30237210433)^10079070144 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 30237210433)^2748837312 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (5 : ZMod 30237210433)^2325939264 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
              subst q
              change (5 : ZMod 30237210433)^1591432128 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
              subst q
              change (5 : ZMod 30237210433)^217533888 ≠ 1
              reduce_mod_char
              decide

theorem prime_30840979459 : Nat.Prime 30840979459 := by
  apply lucas_primality 30840979459 (2 : ZMod 30840979459)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 30840979459 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((283 : ℕ)^1 * ((18163121 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 30840979459)^15420489729 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 30840979459)^10280326486 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 283 := Nat.prime_eq_prime_of_dvd_pow hq prime_283 hd
          subst q
          change (2 : ZMod 30840979459)^108978726 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 18163121 := Nat.prime_eq_prime_of_dvd_pow hq prime_18163121 hd
          subst q
          change (2 : ZMod 30840979459)^1698 ≠ 1
          reduce_mod_char
          decide

theorem prime_31584065101 : Nat.Prime 31584065101 := by
  apply lucas_primality 31584065101 (10 : ZMod 31584065101)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 31584065101 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((7 : ℕ)^1 * ((239 : ℕ)^1 * ((62929 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 31584065101)^15792032550 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 31584065101)^10528021700 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 31584065101)^6316813020 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (10 : ZMod 31584065101)^4512009300 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 239 := Nat.prime_eq_prime_of_dvd_pow hq prime_239 hd
              subst q
              change (10 : ZMod 31584065101)^132150900 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 62929 := Nat.prime_eq_prime_of_dvd_pow hq prime_62929 hd
              subst q
              change (10 : ZMod 31584065101)^501900 ≠ 1
              reduce_mod_char
              decide

theorem prime_32391758101 : Nat.Prime 32391758101 := by
  apply lucas_primality 32391758101 (2 : ZMod 32391758101)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32391758101 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((13 : ℕ)^1 * ((43 : ℕ)^1 * ((193153 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 32391758101)^16195879050 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 32391758101)^10797252700 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 32391758101)^6478351620 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (2 : ZMod 32391758101)^2491673700 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
              subst q
              change (2 : ZMod 32391758101)^753296700 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 193153 := Nat.prime_eq_prime_of_dvd_pow hq prime_193153 hd
              subst q
              change (2 : ZMod 32391758101)^167700 ≠ 1
              reduce_mod_char
              decide

theorem prime_32458296817 : Nat.Prime 32458296817 := by
  apply lucas_primality 32458296817 (13 : ZMod 32458296817)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32458296817 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((41 : ℕ)^1 * ((43 : ℕ)^1 * ((59 : ℕ)^1 * ((197 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 32458296817)^16229148408 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 32458296817)^10819432272 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (13 : ZMod 32458296817)^2950754256 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (13 : ZMod 32458296817)^791665776 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
              subst q
              change (13 : ZMod 32458296817)^754844112 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
                subst q
                change (13 : ZMod 32458296817)^550140624 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
                subst q
                change (13 : ZMod 32458296817)^164762928 ≠ 1
                reduce_mod_char
                decide

theorem prime_32781821333 : Nat.Prime 32781821333 := by
  apply lucas_primality 32781821333 (2 : ZMod 32781821333)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32781821333 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((9619 : ℕ)^1 * ((65539 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 32781821333)^16390910666 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 32781821333)^2521678564 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 9619 := Nat.prime_eq_prime_of_dvd_pow hq prime_9619 hd
          subst q
          change (2 : ZMod 32781821333)^3408028 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 65539 := Nat.prime_eq_prime_of_dvd_pow hq prime_65539 hd
          subst q
          change (2 : ZMod 32781821333)^500188 ≠ 1
          reduce_mod_char
          decide

theorem prime_32789408737 : Nat.Prime 32789408737 := by
  apply lucas_primality 32789408737 (31 : ZMod 32789408737)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32789408737 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((257 : ℕ)^1 * ((189859 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (31 : ZMod 32789408737)^16394704368 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (31 : ZMod 32789408737)^10929802912 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (31 : ZMod 32789408737)^4684201248 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 257 := Nat.prime_eq_prime_of_dvd_pow hq prime_257 hd
            subst q
            change (31 : ZMod 32789408737)^127585248 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 189859 := Nat.prime_eq_prime_of_dvd_pow hq prime_189859 hd
            subst q
            change (31 : ZMod 32789408737)^172704 ≠ 1
            reduce_mod_char
            decide

theorem prime_32847075517 : Nat.Prime 32847075517 := by
  apply lucas_primality 32847075517 (2 : ZMod 32847075517)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32847075517 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((2737256293 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 32847075517)^16423537758 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 32847075517)^10949025172 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2737256293 := Nat.prime_eq_prime_of_dvd_pow hq prime_2737256293 hd
        subst q
        change (2 : ZMod 32847075517)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_33257475443 : Nat.Prime 33257475443 := by
  apply lucas_primality 33257475443 (2 : ZMod 33257475443)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 33257475443 - 1 = (2 : ℕ)^1 * ((29 : ℕ)^1 * ((673 : ℕ)^1 * ((852013 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 33257475443)^16628737721 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (2 : ZMod 33257475443)^1146809498 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 673 := Nat.prime_eq_prime_of_dvd_pow hq prime_673 hd
          subst q
          change (2 : ZMod 33257475443)^49416754 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 852013 := Nat.prime_eq_prime_of_dvd_pow hq prime_852013 hd
          subst q
          change (2 : ZMod 33257475443)^39034 ≠ 1
          reduce_mod_char
          decide

theorem prime_33986271899 : Nat.Prime 33986271899 := by
  apply lucas_primality 33986271899 (2 : ZMod 33986271899)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 33986271899 - 1 = (2 : ℕ)^1 * ((181 : ℕ)^1 * ((2953 : ℕ)^1 * ((31793 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 33986271899)^16993135949 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 181 := Nat.prime_eq_prime_of_dvd_pow hq prime_181 hd
        subst q
        change (2 : ZMod 33986271899)^187769458 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2953 := Nat.prime_eq_prime_of_dvd_pow hq prime_2953 hd
          subst q
          change (2 : ZMod 33986271899)^11509066 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 31793 := Nat.prime_eq_prime_of_dvd_pow hq prime_31793 hd
          subst q
          change (2 : ZMod 33986271899)^1068986 ≠ 1
          reduce_mod_char
          decide

theorem prime_34144654157 : Nat.Prime 34144654157 := by
  apply lucas_primality 34144654157 (2 : ZMod 34144654157)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34144654157 - 1 = (2 : ℕ)^2 * ((17 : ℕ)^1 * ((1847 : ℕ)^1 * ((271861 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 34144654157)^17072327078 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 34144654157)^2008509068 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1847 := Nat.prime_eq_prime_of_dvd_pow hq prime_1847 hd
          subst q
          change (2 : ZMod 34144654157)^18486548 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 271861 := Nat.prime_eq_prime_of_dvd_pow hq prime_271861 hd
          subst q
          change (2 : ZMod 34144654157)^125596 ≠ 1
          reduce_mod_char
          decide

theorem prime_34146868243 : Nat.Prime 34146868243 := by
  apply lucas_primality 34146868243 (2 : ZMod 34146868243)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34146868243 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((20147 : ℕ)^1 * ((282481 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 34146868243)^17073434121 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 34146868243)^11382289414 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 20147 := Nat.prime_eq_prime_of_dvd_pow hq prime_20147 hd
          subst q
          change (2 : ZMod 34146868243)^1694886 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 282481 := Nat.prime_eq_prime_of_dvd_pow hq prime_282481 hd
          subst q
          change (2 : ZMod 34146868243)^120882 ≠ 1
          reduce_mod_char
          decide

theorem prime_34166054653 : Nat.Prime 34166054653 := by
  apply lucas_primality 34166054653 (2 : ZMod 34166054653)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34166054653 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((15451 : ℕ)^1 * ((184271 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 34166054653)^17083027326 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 34166054653)^11388684884 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 15451 := Nat.prime_eq_prime_of_dvd_pow hq prime_15451 hd
          subst q
          change (2 : ZMod 34166054653)^2211252 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 184271 := Nat.prime_eq_prime_of_dvd_pow hq prime_184271 hd
          subst q
          change (2 : ZMod 34166054653)^185412 ≠ 1
          reduce_mod_char
          decide

theorem prime_34296447299 : Nat.Prime 34296447299 := by
  apply lucas_primality 34296447299 (2 : ZMod 34296447299)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34296447299 - 1 = (2 : ℕ)^1 * ((557 : ℕ)^1 * ((30786757 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 34296447299)^17148223649 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 557 := Nat.prime_eq_prime_of_dvd_pow hq prime_557 hd
        subst q
        change (2 : ZMod 34296447299)^61573514 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 30786757 := Nat.prime_eq_prime_of_dvd_pow hq prime_30786757 hd
        subst q
        change (2 : ZMod 34296447299)^1114 ≠ 1
        reduce_mod_char
        decide

theorem prime_34566329251 : Nat.Prime 34566329251 := by
  apply lucas_primality 34566329251 (2 : ZMod 34566329251)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34566329251 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^3 * ((15362813 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 34566329251)^17283164625 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 34566329251)^11522109750 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 34566329251)^6913265850 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 15362813 := Nat.prime_eq_prime_of_dvd_pow hq prime_15362813 hd
          subst q
          change (2 : ZMod 34566329251)^2250 ≠ 1
          reduce_mod_char
          decide

theorem prime_34639236479 : Nat.Prime 34639236479 := by
  apply lucas_primality 34639236479 (7 : ZMod 34639236479)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34639236479 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((224930107 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 34639236479)^17319618239 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 34639236479)^4948462354 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (7 : ZMod 34639236479)^3149021498 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 224930107 := Nat.prime_eq_prime_of_dvd_pow hq prime_224930107 hd
          subst q
          change (7 : ZMod 34639236479)^154 ≠ 1
          reduce_mod_char
          decide

theorem prime_35712851641 : Nat.Prime 35712851641 := by
  apply lucas_primality 35712851641 (7 : ZMod 35712851641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 35712851641 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((23 : ℕ)^1 * ((379 : ℕ)^1 * ((34141 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 35712851641)^17856425820 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 35712851641)^11904283880 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 35712851641)^7142570328 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (7 : ZMod 35712851641)^1552732680 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 379 := Nat.prime_eq_prime_of_dvd_pow hq prime_379 hd
              subst q
              change (7 : ZMod 35712851641)^94229160 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 34141 := Nat.prime_eq_prime_of_dvd_pow hq prime_34141 hd
              subst q
              change (7 : ZMod 35712851641)^1046040 ≠ 1
              reduce_mod_char
              decide

theorem prime_36487362811 : Nat.Prime 36487362811 := by
  apply lucas_primality 36487362811 (3 : ZMod 36487362811)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 36487362811 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((239 : ℕ)^1 * ((311 : ℕ)^1 * ((16363 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 36487362811)^18243681405 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 36487362811)^12162454270 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 36487362811)^7297472562 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 239 := Nat.prime_eq_prime_of_dvd_pow hq prime_239 hd
            subst q
            change (3 : ZMod 36487362811)^152666790 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 311 := Nat.prime_eq_prime_of_dvd_pow hq prime_311 hd
              subst q
              change (3 : ZMod 36487362811)^117322710 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 16363 := Nat.prime_eq_prime_of_dvd_pow hq prime_16363 hd
              subst q
              change (3 : ZMod 36487362811)^2229870 ≠ 1
              reduce_mod_char
              decide

theorem prime_36870867127 : Nat.Prime 36870867127 := by
  apply lucas_primality 36870867127 (3 : ZMod 36870867127)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 36870867127 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((19 : ℕ)^2 * ((367 : ℕ)^1 * ((15461 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 36870867127)^18435433563 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 36870867127)^12290289042 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (3 : ZMod 36870867127)^1940571954 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 367 := Nat.prime_eq_prime_of_dvd_pow hq prime_367 hd
            subst q
            change (3 : ZMod 36870867127)^100465578 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 15461 := Nat.prime_eq_prime_of_dvd_pow hq prime_15461 hd
            subst q
            change (3 : ZMod 36870867127)^2384766 ≠ 1
            reduce_mod_char
            decide

theorem prime_37057817743 : Nat.Prime 37057817743 := by
  apply lucas_primality 37057817743 (3 : ZMod 37057817743)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 37057817743 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((561482087 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 37057817743)^18528908871 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 37057817743)^12352605914 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 37057817743)^3368892522 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 561482087 := Nat.prime_eq_prime_of_dvd_pow hq prime_561482087 hd
          subst q
          change (3 : ZMod 37057817743)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_37879197157 : Nat.Prime 37879197157 := by
  apply lucas_primality 37879197157 (5 : ZMod 37879197157)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 37879197157 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((17 : ℕ)^1 * ((101 : ℕ)^1 * ((359 : ℕ)^1 * ((569 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 37879197157)^18939598578 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 37879197157)^12626399052 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (5 : ZMod 37879197157)^2228188068 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
            subst q
            change (5 : ZMod 37879197157)^375041556 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 359 := Nat.prime_eq_prime_of_dvd_pow hq prime_359 hd
              subst q
              change (5 : ZMod 37879197157)^105513084 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 569 := Nat.prime_eq_prime_of_dvd_pow hq prime_569 hd
              subst q
              change (5 : ZMod 37879197157)^66571524 ≠ 1
              reduce_mod_char
              decide

theorem prime_38068692611 : Nat.Prime 38068692611 := by
  apply lucas_primality 38068692611 (2 : ZMod 38068692611)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 38068692611 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((1427 : ℕ)^1 * ((205211 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 38068692611)^19034346305 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 38068692611)^7613738522 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 38068692611)^2928360970 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1427 := Nat.prime_eq_prime_of_dvd_pow hq prime_1427 hd
            subst q
            change (2 : ZMod 38068692611)^26677430 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 205211 := Nat.prime_eq_prime_of_dvd_pow hq prime_205211 hd
            subst q
            change (2 : ZMod 38068692611)^185510 ≠ 1
            reduce_mod_char
            decide

theorem prime_38535689761 : Nat.Prime 38535689761 := by
  apply lucas_primality 38535689761 (11 : ZMod 38535689761)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 38535689761 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((1061 : ℕ)^1 * ((4451 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 38535689761)^19267844880 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 38535689761)^12845229920 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 38535689761)^7707137952 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (11 : ZMod 38535689761)^2266805280 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1061 := Nat.prime_eq_prime_of_dvd_pow hq prime_1061 hd
              subst q
              change (11 : ZMod 38535689761)^36320160 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 4451 := Nat.prime_eq_prime_of_dvd_pow hq prime_4451 hd
              subst q
              change (11 : ZMod 38535689761)^8657760 ≠ 1
              reduce_mod_char
              decide

theorem prime_38736695497 : Nat.Prime 38736695497 := by
  apply lucas_primality 38736695497 (5 : ZMod 38736695497)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 38736695497 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((233 : ℕ)^1 * ((301181 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 38736695497)^19368347748 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 38736695497)^12912231832 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (5 : ZMod 38736695497)^1684204152 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
            subst q
            change (5 : ZMod 38736695497)^166251912 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 301181 := Nat.prime_eq_prime_of_dvd_pow hq prime_301181 hd
            subst q
            change (5 : ZMod 38736695497)^128616 ≠ 1
            reduce_mod_char
            decide

theorem prime_39305446393 : Nat.Prime 39305446393 := by
  apply lucas_primality 39305446393 (5 : ZMod 39305446393)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 39305446393 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((311 : ℕ)^1 * ((461 : ℕ)^1 * ((11423 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 39305446393)^19652723196 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 39305446393)^13101815464 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 311 := Nat.prime_eq_prime_of_dvd_pow hq prime_311 hd
          subst q
          change (5 : ZMod 39305446393)^126384072 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 461 := Nat.prime_eq_prime_of_dvd_pow hq prime_461 hd
            subst q
            change (5 : ZMod 39305446393)^85261272 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 11423 := Nat.prime_eq_prime_of_dvd_pow hq prime_11423 hd
            subst q
            change (5 : ZMod 39305446393)^3440904 ≠ 1
            reduce_mod_char
            decide

theorem prime_39406011353 : Nat.Prime 39406011353 := by
  apply lucas_primality 39406011353 (3 : ZMod 39406011353)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 39406011353 - 1 = (2 : ℕ)^3 * ((311 : ℕ)^1 * ((15838429 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 39406011353)^19703005676 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 311 := Nat.prime_eq_prime_of_dvd_pow hq prime_311 hd
        subst q
        change (3 : ZMod 39406011353)^126707432 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 15838429 := Nat.prime_eq_prime_of_dvd_pow hq prime_15838429 hd
        subst q
        change (3 : ZMod 39406011353)^2488 ≠ 1
        reduce_mod_char
        decide

theorem prime_39461932063 : Nat.Prime 39461932063 := by
  apply lucas_primality 39461932063 (3 : ZMod 39461932063)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 39461932063 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((29 : ℕ)^1 * ((103 : ℕ)^1 * ((104851 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 39461932063)^19730966031 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 39461932063)^13153977354 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 39461932063)^5637418866 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (3 : ZMod 39461932063)^1360756278 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
              subst q
              change (3 : ZMod 39461932063)^383125554 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 104851 := Nat.prime_eq_prime_of_dvd_pow hq prime_104851 hd
              subst q
              change (3 : ZMod 39461932063)^376362 ≠ 1
              reduce_mod_char
              decide

theorem prime_39923436673 : Nat.Prime 39923436673 := by
  apply lucas_primality 39923436673 (5 : ZMod 39923436673)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 39923436673 - 1 = (2 : ℕ)^7 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((149 : ℕ)^2 * ((223 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 39923436673)^19961718336 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 39923436673)^13307812224 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 39923436673)^5703348096 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
            subst q
            change (5 : ZMod 39923436673)^267942528 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 223 := Nat.prime_eq_prime_of_dvd_pow hq prime_223 hd
            subst q
            change (5 : ZMod 39923436673)^179028864 ≠ 1
            reduce_mod_char
            decide

theorem prime_40885073209 : Nat.Prime 40885073209 := by
  apply lucas_primality 40885073209 (11 : ZMod 40885073209)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 40885073209 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((43 : ℕ)^2 * ((73 : ℕ)^1 * ((601 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 40885073209)^20442536604 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 40885073209)^13628357736 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (11 : ZMod 40885073209)^5840724744 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (11 : ZMod 40885073209)^950815656 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
              subst q
              change (11 : ZMod 40885073209)^560069496 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 601 := Nat.prime_eq_prime_of_dvd_pow hq prime_601 hd
              subst q
              change (11 : ZMod 40885073209)^68028408 ≠ 1
              reduce_mod_char
              decide

theorem prime_41360163349 : Nat.Prime 41360163349 := by
  apply lucas_primality 41360163349 (2 : ZMod 41360163349)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 41360163349 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((139 : ℕ)^1 * ((3542323 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 41360163349)^20680081674 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 41360163349)^13786721116 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 41360163349)^5908594764 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
            subst q
            change (2 : ZMod 41360163349)^297555132 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3542323 := Nat.prime_eq_prime_of_dvd_pow hq prime_3542323 hd
            subst q
            change (2 : ZMod 41360163349)^11676 ≠ 1
            reduce_mod_char
            decide

theorem prime_41361447599 : Nat.Prime 41361447599 := by
  apply lucas_primality 41361447599 (17 : ZMod 41361447599)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 41361447599 - 1 = (2 : ℕ)^1 * ((61 : ℕ)^1 * ((109 : ℕ)^1 * ((211 : ℕ)^1 * ((14741 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 41361447599)^20680723799 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
        subst q
        change (17 : ZMod 41361447599)^678056518 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
          subst q
          change (17 : ZMod 41361447599)^379462822 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 211 := Nat.prime_eq_prime_of_dvd_pow hq prime_211 hd
            subst q
            change (17 : ZMod 41361447599)^196025818 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 14741 := Nat.prime_eq_prime_of_dvd_pow hq prime_14741 hd
            subst q
            change (17 : ZMod 41361447599)^2805878 ≠ 1
            reduce_mod_char
            decide

theorem prime_42180533663 : Nat.Prime 42180533663 := by
  apply lucas_primality 42180533663 (5 : ZMod 42180533663)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 42180533663 - 1 = (2 : ℕ)^1 * ((21090266831 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 42180533663)^21090266831 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 21090266831 := Nat.prime_eq_prime_of_dvd_pow hq prime_21090266831 hd
      subst q
      change (5 : ZMod 42180533663)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_42701498641 : Nat.Prime 42701498641 := by
  apply lucas_primality 42701498641 (29 : ZMod 42701498641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 42701498641 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((1171 : ℕ)^1 * ((50647 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (29 : ZMod 42701498641)^21350749320 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (29 : ZMod 42701498641)^14233832880 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (29 : ZMod 42701498641)^8540299728 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1171 := Nat.prime_eq_prime_of_dvd_pow hq prime_1171 hd
            subst q
            change (29 : ZMod 42701498641)^36465840 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 50647 := Nat.prime_eq_prime_of_dvd_pow hq prime_50647 hd
            subst q
            change (29 : ZMod 42701498641)^843120 ≠ 1
            reduce_mod_char
            decide

theorem prime_44709559663 : Nat.Prime 44709559663 := by
  apply lucas_primality 44709559663 (5 : ZMod 44709559663)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 44709559663 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((311 : ℕ)^1 * ((23960107 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 44709559663)^22354779831 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 44709559663)^14903186554 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 311 := Nat.prime_eq_prime_of_dvd_pow hq prime_311 hd
          subst q
          change (5 : ZMod 44709559663)^143760642 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 23960107 := Nat.prime_eq_prime_of_dvd_pow hq prime_23960107 hd
          subst q
          change (5 : ZMod 44709559663)^1866 ≠ 1
          reduce_mod_char
          decide

theorem prime_45631187443 : Nat.Prime 45631187443 := by
  apply lucas_primality 45631187443 (2 : ZMod 45631187443)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 45631187443 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((157 : ℕ)^1 * ((16146917 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 45631187443)^22815593721 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 45631187443)^15210395814 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
          subst q
          change (2 : ZMod 45631187443)^290644506 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 16146917 := Nat.prime_eq_prime_of_dvd_pow hq prime_16146917 hd
          subst q
          change (2 : ZMod 45631187443)^2826 ≠ 1
          reduce_mod_char
          decide

theorem prime_46009408321 : Nat.Prime 46009408321 := by
  apply lucas_primality 46009408321 (11 : ZMod 46009408321)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 46009408321 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((43 : ℕ)^1 * ((59 : ℕ)^1 * ((2099 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 46009408321)^23004704160 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 46009408321)^15336469440 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 46009408321)^9201881664 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (11 : ZMod 46009408321)^1069986240 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
              subst q
              change (11 : ZMod 46009408321)^779820480 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 2099 := Nat.prime_eq_prime_of_dvd_pow hq prime_2099 hd
              subst q
              change (11 : ZMod 46009408321)^21919680 ≠ 1
              reduce_mod_char
              decide

theorem prime_46082949977 : Nat.Prime 46082949977 := by
  apply lucas_primality 46082949977 (5 : ZMod 46082949977)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 46082949977 - 1 = (2 : ℕ)^3 * ((7 : ℕ)^1 * ((1301 : ℕ)^1 * ((632521 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 46082949977)^23041474988 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 46082949977)^6583278568 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1301 := Nat.prime_eq_prime_of_dvd_pow hq prime_1301 hd
          subst q
          change (5 : ZMod 46082949977)^35421176 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 632521 := Nat.prime_eq_prime_of_dvd_pow hq prime_632521 hd
          subst q
          change (5 : ZMod 46082949977)^72856 ≠ 1
          reduce_mod_char
          decide

theorem prime_46103592919 : Nat.Prime 46103592919 := by
  apply lucas_primality 46103592919 (3 : ZMod 46103592919)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 46103592919 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((451996009 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 46103592919)^23051796459 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 46103592919)^15367864306 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (3 : ZMod 46103592919)^2711976054 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 451996009 := Nat.prime_eq_prime_of_dvd_pow hq prime_451996009 hd
          subst q
          change (3 : ZMod 46103592919)^102 ≠ 1
          reduce_mod_char
          decide

theorem prime_46150329857 : Nat.Prime 46150329857 := by
  apply lucas_primality 46150329857 (3 : ZMod 46150329857)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 46150329857 - 1 = (2 : ℕ)^9 * ((251 : ℕ)^1 * ((421 : ℕ)^1 * ((853 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 46150329857)^23075164928 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 251 := Nat.prime_eq_prime_of_dvd_pow hq prime_251 hd
        subst q
        change (3 : ZMod 46150329857)^183865856 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 421 := Nat.prime_eq_prime_of_dvd_pow hq prime_421 hd
          subst q
          change (3 : ZMod 46150329857)^109620736 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 853 := Nat.prime_eq_prime_of_dvd_pow hq prime_853 hd
          subst q
          change (3 : ZMod 46150329857)^54103552 ≠ 1
          reduce_mod_char
          decide

theorem prime_46303617623 : Nat.Prime 46303617623 := by
  apply lucas_primality 46303617623 (5 : ZMod 46303617623)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 46303617623 - 1 = (2 : ℕ)^1 * ((541 : ℕ)^1 * ((42794471 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 46303617623)^23151808811 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 541 := Nat.prime_eq_prime_of_dvd_pow hq prime_541 hd
        subst q
        change (5 : ZMod 46303617623)^85588942 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 42794471 := Nat.prime_eq_prime_of_dvd_pow hq prime_42794471 hd
        subst q
        change (5 : ZMod 46303617623)^1082 ≠ 1
        reduce_mod_char
        decide

theorem prime_46656000007 : Nat.Prime 46656000007 := by
  apply lucas_primality 46656000007 (11 : ZMod 46656000007)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 46656000007 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((83 : ℕ)^1 * ((1216711 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 46656000007)^23328000003 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 46656000007)^15552000002 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (11 : ZMod 46656000007)^6665142858 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (11 : ZMod 46656000007)^4241454546 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
              subst q
              change (11 : ZMod 46656000007)^562120482 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1216711 := Nat.prime_eq_prime_of_dvd_pow hq prime_1216711 hd
              subst q
              change (11 : ZMod 46656000007)^38346 ≠ 1
              reduce_mod_char
              decide

theorem prime_48242066783 : Nat.Prime 48242066783 := by
  apply lucas_primality 48242066783 (7 : ZMod 48242066783)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 48242066783 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((265066301 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 48242066783)^24121033391 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 48242066783)^6891723826 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (7 : ZMod 48242066783)^3710928214 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 265066301 := Nat.prime_eq_prime_of_dvd_pow hq prime_265066301 hd
          subst q
          change (7 : ZMod 48242066783)^182 ≠ 1
          reduce_mod_char
          decide

theorem prime_48250915939 : Nat.Prime 48250915939 := by
  apply lucas_primality 48250915939 (2 : ZMod 48250915939)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 48250915939 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((433 : ℕ)^1 * ((991 : ℕ)^1 * ((6247 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 48250915939)^24125457969 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 48250915939)^16083638646 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 433 := Nat.prime_eq_prime_of_dvd_pow hq prime_433 hd
          subst q
          change (2 : ZMod 48250915939)^111433986 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 991 := Nat.prime_eq_prime_of_dvd_pow hq prime_991 hd
            subst q
            change (2 : ZMod 48250915939)^48689118 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 6247 := Nat.prime_eq_prime_of_dvd_pow hq prime_6247 hd
            subst q
            change (2 : ZMod 48250915939)^7723854 ≠ 1
            reduce_mod_char
            decide

theorem prime_49105126333 : Nat.Prime 49105126333 := by
  apply lucas_primality 49105126333 (6 : ZMod 49105126333)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 49105126333 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((1364031287 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 49105126333)^24552563166 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 49105126333)^16368375444 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1364031287 := Nat.prime_eq_prime_of_dvd_pow hq prime_1364031287 hd
        subst q
        change (6 : ZMod 49105126333)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_51520374383 : Nat.Prime 51520374383 := by
  apply lucas_primality 51520374383 (5 : ZMod 51520374383)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 51520374383 - 1 = (2 : ℕ)^1 * ((107 : ℕ)^1 * ((461 : ℕ)^1 * ((522233 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 51520374383)^25760187191 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
        subst q
        change (5 : ZMod 51520374383)^481498826 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 461 := Nat.prime_eq_prime_of_dvd_pow hq prime_461 hd
          subst q
          change (5 : ZMod 51520374383)^111757862 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 522233 := Nat.prime_eq_prime_of_dvd_pow hq prime_522233 hd
          subst q
          change (5 : ZMod 51520374383)^98654 ≠ 1
          reduce_mod_char
          decide

theorem prime_51567024869 : Nat.Prime 51567024869 := by
  apply lucas_primality 51567024869 (2 : ZMod 51567024869)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 51567024869 - 1 = (2 : ℕ)^2 * ((17 : ℕ)^3 * ((709 : ℕ)^1 * ((3701 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 51567024869)^25783512434 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 51567024869)^3033354404 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 709 := Nat.prime_eq_prime_of_dvd_pow hq prime_709 hd
          subst q
          change (2 : ZMod 51567024869)^72732052 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3701 := Nat.prime_eq_prime_of_dvd_pow hq prime_3701 hd
          subst q
          change (2 : ZMod 51567024869)^13933268 ≠ 1
          reduce_mod_char
          decide

theorem prime_52292336069 : Nat.Prime 52292336069 := by
  apply lucas_primality 52292336069 (2 : ZMod 52292336069)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 52292336069 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^2 * ((113 : ℕ)^1 * ((2361041 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 52292336069)^26146168034 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 52292336069)^7470333724 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
          subst q
          change (2 : ZMod 52292336069)^462764036 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2361041 := Nat.prime_eq_prime_of_dvd_pow hq prime_2361041 hd
          subst q
          change (2 : ZMod 52292336069)^22148 ≠ 1
          reduce_mod_char
          decide

theorem prime_52445056723 : Nat.Prime 52445056723 := by
  apply lucas_primality 52445056723 (11 : ZMod 52445056723)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 52445056723 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((8740842787 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 52445056723)^26222528361 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 52445056723)^17481685574 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 8740842787 := Nat.prime_eq_prime_of_dvd_pow hq prime_8740842787 hd
        subst q
        change (11 : ZMod 52445056723)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_52593983341 : Nat.Prime 52593983341 := by
  apply lucas_primality 52593983341 (2 : ZMod 52593983341)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 52593983341 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((876566389 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 52593983341)^26296991670 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 52593983341)^17531327780 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 52593983341)^10518796668 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 876566389 := Nat.prime_eq_prime_of_dvd_pow hq prime_876566389 hd
          subst q
          change (2 : ZMod 52593983341)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_52627149649 : Nat.Prime 52627149649 := by
  apply lucas_primality 52627149649 (11 : ZMod 52627149649)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 52627149649 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((1217 : ℕ)^1 * ((300301 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 52627149649)^26313574824 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 52627149649)^17542383216 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1217 := Nat.prime_eq_prime_of_dvd_pow hq prime_1217 hd
          subst q
          change (11 : ZMod 52627149649)^43243344 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 300301 := Nat.prime_eq_prime_of_dvd_pow hq prime_300301 hd
          subst q
          change (11 : ZMod 52627149649)^175248 ≠ 1
          reduce_mod_char
          decide

theorem prime_53682083753 : Nat.Prime 53682083753 := by
  apply lucas_primality 53682083753 (3 : ZMod 53682083753)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 53682083753 - 1 = (2 : ℕ)^3 * ((11 : ℕ)^1 * ((7703 : ℕ)^1 * ((79193 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 53682083753)^26841041876 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 53682083753)^4880189432 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7703 := Nat.prime_eq_prime_of_dvd_pow hq prime_7703 hd
          subst q
          change (3 : ZMod 53682083753)^6968984 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 79193 := Nat.prime_eq_prime_of_dvd_pow hq prime_79193 hd
          subst q
          change (3 : ZMod 53682083753)^677864 ≠ 1
          reduce_mod_char
          decide

theorem prime_56047701089 : Nat.Prime 56047701089 := by
  apply lucas_primality 56047701089 (3 : ZMod 56047701089)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 56047701089 - 1 = (2 : ℕ)^5 * ((2971 : ℕ)^1 * ((589529 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 56047701089)^28023850544 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 2971 := Nat.prime_eq_prime_of_dvd_pow hq prime_2971 hd
        subst q
        change (3 : ZMod 56047701089)^18864928 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 589529 := Nat.prime_eq_prime_of_dvd_pow hq prime_589529 hd
        subst q
        change (3 : ZMod 56047701089)^95072 ≠ 1
        reduce_mod_char
        decide

theorem prime_56405020153 : Nat.Prime 56405020153 := by
  apply lucas_primality 56405020153 (5 : ZMod 56405020153)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 56405020153 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((2579 : ℕ)^1 * ((70099 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 56405020153)^28202510076 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 56405020153)^18801673384 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (5 : ZMod 56405020153)^4338847704 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2579 := Nat.prime_eq_prime_of_dvd_pow hq prime_2579 hd
            subst q
            change (5 : ZMod 56405020153)^21870888 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 70099 := Nat.prime_eq_prime_of_dvd_pow hq prime_70099 hd
            subst q
            change (5 : ZMod 56405020153)^804648 ≠ 1
            reduce_mod_char
            decide

theorem prime_56800235633 : Nat.Prime 56800235633 := by
  apply lucas_primality 56800235633 (5 : ZMod 56800235633)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 56800235633 - 1 = (2 : ℕ)^4 * ((7 : ℕ)^1 * ((507144961 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 56800235633)^28400117816 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 56800235633)^8114319376 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 507144961 := Nat.prime_eq_prime_of_dvd_pow hq prime_507144961 hd
        subst q
        change (5 : ZMod 56800235633)^112 ≠ 1
        reduce_mod_char
        decide

theorem prime_57485995321 : Nat.Prime 57485995321 := by
  apply lucas_primality 57485995321 (11 : ZMod 57485995321)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 57485995321 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((3391 : ℕ)^1 * ((10867 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 57485995321)^28742997660 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 57485995321)^19161998440 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 57485995321)^11497199064 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (11 : ZMod 57485995321)^4421999640 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 3391 := Nat.prime_eq_prime_of_dvd_pow hq prime_3391 hd
              subst q
              change (11 : ZMod 57485995321)^16952520 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 10867 := Nat.prime_eq_prime_of_dvd_pow hq prime_10867 hd
              subst q
              change (11 : ZMod 57485995321)^5289960 ≠ 1
              reduce_mod_char
              decide

theorem prime_57924299243 : Nat.Prime 57924299243 := by
  apply lucas_primality 57924299243 (2 : ZMod 57924299243)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 57924299243 - 1 = (2 : ℕ)^1 * ((31 : ℕ)^1 * ((3467 : ℕ)^1 * ((269473 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 57924299243)^28962149621 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (2 : ZMod 57924299243)^1868525782 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 3467 := Nat.prime_eq_prime_of_dvd_pow hq prime_3467 hd
          subst q
          change (2 : ZMod 57924299243)^16707326 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 269473 := Nat.prime_eq_prime_of_dvd_pow hq prime_269473 hd
          subst q
          change (2 : ZMod 57924299243)^214954 ≠ 1
          reduce_mod_char
          decide

theorem prime_58373516807 : Nat.Prime 58373516807 := by
  apply lucas_primality 58373516807 (5 : ZMod 58373516807)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 58373516807 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((1213 : ℕ)^1 * ((2187421 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 58373516807)^29186758403 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 58373516807)^5306683346 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1213 := Nat.prime_eq_prime_of_dvd_pow hq prime_1213 hd
          subst q
          change (5 : ZMod 58373516807)^48123262 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2187421 := Nat.prime_eq_prime_of_dvd_pow hq prime_2187421 hd
          subst q
          change (5 : ZMod 58373516807)^26686 ≠ 1
          reduce_mod_char
          decide

end LegendreK6.Pratt
