import LegendreK6.Pratt.Block019

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LegendreK6.Pratt

theorem prime_11390625000023 : Nat.Prime 11390625000023 := by
  apply lucas_primality 11390625000023 (5 : ZMod 11390625000023)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11390625000023 - 1 = (2 : ℕ)^1 * ((5695312500011 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 11390625000023)^5695312500011 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 5695312500011 := Nat.prime_eq_prime_of_dvd_pow hq prime_5695312500011 hd
      subst q
      change (5 : ZMod 11390625000023)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_11470093094431 : Nat.Prime 11470093094431 := by
  apply lucas_primality 11470093094431 (3 : ZMod 11470093094431)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11470093094431 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((127445478827 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 11470093094431)^5735046547215 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 11470093094431)^3823364364810 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 11470093094431)^2294018618886 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 127445478827 := Nat.prime_eq_prime_of_dvd_pow hq prime_127445478827 hd
          subst q
          change (3 : ZMod 11470093094431)^90 ≠ 1
          reduce_mod_char
          decide

theorem prime_11693569402573 : Nat.Prime 11693569402573 := by
  apply lucas_primality 11693569402573 (5 : ZMod 11693569402573)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11693569402573 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((31 : ℕ)^1 * ((21649 : ℕ)^1 * ((76421 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 11693569402573)^5846784701286 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 11693569402573)^3897856467524 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (5 : ZMod 11693569402573)^615451021188 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (5 : ZMod 11693569402573)^377211916212 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 21649 := Nat.prime_eq_prime_of_dvd_pow hq prime_21649 hd
              subst q
              change (5 : ZMod 11693569402573)^540143628 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 76421 := Nat.prime_eq_prime_of_dvd_pow hq prime_76421 hd
              subst q
              change (5 : ZMod 11693569402573)^153015132 ≠ 1
              reduce_mod_char
              decide

theorem prime_11853911588417 : Nat.Prime 11853911588417 := by
  apply lucas_primality 11853911588417 (3 : ZMod 11853911588417)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11853911588417 - 1 = (2 : ℕ)^6 * ((185217368569 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 11853911588417)^5926955794208 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 185217368569 := Nat.prime_eq_prime_of_dvd_pow hq prime_185217368569 hd
      subst q
      change (3 : ZMod 11853911588417)^64 ≠ 1
      reduce_mod_char
      decide

theorem prime_12064711140953 : Nat.Prime 12064711140953 := by
  apply lucas_primality 12064711140953 (3 : ZMod 12064711140953)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12064711140953 - 1 = (2 : ℕ)^3 * ((1508088892619 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 12064711140953)^6032355570476 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 1508088892619 := Nat.prime_eq_prime_of_dvd_pow hq prime_1508088892619 hd
      subst q
      change (3 : ZMod 12064711140953)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_12332795428901 : Nat.Prime 12332795428901 := by
  apply lucas_primality 12332795428901 (2 : ZMod 12332795428901)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12332795428901 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((421 : ℕ)^1 * ((292940509 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 12332795428901)^6166397714450 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 12332795428901)^2466559085780 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 421 := Nat.prime_eq_prime_of_dvd_pow hq prime_421 hd
          subst q
          change (2 : ZMod 12332795428901)^29294050900 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 292940509 := Nat.prime_eq_prime_of_dvd_pow hq prime_292940509 hd
          subst q
          change (2 : ZMod 12332795428901)^42100 ≠ 1
          reduce_mod_char
          decide

theorem prime_12497030435353 : Nat.Prime 12497030435353 := by
  apply lucas_primality 12497030435353 (10 : ZMod 12497030435353)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12497030435353 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((179 : ℕ)^2 * ((241 : ℕ)^1 * ((67433 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 12497030435353)^6248515217676 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 12497030435353)^4165676811784 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 179 := Nat.prime_eq_prime_of_dvd_pow hq prime_179 hd
          subst q
          change (10 : ZMod 12497030435353)^69815812488 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 241 := Nat.prime_eq_prime_of_dvd_pow hq prime_241 hd
            subst q
            change (10 : ZMod 12497030435353)^51854898072 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 67433 := Nat.prime_eq_prime_of_dvd_pow hq prime_67433 hd
            subst q
            change (10 : ZMod 12497030435353)^185325144 ≠ 1
            reduce_mod_char
            decide

theorem prime_12717698628641 : Nat.Prime 12717698628641 := by
  apply lucas_primality 12717698628641 (3 : ZMod 12717698628641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12717698628641 - 1 = (2 : ℕ)^5 * ((5 : ℕ)^1 * ((79485616429 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 12717698628641)^6358849314320 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 12717698628641)^2543539725728 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 79485616429 := Nat.prime_eq_prime_of_dvd_pow hq prime_79485616429 hd
        subst q
        change (3 : ZMod 12717698628641)^160 ≠ 1
        reduce_mod_char
        decide

theorem prime_12827693806987 : Nat.Prime 12827693806987 := by
  apply lucas_primality 12827693806987 (3 : ZMod 12827693806987)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12827693806987 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5501 : ℕ)^1 * ((10837 : ℕ)^1 * ((35863 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 12827693806987)^6413846903493 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 12827693806987)^4275897935662 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5501 := Nat.prime_eq_prime_of_dvd_pow hq prime_5501 hd
          subst q
          change (3 : ZMod 12827693806987)^2331883986 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 10837 := Nat.prime_eq_prime_of_dvd_pow hq prime_10837 hd
            subst q
            change (3 : ZMod 12827693806987)^1183694178 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 35863 := Nat.prime_eq_prime_of_dvd_pow hq prime_35863 hd
            subst q
            change (3 : ZMod 12827693806987)^357686022 ≠ 1
            reduce_mod_char
            decide

theorem prime_13339032325711 : Nat.Prime 13339032325711 := by
  apply lucas_primality 13339032325711 (3 : ZMod 13339032325711)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13339032325711 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((4886092427 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 13339032325711)^6669516162855 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 13339032325711)^4446344108570 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 13339032325711)^2667806465142 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (3 : ZMod 13339032325711)^1905576046530 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
              subst q
              change (3 : ZMod 13339032325711)^1026079409670 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 4886092427 := Nat.prime_eq_prime_of_dvd_pow hq prime_4886092427 hd
              subst q
              change (3 : ZMod 13339032325711)^2730 ≠ 1
              reduce_mod_char
              decide

theorem prime_13404376666049 : Nat.Prime 13404376666049 := by
  apply lucas_primality 13404376666049 (3 : ZMod 13404376666049)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13404376666049 - 1 = (2 : ℕ)^6 * ((34981 : ℕ)^1 * ((5987347 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 13404376666049)^6702188333024 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 34981 := Nat.prime_eq_prime_of_dvd_pow hq prime_34981 hd
        subst q
        change (3 : ZMod 13404376666049)^383190208 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5987347 := Nat.prime_eq_prime_of_dvd_pow hq prime_5987347 hd
        subst q
        change (3 : ZMod 13404376666049)^2238784 ≠ 1
        reduce_mod_char
        decide

theorem prime_13728901620463 : Nat.Prime 13728901620463 := by
  apply lucas_primality 13728901620463 (5 : ZMod 13728901620463)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13728901620463 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((19 : ℕ)^1 * ((269 : ℕ)^1 * ((4651 : ℕ)^1 * ((13751 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 13728901620463)^6864450810231 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 13728901620463)^4576300540154 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 13728901620463)^1961271660066 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (5 : ZMod 13728901620463)^722573769498 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
              subst q
              change (5 : ZMod 13728901620463)^51036808998 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 4651 := Nat.prime_eq_prime_of_dvd_pow hq prime_4651 hd
                subst q
                change (5 : ZMod 13728901620463)^2951817162 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 13751 := Nat.prime_eq_prime_of_dvd_pow hq prime_13751 hd
                subst q
                change (5 : ZMod 13728901620463)^998392962 ≠ 1
                reduce_mod_char
                decide

theorem prime_13867245015641 : Nat.Prime 13867245015641 := by
  apply lucas_primality 13867245015641 (3 : ZMod 13867245015641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13867245015641 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((347 : ℕ)^1 * ((999081053 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 13867245015641)^6933622507820 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 13867245015641)^2773449003128 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 347 := Nat.prime_eq_prime_of_dvd_pow hq prime_347 hd
          subst q
          change (3 : ZMod 13867245015641)^39963242120 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 999081053 := Nat.prime_eq_prime_of_dvd_pow hq prime_999081053 hd
          subst q
          change (3 : ZMod 13867245015641)^13880 ≠ 1
          reduce_mod_char
          decide

theorem prime_13949455930411 : Nat.Prime 13949455930411 := by
  apply lucas_primality 13949455930411 (10 : ZMod 13949455930411)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13949455930411 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^2 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((43 : ℕ)^1 * ((167 : ℕ)^1 * ((9241 : ℕ)^1)))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 13949455930411)^6974727965205 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 13949455930411)^4649818643470 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 13949455930411)^2789891186082 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (10 : ZMod 13949455930411)^1992779418630 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
              subst q
              change (10 : ZMod 13949455930411)^1268132357310 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
                subst q
                change (10 : ZMod 13949455930411)^1073035071570 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
                  subst q
                  change (10 : ZMod 13949455930411)^324405951870 ≠ 1
                  reduce_mod_char
                  decide
                · rcases hq.dvd_mul.mp hd with hd | hd
                  · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
                    subst q
                    change (10 : ZMod 13949455930411)^83529676230 ≠ 1
                    reduce_mod_char
                    decide
                  · have heq : q = 9241 := Nat.prime_eq_prime_of_dvd_pow hq prime_9241 hd
                    subst q
                    change (10 : ZMod 13949455930411)^1509518010 ≠ 1
                    reduce_mod_char
                    decide

theorem prime_14412774445063 : Nat.Prime 14412774445063 := by
  apply lucas_primality 14412774445063 (3 : ZMod 14412774445063)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14412774445063 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((3361 : ℕ)^1 * ((102100951 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 14412774445063)^7206387222531 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 14412774445063)^4804258148354 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 14412774445063)^2058967777866 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3361 := Nat.prime_eq_prime_of_dvd_pow hq prime_3361 hd
            subst q
            change (3 : ZMod 14412774445063)^4288239942 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 102100951 := Nat.prime_eq_prime_of_dvd_pow hq prime_102100951 hd
            subst q
            change (3 : ZMod 14412774445063)^141162 ≠ 1
            reduce_mod_char
            decide

theorem prime_14976071831459 : Nat.Prime 14976071831459 := by
  apply lucas_primality 14976071831459 (2 : ZMod 14976071831459)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14976071831459 - 1 = (2 : ℕ)^1 * ((193 : ℕ)^1 * ((52697 : ℕ)^1 * ((736249 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 14976071831459)^7488035915729 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
        subst q
        change (2 : ZMod 14976071831459)^77596227106 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 52697 := Nat.prime_eq_prime_of_dvd_pow hq prime_52697 hd
          subst q
          change (2 : ZMod 14976071831459)^284192114 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 736249 := Nat.prime_eq_prime_of_dvd_pow hq prime_736249 hd
          subst q
          change (2 : ZMod 14976071831459)^20341042 ≠ 1
          reduce_mod_char
          decide

theorem prime_15282574760039 : Nat.Prime 15282574760039 := by
  apply lucas_primality 15282574760039 (13 : ZMod 15282574760039)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15282574760039 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((115019 : ℕ)^1 * ((3496579 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 15282574760039)^7641287380019 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (13 : ZMod 15282574760039)^804346040002 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 115019 := Nat.prime_eq_prime_of_dvd_pow hq prime_115019 hd
          subst q
          change (13 : ZMod 15282574760039)^132870002 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3496579 := Nat.prime_eq_prime_of_dvd_pow hq prime_3496579 hd
          subst q
          change (13 : ZMod 15282574760039)^4370722 ≠ 1
          reduce_mod_char
          decide

theorem prime_15557597153369 : Nat.Prime 15557597153369 := by
  apply lucas_primality 15557597153369 (3 : ZMod 15557597153369)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15557597153369 - 1 = (2 : ℕ)^3 * ((1488869 : ℕ)^1 * ((1306159 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 15557597153369)^7778798576684 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1488869 := Nat.prime_eq_prime_of_dvd_pow hq prime_1488869 hd
        subst q
        change (3 : ZMod 15557597153369)^10449272 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1306159 := Nat.prime_eq_prime_of_dvd_pow hq prime_1306159 hd
        subst q
        change (3 : ZMod 15557597153369)^11910952 ≠ 1
        reduce_mod_char
        decide

theorem prime_16000572653959 : Nat.Prime 16000572653959 := by
  apply lucas_primality 16000572653959 (3 : ZMod 16000572653959)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16000572653959 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((353 : ℕ)^1 * ((7554566881 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 16000572653959)^8000286326979 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 16000572653959)^5333524217986 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 353 := Nat.prime_eq_prime_of_dvd_pow hq prime_353 hd
          subst q
          change (3 : ZMod 16000572653959)^45327401286 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7554566881 := Nat.prime_eq_prime_of_dvd_pow hq prime_7554566881 hd
          subst q
          change (3 : ZMod 16000572653959)^2118 ≠ 1
          reduce_mod_char
          decide

theorem prime_16157819263073 : Nat.Prime 16157819263073 := by
  apply lucas_primality 16157819263073 (3 : ZMod 16157819263073)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16157819263073 - 1 = (2 : ℕ)^5 * ((47 : ℕ)^1 * ((10743230893 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 16157819263073)^8078909631536 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (3 : ZMod 16157819263073)^343783388576 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 10743230893 := Nat.prime_eq_prime_of_dvd_pow hq prime_10743230893 hd
        subst q
        change (3 : ZMod 16157819263073)^1504 ≠ 1
        reduce_mod_char
        decide

theorem prime_16447056722471 : Nat.Prime 16447056722471 := by
  apply lucas_primality 16447056722471 (7 : ZMod 16447056722471)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16447056722471 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((26683 : ℕ)^1 * ((5603519 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 16447056722471)^8223528361235 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 16447056722471)^3289411344494 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (7 : ZMod 16447056722471)^1495186974770 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 26683 := Nat.prime_eq_prime_of_dvd_pow hq prime_26683 hd
            subst q
            change (7 : ZMod 16447056722471)^616387090 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 5603519 := Nat.prime_eq_prime_of_dvd_pow hq prime_5603519 hd
            subst q
            change (7 : ZMod 16447056722471)^2935130 ≠ 1
            reduce_mod_char
            decide

theorem prime_16527208835329 : Nat.Prime 16527208835329 := by
  apply lucas_primality 16527208835329 (7 : ZMod 16527208835329)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16527208835329 - 1 = (2 : ℕ)^8 * ((3 : ℕ)^1 * ((83 : ℕ)^1 * ((9241 : ℕ)^1 * ((28057 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 16527208835329)^8263604417664 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 16527208835329)^5509069611776 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
          subst q
          change (7 : ZMod 16527208835329)^199122998016 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 9241 := Nat.prime_eq_prime_of_dvd_pow hq prime_9241 hd
            subst q
            change (7 : ZMod 16527208835329)^1788465408 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 28057 := Nat.prime_eq_prime_of_dvd_pow hq prime_28057 hd
            subst q
            change (7 : ZMod 16527208835329)^589058304 ≠ 1
            reduce_mod_char
            decide

theorem prime_16542056794189 : Nat.Prime 16542056794189 := by
  apply lucas_primality 16542056794189 (2 : ZMod 16542056794189)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16542056794189 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((1879 : ℕ)^1 * ((43155143 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 16542056794189)^8271028397094 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 16542056794189)^5514018931396 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 16542056794189)^973062164364 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1879 := Nat.prime_eq_prime_of_dvd_pow hq prime_1879 hd
            subst q
            change (2 : ZMod 16542056794189)^8803649172 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 43155143 := Nat.prime_eq_prime_of_dvd_pow hq prime_43155143 hd
            subst q
            change (2 : ZMod 16542056794189)^383316 ≠ 1
            reduce_mod_char
            decide

theorem prime_16777216000033 : Nat.Prime 16777216000033 := by
  apply lucas_primality 16777216000033 (5 : ZMod 16777216000033)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16777216000033 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((601 : ℕ)^1 * ((290786467 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 16777216000033)^8388608000016 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 16777216000033)^5592405333344 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 601 := Nat.prime_eq_prime_of_dvd_pow hq prime_601 hd
          subst q
          change (5 : ZMod 16777216000033)^27915500832 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 290786467 := Nat.prime_eq_prime_of_dvd_pow hq prime_290786467 hd
          subst q
          change (5 : ZMod 16777216000033)^57696 ≠ 1
          reduce_mod_char
          decide

theorem prime_16962641644901 : Nat.Prime 16962641644901 := by
  apply lucas_primality 16962641644901 (2 : ZMod 16962641644901)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16962641644901 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((7 : ℕ)^2 * ((17 : ℕ)^1 * ((1201 : ℕ)^1 * ((169553 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 16962641644901)^8481320822450 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 16962641644901)^3392528328980 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 16962641644901)^2423234520700 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (2 : ZMod 16962641644901)^997802449700 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1201 := Nat.prime_eq_prime_of_dvd_pow hq prime_1201 hd
              subst q
              change (2 : ZMod 16962641644901)^14123764900 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 169553 := Nat.prime_eq_prime_of_dvd_pow hq prime_169553 hd
              subst q
              change (2 : ZMod 16962641644901)^100043300 ≠ 1
              reduce_mod_char
              decide

theorem prime_17082879366811 : Nat.Prime 17082879366811 := by
  apply lucas_primality 17082879366811 (3 : ZMod 17082879366811)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17082879366811 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((421 : ℕ)^1 * ((1352563687 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 17082879366811)^8541439683405 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 17082879366811)^5694293122270 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 17082879366811)^3416575873362 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 421 := Nat.prime_eq_prime_of_dvd_pow hq prime_421 hd
            subst q
            change (3 : ZMod 17082879366811)^40576910610 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1352563687 := Nat.prime_eq_prime_of_dvd_pow hq prime_1352563687 hd
            subst q
            change (3 : ZMod 17082879366811)^12630 ≠ 1
            reduce_mod_char
            decide

theorem prime_17416274304971 : Nat.Prime 17416274304971 := by
  apply lucas_primality 17416274304971 (2 : ZMod 17416274304971)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17416274304971 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((29 : ℕ)^1 * ((41 : ℕ)^1 * ((7673 : ℕ)^1 * ((190901 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 17416274304971)^8708137152485 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 17416274304971)^3483254860994 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (2 : ZMod 17416274304971)^600561182930 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (2 : ZMod 17416274304971)^424787178170 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 7673 := Nat.prime_eq_prime_of_dvd_pow hq prime_7673 hd
              subst q
              change (2 : ZMod 17416274304971)^2269812890 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 190901 := Nat.prime_eq_prime_of_dvd_pow hq prime_190901 hd
              subst q
              change (2 : ZMod 17416274304971)^91231970 ≠ 1
              reduce_mod_char
              decide

theorem prime_17580914163551 : Nat.Prime 17580914163551 := by
  apply lucas_primality 17580914163551 (7 : ZMod 17580914163551)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17580914163551 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((1187 : ℕ)^1 * ((296224333 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 17580914163551)^8790457081775 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 17580914163551)^3516182832710 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1187 := Nat.prime_eq_prime_of_dvd_pow hq prime_1187 hd
          subst q
          change (7 : ZMod 17580914163551)^14811216650 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 296224333 := Nat.prime_eq_prime_of_dvd_pow hq prime_296224333 hd
          subst q
          change (7 : ZMod 17580914163551)^59350 ≠ 1
          reduce_mod_char
          decide

theorem prime_18075490334807 : Nat.Prime 18075490334807 := by
  apply lucas_primality 18075490334807 (5 : ZMod 18075490334807)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18075490334807 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((613 : ℕ)^1 * ((641020297 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 18075490334807)^9037745167403 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (5 : ZMod 18075490334807)^785890884122 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 613 := Nat.prime_eq_prime_of_dvd_pow hq prime_613 hd
          subst q
          change (5 : ZMod 18075490334807)^29486933662 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 641020297 := Nat.prime_eq_prime_of_dvd_pow hq prime_641020297 hd
          subst q
          change (5 : ZMod 18075490334807)^28198 ≠ 1
          reduce_mod_char
          decide

theorem prime_18079386826981 : Nat.Prime 18079386826981 := by
  apply lucas_primality 18079386826981 (2 : ZMod 18079386826981)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18079386826981 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((389 : ℕ)^1 * ((523 : ℕ)^1 * ((1217 : ℕ)^2))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 18079386826981)^9039693413490 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 18079386826981)^6026462275660 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 18079386826981)^3615877365396 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 389 := Nat.prime_eq_prime_of_dvd_pow hq prime_389 hd
            subst q
            change (2 : ZMod 18079386826981)^46476572820 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 523 := Nat.prime_eq_prime_of_dvd_pow hq prime_523 hd
              subst q
              change (2 : ZMod 18079386826981)^34568617260 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1217 := Nat.prime_eq_prime_of_dvd_pow hq prime_1217 hd
              subst q
              change (2 : ZMod 18079386826981)^14855699940 ≠ 1
              reduce_mod_char
              decide

theorem prime_18647389868269 : Nat.Prime 18647389868269 := by
  apply lucas_primality 18647389868269 (2 : ZMod 18647389868269)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18647389868269 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((31 : ℕ)^2 * ((163 : ℕ)^1 * ((1417189 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 18647389868269)^9323694934134 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 18647389868269)^6215796622756 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 18647389868269)^2663912838324 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (2 : ZMod 18647389868269)^601528705428 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
              subst q
              change (2 : ZMod 18647389868269)^114401164836 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1417189 := Nat.prime_eq_prime_of_dvd_pow hq prime_1417189 hd
              subst q
              change (2 : ZMod 18647389868269)^13158012 ≠ 1
              reduce_mod_char
              decide

theorem prime_18755369578067 : Nat.Prime 18755369578067 := by
  apply lucas_primality 18755369578067 (2 : ZMod 18755369578067)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18755369578067 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((15923 : ℕ)^1 * ((53539961 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 18755369578067)^9377684789033 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 18755369578067)^1705033598006 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 15923 := Nat.prime_eq_prime_of_dvd_pow hq prime_15923 hd
          subst q
          change (2 : ZMod 18755369578067)^1177879142 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 53539961 := Nat.prime_eq_prime_of_dvd_pow hq prime_53539961 hd
          subst q
          change (2 : ZMod 18755369578067)^350306 ≠ 1
          reduce_mod_char
          decide

theorem prime_19276252118927 : Nat.Prime 19276252118927 := by
  apply lucas_primality 19276252118927 (5 : ZMod 19276252118927)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19276252118927 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((37 : ℕ)^1 * ((661 : ℕ)^1 * ((1021 : ℕ)^1 * ((35089 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 19276252118927)^9638126059463 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 19276252118927)^1752386556266 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (5 : ZMod 19276252118927)^520979786998 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 661 := Nat.prime_eq_prime_of_dvd_pow hq prime_661 hd
            subst q
            change (5 : ZMod 19276252118927)^29162257366 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1021 := Nat.prime_eq_prime_of_dvd_pow hq prime_1021 hd
              subst q
              change (5 : ZMod 19276252118927)^18879776806 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 35089 := Nat.prime_eq_prime_of_dvd_pow hq prime_35089 hd
              subst q
              change (5 : ZMod 19276252118927)^549353134 ≠ 1
              reduce_mod_char
              decide

theorem prime_19456426971187 : Nat.Prime 19456426971187 := by
  apply lucas_primality 19456426971187 (2 : ZMod 19456426971187)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19456426971187 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((2963 : ℕ)^1 * ((1094410337 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 19456426971187)^9728213485593 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 19456426971187)^6485475657062 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2963 := Nat.prime_eq_prime_of_dvd_pow hq prime_2963 hd
          subst q
          change (2 : ZMod 19456426971187)^6566462022 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1094410337 := Nat.prime_eq_prime_of_dvd_pow hq prime_1094410337 hd
          subst q
          change (2 : ZMod 19456426971187)^17778 ≠ 1
          reduce_mod_char
          decide

theorem prime_20046078070897 : Nat.Prime 20046078070897 := by
  apply lucas_primality 20046078070897 (10 : ZMod 20046078070897)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20046078070897 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((37 : ℕ)^1 * ((67 : ℕ)^1 * ((168465763 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 20046078070897)^10023039035448 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 20046078070897)^6682026023632 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (10 : ZMod 20046078070897)^541785893808 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
            subst q
            change (10 : ZMod 20046078070897)^299195195088 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 168465763 := Nat.prime_eq_prime_of_dvd_pow hq prime_168465763 hd
            subst q
            change (10 : ZMod 20046078070897)^118992 ≠ 1
            reduce_mod_char
            decide

theorem prime_20179187015629 : Nat.Prime 20179187015629 := by
  apply lucas_primality 20179187015629 (7 : ZMod 20179187015629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20179187015629 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((21157 : ℕ)^1 * ((79481917 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 20179187015629)^10089593507814 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 20179187015629)^6726395671876 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 21157 := Nat.prime_eq_prime_of_dvd_pow hq prime_21157 hd
          subst q
          change (7 : ZMod 20179187015629)^953783004 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 79481917 := Nat.prime_eq_prime_of_dvd_pow hq prime_79481917 hd
          subst q
          change (7 : ZMod 20179187015629)^253884 ≠ 1
          reduce_mod_char
          decide

theorem prime_20924183895751 : Nat.Prime 20924183895751 := by
  apply lucas_primality 20924183895751 (11 : ZMod 20924183895751)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20924183895751 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^3 * ((9299637287 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 20924183895751)^10462091947875 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 20924183895751)^6974727965250 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 20924183895751)^4184836779150 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 9299637287 := Nat.prime_eq_prime_of_dvd_pow hq prime_9299637287 hd
          subst q
          change (11 : ZMod 20924183895751)^2250 ≠ 1
          reduce_mod_char
          decide

theorem prime_21624389648441 : Nat.Prime 21624389648441 := by
  apply lucas_primality 21624389648441 (3 : ZMod 21624389648441)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21624389648441 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((23 : ℕ)^1 * ((23504771357 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 21624389648441)^10812194824220 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 21624389648441)^4324877929688 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (3 : ZMod 21624389648441)^940190854280 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 23504771357 := Nat.prime_eq_prime_of_dvd_pow hq prime_23504771357 hd
          subst q
          change (3 : ZMod 21624389648441)^920 ≠ 1
          reduce_mod_char
          decide

theorem prime_21691961596381 : Nat.Prime 21691961596381 := by
  apply lucas_primality 21691961596381 (2 : ZMod 21691961596381)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21691961596381 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((23 : ℕ)^1 * ((389 : ℕ)^1 * ((2797 : ℕ)^1 * ((14447 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 21691961596381)^10845980798190 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 21691961596381)^7230653865460 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 21691961596381)^4338392319276 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (2 : ZMod 21691961596381)^943128765060 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 389 := Nat.prime_eq_prime_of_dvd_pow hq prime_389 hd
              subst q
              change (2 : ZMod 21691961596381)^55763397420 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 2797 := Nat.prime_eq_prime_of_dvd_pow hq prime_2797 hd
                subst q
                change (2 : ZMod 21691961596381)^7755438540 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 14447 := Nat.prime_eq_prime_of_dvd_pow hq prime_14447 hd
                subst q
                change (2 : ZMod 21691961596381)^1501485540 ≠ 1
                reduce_mod_char
                decide

theorem prime_21981971869213 : Nat.Prime 21981971869213 := by
  apply lucas_primality 21981971869213 (5 : ZMod 21981971869213)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21981971869213 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((163 : ℕ)^1 * ((241 : ℕ)^1 * ((46631647 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 21981971869213)^10990985934606 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 21981971869213)^7327323956404 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
          subst q
          change (5 : ZMod 21981971869213)^134858723124 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 241 := Nat.prime_eq_prime_of_dvd_pow hq prime_241 hd
            subst q
            change (5 : ZMod 21981971869213)^91211501532 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 46631647 := Nat.prime_eq_prime_of_dvd_pow hq prime_46631647 hd
            subst q
            change (5 : ZMod 21981971869213)^471396 ≠ 1
            reduce_mod_char
            decide

theorem prime_22101639798989 : Nat.Prime 22101639798989 := by
  apply lucas_primality 22101639798989 (2 : ZMod 22101639798989)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22101639798989 - 1 = (2 : ℕ)^2 * ((17 : ℕ)^1 * ((31 : ℕ)^1 * ((61837 : ℕ)^1 * ((169553 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 22101639798989)^11050819899494 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 22101639798989)^1300096458764 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (2 : ZMod 22101639798989)^712956122548 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 61837 := Nat.prime_eq_prime_of_dvd_pow hq prime_61837 hd
            subst q
            change (2 : ZMod 22101639798989)^357417724 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 169553 := Nat.prime_eq_prime_of_dvd_pow hq prime_169553 hd
            subst q
            change (2 : ZMod 22101639798989)^130352396 ≠ 1
            reduce_mod_char
            decide

theorem prime_22483074023437 : Nat.Prime 22483074023437 := by
  apply lucas_primality 22483074023437 (2 : ZMod 22483074023437)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22483074023437 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((19 : ℕ)^1 * ((3697 : ℕ)^1 * ((2051767 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 22483074023437)^11241537011718 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 22483074023437)^7494358007812 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 22483074023437)^1729467232572 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (2 : ZMod 22483074023437)^1183319685444 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 3697 := Nat.prime_eq_prime_of_dvd_pow hq prime_3697 hd
              subst q
              change (2 : ZMod 22483074023437)^6081437388 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 2051767 := Nat.prime_eq_prime_of_dvd_pow hq prime_2051767 hd
              subst q
              change (2 : ZMod 22483074023437)^10957908 ≠ 1
              reduce_mod_char
              decide

theorem prime_22580444863391 : Nat.Prime 22580444863391 := by
  apply lucas_primality 22580444863391 (7 : ZMod 22580444863391)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22580444863391 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((43 : ℕ)^1 * ((397 : ℕ)^1 * ((132273709 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 22580444863391)^11290222431695 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 22580444863391)^4516088972678 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (7 : ZMod 22580444863391)^525126624730 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 397 := Nat.prime_eq_prime_of_dvd_pow hq prime_397 hd
            subst q
            change (7 : ZMod 22580444863391)^56877694870 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 132273709 := Nat.prime_eq_prime_of_dvd_pow hq prime_132273709 hd
            subst q
            change (7 : ZMod 22580444863391)^170710 ≠ 1
            reduce_mod_char
            decide

theorem prime_23118071761153 : Nat.Prime 23118071761153 := by
  apply lucas_primality 23118071761153 (11 : ZMod 23118071761153)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23118071761153 - 1 = (2 : ℕ)^8 * ((3 : ℕ)^2 * ((19 : ℕ)^1 * ((528099227 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 23118071761153)^11559035880576 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 23118071761153)^7706023920384 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (11 : ZMod 23118071761153)^1216740619008 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 528099227 := Nat.prime_eq_prime_of_dvd_pow hq prime_528099227 hd
          subst q
          change (11 : ZMod 23118071761153)^43776 ≠ 1
          reduce_mod_char
          decide

theorem prime_23298085122503 : Nat.Prime 23298085122503 := by
  apply lucas_primality 23298085122503 (5 : ZMod 23298085122503)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23298085122503 - 1 = (2 : ℕ)^1 * ((881 : ℕ)^1 * ((13222522771 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 23298085122503)^11649042561251 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 881 := Nat.prime_eq_prime_of_dvd_pow hq prime_881 hd
        subst q
        change (5 : ZMod 23298085122503)^26445045542 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13222522771 := Nat.prime_eq_prime_of_dvd_pow hq prime_13222522771 hd
        subst q
        change (5 : ZMod 23298085122503)^1762 ≠ 1
        reduce_mod_char
        decide

theorem prime_23580429529889 : Nat.Prime 23580429529889 := by
  apply lucas_primality 23580429529889 (6 : ZMod 23580429529889)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23580429529889 - 1 = (2 : ℕ)^5 * ((7 : ℕ)^2 * ((11 : ℕ)^1 * ((1367139931 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 23580429529889)^11790214764944 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (6 : ZMod 23580429529889)^3368632789984 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (6 : ZMod 23580429529889)^2143675411808 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1367139931 := Nat.prime_eq_prime_of_dvd_pow hq prime_1367139931 hd
          subst q
          change (6 : ZMod 23580429529889)^17248 ≠ 1
          reduce_mod_char
          decide

theorem prime_24137569000019 : Nat.Prime 24137569000019 := by
  apply lucas_primality 24137569000019 (6 : ZMod 24137569000019)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24137569000019 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((635199184211 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 24137569000019)^12068784500009 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (6 : ZMod 24137569000019)^1270398368422 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 635199184211 := Nat.prime_eq_prime_of_dvd_pow hq prime_635199184211 hd
        subst q
        change (6 : ZMod 24137569000019)^38 ≠ 1
        reduce_mod_char
        decide

theorem prime_24430499846959 : Nat.Prime 24430499846959 := by
  apply lucas_primality 24430499846959 (13 : ZMod 24430499846959)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24430499846959 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((67 : ℕ)^1 * ((313 : ℕ)^1 * ((367 : ℕ)^1 * ((529049 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 24430499846959)^12215249923479 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 24430499846959)^8143499948986 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (13 : ZMod 24430499846959)^364634326074 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 313 := Nat.prime_eq_prime_of_dvd_pow hq prime_313 hd
            subst q
            change (13 : ZMod 24430499846959)^78052715166 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 367 := Nat.prime_eq_prime_of_dvd_pow hq prime_367 hd
              subst q
              change (13 : ZMod 24430499846959)^66568119474 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 529049 := Nat.prime_eq_prime_of_dvd_pow hq prime_529049 hd
              subst q
              change (13 : ZMod 24430499846959)^46178142 ≠ 1
              reduce_mod_char
              decide

theorem prime_25002110044573 : Nat.Prime 25002110044573 := by
  apply lucas_primality 25002110044573 (2 : ZMod 25002110044573)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 25002110044573 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((1061 : ℕ)^1 * ((2351 : ℕ)^1 * ((835271 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 25002110044573)^12501055022286 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 25002110044573)^8334036681524 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1061 := Nat.prime_eq_prime_of_dvd_pow hq prime_1061 hd
          subst q
          change (2 : ZMod 25002110044573)^23564665452 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2351 := Nat.prime_eq_prime_of_dvd_pow hq prime_2351 hd
            subst q
            change (2 : ZMod 25002110044573)^10634670372 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 835271 := Nat.prime_eq_prime_of_dvd_pow hq prime_835271 hd
            subst q
            change (2 : ZMod 25002110044573)^29932932 ≠ 1
            reduce_mod_char
            decide

theorem prime_25096092664919 : Nat.Prime 25096092664919 := by
  apply lucas_primality 25096092664919 (23 : ZMod 25096092664919)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 25096092664919 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((1140731484769 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (23 : ZMod 25096092664919)^12548046332459 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (23 : ZMod 25096092664919)^2281462969538 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1140731484769 := Nat.prime_eq_prime_of_dvd_pow hq prime_1140731484769 hd
        subst q
        change (23 : ZMod 25096092664919)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_25892303048723 : Nat.Prime 25892303048723 := by
  apply lucas_primality 25892303048723 (2 : ZMod 25892303048723)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 25892303048723 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((19 : ℕ)^1 * ((78593 : ℕ)^1 * ((788153 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 25892303048723)^12946151524361 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 25892303048723)^2353845731702 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 25892303048723)^1362752792038 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 78593 := Nat.prime_eq_prime_of_dvd_pow hq prime_78593 hd
            subst q
            change (2 : ZMod 25892303048723)^329447954 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 788153 := Nat.prime_eq_prime_of_dvd_pow hq prime_788153 hd
            subst q
            change (2 : ZMod 25892303048723)^32851874 ≠ 1
            reduce_mod_char
            decide

theorem prime_26808753332099 : Nat.Prime 26808753332099 := by
  apply lucas_primality 26808753332099 (2 : ZMod 26808753332099)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26808753332099 - 1 = (2 : ℕ)^1 * ((13404376666049 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 26808753332099)^13404376666049 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 13404376666049 := Nat.prime_eq_prime_of_dvd_pow hq prime_13404376666049 hd
      subst q
      change (2 : ZMod 26808753332099)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_27752076864583 : Nat.Prime 27752076864583 := by
  apply lucas_primality 27752076864583 (5 : ZMod 27752076864583)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 27752076864583 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((660763734871 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 27752076864583)^13876038432291 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 27752076864583)^9250692288194 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 27752076864583)^3964582409226 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 660763734871 := Nat.prime_eq_prime_of_dvd_pow hq prime_660763734871 hd
          subst q
          change (5 : ZMod 27752076864583)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_27917216890837 : Nat.Prime 27917216890837 := by
  apply lucas_primality 27917216890837 (26 : ZMod 27917216890837)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 27917216890837 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((23 : ℕ)^1 * ((37 : ℕ)^1 * ((30041383 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (26 : ZMod 27917216890837)^13958608445418 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (26 : ZMod 27917216890837)^9305738963612 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (26 : ZMod 27917216890837)^3988173841548 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (26 : ZMod 27917216890837)^2147478222372 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
              subst q
              change (26 : ZMod 27917216890837)^1213792038732 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
                subst q
                change (26 : ZMod 27917216890837)^754519375428 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 30041383 := Nat.prime_eq_prime_of_dvd_pow hq prime_30041383 hd
                subst q
                change (26 : ZMod 27917216890837)^929292 ≠ 1
                reduce_mod_char
                decide

theorem prime_28722900390631 : Nat.Prime 28722900390631 := by
  apply lucas_primality 28722900390631 (3 : ZMod 28722900390631)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 28722900390631 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((957430013021 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 28722900390631)^14361450195315 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 28722900390631)^9574300130210 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 28722900390631)^5744580078126 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 957430013021 := Nat.prime_eq_prime_of_dvd_pow hq prime_957430013021 hd
          subst q
          change (3 : ZMod 28722900390631)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_29187423583699 : Nat.Prime 29187423583699 := by
  apply lucas_primality 29187423583699 (17 : ZMod 29187423583699)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 29187423583699 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((599 : ℕ)^1 * ((102013 : ℕ)^1 * ((79609 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 29187423583699)^14593711791849 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 29187423583699)^9729141194566 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 599 := Nat.prime_eq_prime_of_dvd_pow hq prime_599 hd
          subst q
          change (17 : ZMod 29187423583699)^48726917502 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 102013 := Nat.prime_eq_prime_of_dvd_pow hq prime_102013 hd
            subst q
            change (17 : ZMod 29187423583699)^286114746 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 79609 := Nat.prime_eq_prime_of_dvd_pow hq prime_79609 hd
            subst q
            change (17 : ZMod 29187423583699)^366634722 ≠ 1
            reduce_mod_char
            decide

theorem prime_29434443991723 : Nat.Prime 29434443991723 := by
  apply lucas_primality 29434443991723 (7 : ZMod 29434443991723)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 29434443991723 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((11719 : ℕ)^1 * ((35533 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 29434443991723)^14717221995861 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 29434443991723)^9811481330574 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 29434443991723)^4204920570246 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (7 : ZMod 29434443991723)^2675858544702 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
              subst q
              change (7 : ZMod 29434443991723)^1731437881866 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 11719 := Nat.prime_eq_prime_of_dvd_pow hq prime_11719 hd
                subst q
                change (7 : ZMod 29434443991723)^2511685638 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 35533 := Nat.prime_eq_prime_of_dvd_pow hq prime_35533 hd
                subst q
                change (7 : ZMod 29434443991723)^828369234 ≠ 1
                reduce_mod_char
                decide

theorem prime_29721861554179 : Nat.Prime 29721861554179 := by
  apply lucas_primality 29721861554179 (2 : ZMod 29721861554179)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 29721861554179 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((4953643592363 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 29721861554179)^14860930777089 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 29721861554179)^9907287184726 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4953643592363 := Nat.prime_eq_prime_of_dvd_pow hq prime_4953643592363 hd
        subst q
        change (2 : ZMod 29721861554179)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_30749609024311 : Nat.Prime 30749609024311 := by
  apply lucas_primality 30749609024311 (3 : ZMod 30749609024311)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 30749609024311 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((3217 : ℕ)^1 * ((28965071 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 30749609024311)^15374804512155 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 30749609024311)^10249869674770 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 30749609024311)^6149921804862 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (3 : ZMod 30749609024311)^2795419002210 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 3217 := Nat.prime_eq_prime_of_dvd_pow hq prime_3217 hd
              subst q
              change (3 : ZMod 30749609024311)^9558473430 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 28965071 := Nat.prime_eq_prime_of_dvd_pow hq prime_28965071 hd
              subst q
              change (3 : ZMod 30749609024311)^1061610 ≠ 1
              reduce_mod_char
              decide

theorem prime_31806802621507 : Nat.Prime 31806802621507 := by
  apply lucas_primality 31806802621507 (2 : ZMod 31806802621507)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 31806802621507 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((6451 : ℕ)^1 * ((74704891 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 31806802621507)^15903401310753 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 31806802621507)^10602267540502 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 31806802621507)^2891527511046 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 6451 := Nat.prime_eq_prime_of_dvd_pow hq prime_6451 hd
            subst q
            change (2 : ZMod 31806802621507)^4930522806 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 74704891 := Nat.prime_eq_prime_of_dvd_pow hq prime_74704891 hd
            subst q
            change (2 : ZMod 31806802621507)^425766 ≠ 1
            reduce_mod_char
            decide

theorem prime_32427743246473 : Nat.Prime 32427743246473 := by
  apply lucas_primality 32427743246473 (5 : ZMod 32427743246473)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32427743246473 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((17 : ℕ)^1 * ((13259 : ℕ)^1 * ((856343 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 32427743246473)^16213871623236 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 32427743246473)^10809247748824 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 32427743246473)^4632534749496 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (5 : ZMod 32427743246473)^1907514308616 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 13259 := Nat.prime_eq_prime_of_dvd_pow hq prime_13259 hd
              subst q
              change (5 : ZMod 32427743246473)^2445715608 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 856343 := Nat.prime_eq_prime_of_dvd_pow hq prime_856343 hd
              subst q
              change (5 : ZMod 32427743246473)^37867704 ≠ 1
              reduce_mod_char
              decide

theorem prime_32714911688741 : Nat.Prime 32714911688741 := by
  apply lucas_primality 32714911688741 (2 : ZMod 32714911688741)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32714911688741 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((29 : ℕ)^1 * ((56405020153 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 32714911688741)^16357455844370 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 32714911688741)^6542982337748 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (2 : ZMod 32714911688741)^1128100403060 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 56405020153 := Nat.prime_eq_prime_of_dvd_pow hq prime_56405020153 hd
          subst q
          change (2 : ZMod 32714911688741)^580 ≠ 1
          reduce_mod_char
          decide

theorem prime_32894113444943 : Nat.Prime 32894113444943 := by
  apply lucas_primality 32894113444943 (5 : ZMod 32894113444943)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32894113444943 - 1 = (2 : ℕ)^1 * ((16447056722471 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 32894113444943)^16447056722471 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 16447056722471 := Nat.prime_eq_prime_of_dvd_pow hq prime_16447056722471 hd
      subst q
      change (5 : ZMod 32894113444943)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_33085430418647 : Nat.Prime 33085430418647 := by
  apply lucas_primality 33085430418647 (5 : ZMod 33085430418647)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 33085430418647 - 1 = (2 : ℕ)^1 * ((4467511 : ℕ)^1 * ((3702893 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 33085430418647)^16542715209323 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 4467511 := Nat.prime_eq_prime_of_dvd_pow hq prime_4467511 hd
        subst q
        change (5 : ZMod 33085430418647)^7405786 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3702893 := Nat.prime_eq_prime_of_dvd_pow hq prime_3702893 hd
        subst q
        change (5 : ZMod 33085430418647)^8935022 ≠ 1
        reduce_mod_char
        decide

theorem prime_34012224000011 : Nat.Prime 34012224000011 := by
  apply lucas_primality 34012224000011 (2 : ZMod 34012224000011)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34012224000011 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((131 : ℕ)^1 * ((1321 : ℕ)^1 * ((19654451 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 34012224000011)^17006112000005 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 34012224000011)^6802444800002 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
          subst q
          change (2 : ZMod 34012224000011)^259635297710 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1321 := Nat.prime_eq_prime_of_dvd_pow hq prime_1321 hd
            subst q
            change (2 : ZMod 34012224000011)^25747330810 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 19654451 := Nat.prime_eq_prime_of_dvd_pow hq prime_19654451 hd
            subst q
            change (2 : ZMod 34012224000011)^1730510 ≠ 1
            reduce_mod_char
            decide

theorem prime_34934717486363 : Nat.Prime 34934717486363 := by
  apply lucas_primality 34934717486363 (2 : ZMod 34934717486363)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34934717486363 - 1 = (2 : ℕ)^1 * ((24611 : ℕ)^1 * ((709737871 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 34934717486363)^17467358743181 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 24611 := Nat.prime_eq_prime_of_dvd_pow hq prime_24611 hd
        subst q
        change (2 : ZMod 34934717486363)^1419475742 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 709737871 := Nat.prime_eq_prime_of_dvd_pow hq prime_709737871 hd
        subst q
        change (2 : ZMod 34934717486363)^49222 ≠ 1
        reduce_mod_char
        decide

theorem prime_35000342122423 : Nat.Prime 35000342122423 := by
  apply lucas_primality 35000342122423 (3 : ZMod 35000342122423)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 35000342122423 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((523553 : ℕ)^1 * ((11141929 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 35000342122423)^17500171061211 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 35000342122423)^11666780707474 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 523553 := Nat.prime_eq_prime_of_dvd_pow hq prime_523553 hd
          subst q
          change (3 : ZMod 35000342122423)^66851574 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11141929 := Nat.prime_eq_prime_of_dvd_pow hq prime_11141929 hd
          subst q
          change (3 : ZMod 35000342122423)^3141318 ≠ 1
          reduce_mod_char
          decide

theorem prime_35042195672167 : Nat.Prime 35042195672167 := by
  apply lucas_primality 35042195672167 (3 : ZMod 35042195672167)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 35042195672167 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((37 : ℕ)^1 * ((157847728253 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 35042195672167)^17521097836083 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 35042195672167)^11680731890722 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (3 : ZMod 35042195672167)^947086369518 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 157847728253 := Nat.prime_eq_prime_of_dvd_pow hq prime_157847728253 hd
          subst q
          change (3 : ZMod 35042195672167)^222 ≠ 1
          reduce_mod_char
          decide

theorem prime_35161828327103 : Nat.Prime 35161828327103 := by
  apply lucas_primality 35161828327103 (5 : ZMod 35161828327103)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 35161828327103 - 1 = (2 : ℕ)^1 * ((17580914163551 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 35161828327103)^17580914163551 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 17580914163551 := Nat.prime_eq_prime_of_dvd_pow hq prime_17580914163551 hd
      subst q
      change (5 : ZMod 35161828327103)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_36123169140469 : Nat.Prime 36123169140469 := by
  apply lucas_primality 36123169140469 (2 : ZMod 36123169140469)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 36123169140469 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((1003421365013 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 36123169140469)^18061584570234 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 36123169140469)^12041056380156 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1003421365013 := Nat.prime_eq_prime_of_dvd_pow hq prime_1003421365013 hd
        subst q
        change (2 : ZMod 36123169140469)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_36343632130667 : Nat.Prime 36343632130667 := by
  apply lucas_primality 36343632130667 (5 : ZMod 36343632130667)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 36343632130667 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((2595973723619 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 36343632130667)^18171816065333 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 36343632130667)^5191947447238 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2595973723619 := Nat.prime_eq_prime_of_dvd_pow hq prime_2595973723619 hd
        subst q
        change (5 : ZMod 36343632130667)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_36864176815877 : Nat.Prime 36864176815877 := by
  apply lucas_primality 36864176815877 (2 : ZMod 36864176815877)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 36864176815877 - 1 = (2 : ℕ)^2 * ((769 : ℕ)^1 * ((38371 : ℕ)^1 * ((312331 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 36864176815877)^18432088407938 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 769 := Nat.prime_eq_prime_of_dvd_pow hq prime_769 hd
        subst q
        change (2 : ZMod 36864176815877)^47937811204 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 38371 := Nat.prime_eq_prime_of_dvd_pow hq prime_38371 hd
          subst q
          change (2 : ZMod 36864176815877)^960730156 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 312331 := Nat.prime_eq_prime_of_dvd_pow hq prime_312331 hd
          subst q
          change (2 : ZMod 36864176815877)^118029196 ≠ 1
          reduce_mod_char
          decide

theorem prime_37558352909219 : Nat.Prime 37558352909219 := by
  apply lucas_primality 37558352909219 (2 : ZMod 37558352909219)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 37558352909219 - 1 = (2 : ℕ)^1 * ((1021 : ℕ)^1 * ((18392925029 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 37558352909219)^18779176454609 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1021 := Nat.prime_eq_prime_of_dvd_pow hq prime_1021 hd
        subst q
        change (2 : ZMod 37558352909219)^36785850058 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 18392925029 := Nat.prime_eq_prime_of_dvd_pow hq prime_18392925029 hd
        subst q
        change (2 : ZMod 37558352909219)^2042 ≠ 1
        reduce_mod_char
        decide

theorem prime_38806720086019 : Nat.Prime 38806720086019 := by
  apply lucas_primality 38806720086019 (2 : ZMod 38806720086019)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 38806720086019 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((1595339 : ℕ)^1 * ((238481 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 38806720086019)^19403360043009 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 38806720086019)^12935573362006 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 38806720086019)^2282748240354 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1595339 := Nat.prime_eq_prime_of_dvd_pow hq prime_1595339 hd
            subst q
            change (2 : ZMod 38806720086019)^24325062 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 238481 := Nat.prime_eq_prime_of_dvd_pow hq prime_238481 hd
            subst q
            change (2 : ZMod 38806720086019)^162724578 ≠ 1
            reduce_mod_char
            decide

theorem prime_40089475140653 : Nat.Prime 40089475140653 := by
  apply lucas_primality 40089475140653 (2 : ZMod 40089475140653)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 40089475140653 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((43 : ℕ)^1 * ((151 : ℕ)^1 * ((199 : ℕ)^1 * ((223 : ℕ)^1 * ((4969 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 40089475140653)^20044737570326 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 40089475140653)^5727067877236 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (2 : ZMod 40089475140653)^932313375364 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
            subst q
            change (2 : ZMod 40089475140653)^265493212852 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 199 := Nat.prime_eq_prime_of_dvd_pow hq prime_199 hd
              subst q
              change (2 : ZMod 40089475140653)^201454648948 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 223 := Nat.prime_eq_prime_of_dvd_pow hq prime_223 hd
                subst q
                change (2 : ZMod 40089475140653)^179773431124 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 4969 := Nat.prime_eq_prime_of_dvd_pow hq prime_4969 hd
                subst q
                change (2 : ZMod 40089475140653)^8067916108 ≠ 1
                reduce_mod_char
                decide

theorem prime_40567018513163 : Nat.Prime 40567018513163 := by
  apply lucas_primality 40567018513163 (2 : ZMod 40567018513163)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 40567018513163 - 1 = (2 : ℕ)^1 * ((1039 : ℕ)^1 * ((24917 : ℕ)^1 * ((783487 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 40567018513163)^20283509256581 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1039 := Nat.prime_eq_prime_of_dvd_pow hq prime_1039 hd
        subst q
        change (2 : ZMod 40567018513163)^39044291158 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 24917 := Nat.prime_eq_prime_of_dvd_pow hq prime_24917 hd
          subst q
          change (2 : ZMod 40567018513163)^1628085986 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 783487 := Nat.prime_eq_prime_of_dvd_pow hq prime_783487 hd
          subst q
          change (2 : ZMod 40567018513163)^51777526 ≠ 1
          reduce_mod_char
          decide

theorem prime_41407371740743 : Nat.Prime 41407371740743 := by
  apply lucas_primality 41407371740743 (13 : ZMod 41407371740743)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 41407371740743 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((101929 : ℕ)^1 * ((9672319 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 41407371740743)^20703685870371 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 41407371740743)^13802457246914 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (13 : ZMod 41407371740743)^5915338820106 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 101929 := Nat.prime_eq_prime_of_dvd_pow hq prime_101929 hd
            subst q
            change (13 : ZMod 41407371740743)^406237398 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 9672319 := Nat.prime_eq_prime_of_dvd_pow hq prime_9672319 hd
            subst q
            change (13 : ZMod 41407371740743)^4281018 ≠ 1
            reduce_mod_char
            decide

theorem prime_42075142964209 : Nat.Prime 42075142964209 := by
  apply lucas_primality 42075142964209 (7 : ZMod 42075142964209)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 42075142964209 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^3 * ((229 : ℕ)^1 * ((425310761 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 42075142964209)^21037571482104 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 42075142964209)^14025047654736 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 229 := Nat.prime_eq_prime_of_dvd_pow hq prime_229 hd
          subst q
          change (7 : ZMod 42075142964209)^183734248752 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 425310761 := Nat.prime_eq_prime_of_dvd_pow hq prime_425310761 hd
          subst q
          change (7 : ZMod 42075142964209)^98928 ≠ 1
          reduce_mod_char
          decide

theorem prime_42512401733713 : Nat.Prime 42512401733713 := by
  apply lucas_primality 42512401733713 (10 : ZMod 42512401733713)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 42512401733713 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((885675036119 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 42512401733713)^21256200866856 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 42512401733713)^14170800577904 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 885675036119 := Nat.prime_eq_prime_of_dvd_pow hq prime_885675036119 hd
        subst q
        change (10 : ZMod 42512401733713)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_42761175875227 : Nat.Prime 42761175875227 := by
  apply lucas_primality 42761175875227 (2 : ZMod 42761175875227)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 42761175875227 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^5 * ((17 : ℕ)^1 * ((163 : ℕ)^1 * ((3607 : ℕ)^1 * ((8803 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 42761175875227)^21380587937613 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 42761175875227)^14253725291742 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 42761175875227)^2515363286778 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
            subst q
            change (2 : ZMod 42761175875227)^262338502302 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 3607 := Nat.prime_eq_prime_of_dvd_pow hq prime_3607 hd
              subst q
              change (2 : ZMod 42761175875227)^11855052918 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 8803 := Nat.prime_eq_prime_of_dvd_pow hq prime_8803 hd
              subst q
              change (2 : ZMod 42761175875227)^4857568542 ≠ 1
              reduce_mod_char
              decide

theorem prime_43423910643779 : Nat.Prime 43423910643779 := by
  apply lucas_primality 43423910643779 (6 : ZMod 43423910643779)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 43423910643779 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((3101707903127 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 43423910643779)^21711955321889 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (6 : ZMod 43423910643779)^6203415806254 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3101707903127 := Nat.prime_eq_prime_of_dvd_pow hq prime_3101707903127 hd
        subst q
        change (6 : ZMod 43423910643779)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_43674080794891 : Nat.Prime 43674080794891 := by
  apply lucas_primality 43674080794891 (2 : ZMod 43674080794891)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 43674080794891 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((17 : ℕ)^1 * ((19 : ℕ)^1 * ((5521 : ℕ)^1 * ((8971 : ℕ)^1)))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 43674080794891)^21837040397445 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 43674080794891)^14558026931630 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 43674080794891)^8734816158978 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (2 : ZMod 43674080794891)^6239154399270 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
              subst q
              change (2 : ZMod 43674080794891)^3359544676530 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
                subst q
                change (2 : ZMod 43674080794891)^2569063576170 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
                  subst q
                  change (2 : ZMod 43674080794891)^2298635831310 ≠ 1
                  reduce_mod_char
                  decide
                · rcases hq.dvd_mul.mp hd with hd | hd
                  · have heq : q = 5521 := Nat.prime_eq_prime_of_dvd_pow hq prime_5521 hd
                    subst q
                    change (2 : ZMod 43674080794891)^7910538090 ≠ 1
                    reduce_mod_char
                    decide
                  · have heq : q = 8971 := Nat.prime_eq_prime_of_dvd_pow hq prime_8971 hd
                    subst q
                    change (2 : ZMod 43674080794891)^4868362590 ≠ 1
                    reduce_mod_char
                    decide

theorem prime_43948610607073 : Nat.Prime 43948610607073 := by
  apply lucas_primality 43948610607073 (5 : ZMod 43948610607073)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 43948610607073 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((157 : ℕ)^1 * ((2915911001 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 43948610607073)^21974305303536 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 43948610607073)^14649536869024 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
          subst q
          change (5 : ZMod 43948610607073)^279927456096 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2915911001 := Nat.prime_eq_prime_of_dvd_pow hq prime_2915911001 hd
          subst q
          change (5 : ZMod 43948610607073)^15072 ≠ 1
          reduce_mod_char
          decide

theorem prime_44052783896249 : Nat.Prime 44052783896249 := by
  apply lucas_primality 44052783896249 (3 : ZMod 44052783896249)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 44052783896249 - 1 = (2 : ℕ)^3 * ((53 : ℕ)^1 * ((103898075227 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 44052783896249)^22026391948124 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
        subst q
        change (3 : ZMod 44052783896249)^831184601816 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 103898075227 := Nat.prime_eq_prime_of_dvd_pow hq prime_103898075227 hd
        subst q
        change (3 : ZMod 44052783896249)^424 ≠ 1
        reduce_mod_char
        decide

theorem prime_44151665987623 : Nat.Prime 44151665987623 := by
  apply lucas_primality 44151665987623 (5 : ZMod 44151665987623)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 44151665987623 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7358610997937 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 44151665987623)^22075832993811 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 44151665987623)^14717221995874 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7358610997937 := Nat.prime_eq_prime_of_dvd_pow hq prime_7358610997937 hd
        subst q
        change (5 : ZMod 44151665987623)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_45579633110383 : Nat.Prime 45579633110383 := by
  apply lucas_primality 45579633110383 (3 : ZMod 45579633110383)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 45579633110383 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((17 : ℕ)^1 * ((63837021163 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 45579633110383)^22789816555191 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 45579633110383)^15193211036794 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 45579633110383)^6511376158626 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (3 : ZMod 45579633110383)^2681154888846 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 63837021163 := Nat.prime_eq_prime_of_dvd_pow hq prime_63837021163 hd
            subst q
            change (3 : ZMod 45579633110383)^714 ≠ 1
            reduce_mod_char
            decide

theorem prime_46083394808981 : Nat.Prime 46083394808981 := by
  apply lucas_primality 46083394808981 (2 : ZMod 46083394808981)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 46083394808981 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((23 : ℕ)^1 * ((29 : ℕ)^1 * ((1327 : ℕ)^1 * ((153133 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 46083394808981)^23041697404490 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 46083394808981)^9216678961796 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 46083394808981)^2710787929940 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (2 : ZMod 46083394808981)^2003625861260 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
              subst q
              change (2 : ZMod 46083394808981)^1589082579620 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 1327 := Nat.prime_eq_prime_of_dvd_pow hq prime_1327 hd
                subst q
                change (2 : ZMod 46083394808981)^34727501740 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 153133 := Nat.prime_eq_prime_of_dvd_pow hq prime_153133 hd
                subst q
                change (2 : ZMod 46083394808981)^300937060 ≠ 1
                reduce_mod_char
                decide

theorem prime_46554867177773 : Nat.Prime 46554867177773 := by
  apply lucas_primality 46554867177773 (2 : ZMod 46554867177773)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 46554867177773 - 1 = (2 : ℕ)^2 * ((1123 : ℕ)^1 * ((10363950841 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 46554867177773)^23277433588886 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1123 := Nat.prime_eq_prime_of_dvd_pow hq prime_1123 hd
        subst q
        change (2 : ZMod 46554867177773)^41455803364 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 10363950841 := Nat.prime_eq_prime_of_dvd_pow hq prime_10363950841 hd
        subst q
        change (2 : ZMod 46554867177773)^4492 ≠ 1
        reduce_mod_char
        decide

theorem prime_46856547084631 : Nat.Prime 46856547084631 := by
  apply lucas_primality 46856547084631 (7 : ZMod 46856547084631)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 46856547084631 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((211247 : ℕ)^1 * ((7393643 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 46856547084631)^23428273542315 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 46856547084631)^15618849028210 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 46856547084631)^9371309416926 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 211247 := Nat.prime_eq_prime_of_dvd_pow hq prime_211247 hd
            subst q
            change (7 : ZMod 46856547084631)^221809290 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 7393643 := Nat.prime_eq_prime_of_dvd_pow hq prime_7393643 hd
            subst q
            change (7 : ZMod 46856547084631)^6337410 ≠ 1
            reduce_mod_char
            decide

theorem prime_47045881000003 : Nat.Prime 47045881000003 := by
  apply lucas_primality 47045881000003 (2 : ZMod 47045881000003)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 47045881000003 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((43 : ℕ)^1 * ((179 : ℕ)^1 * ((5987 : ℕ)^1 * ((10009 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 47045881000003)^23522940500001 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 47045881000003)^15681960333334 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 47045881000003)^2767404764706 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (2 : ZMod 47045881000003)^1094090255814 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 179 := Nat.prime_eq_prime_of_dvd_pow hq prime_179 hd
              subst q
              change (2 : ZMod 47045881000003)^262826150838 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 5987 := Nat.prime_eq_prime_of_dvd_pow hq prime_5987 hd
                subst q
                change (2 : ZMod 47045881000003)^7858005846 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 10009 := Nat.prime_eq_prime_of_dvd_pow hq prime_10009 hd
                subst q
                change (2 : ZMod 47045881000003)^4700357778 ≠ 1
                reduce_mod_char
                decide

theorem prime_48551226272663 : Nat.Prime 48551226272663 := by
  apply lucas_primality 48551226272663 (5 : ZMod 48551226272663)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 48551226272663 - 1 = (2 : ℕ)^1 * ((293 : ℕ)^1 * ((82851921967 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 48551226272663)^24275613136331 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 293 := Nat.prime_eq_prime_of_dvd_pow hq prime_293 hd
        subst q
        change (5 : ZMod 48551226272663)^165703843934 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 82851921967 := Nat.prime_eq_prime_of_dvd_pow hq prime_82851921967 hd
        subst q
        change (5 : ZMod 48551226272663)^586 ≠ 1
        reduce_mod_char
        decide

theorem prime_49480252510417 : Nat.Prime 49480252510417 := by
  apply lucas_primality 49480252510417 (19 : ZMod 49480252510417)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 49480252510417 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((17 : ℕ)^1 * ((103 : ℕ)^1 * ((2011 : ℕ)^1 * ((3217 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 49480252510417)^24740126255208 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 49480252510417)^16493417503472 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (19 : ZMod 49480252510417)^7068607501488 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (19 : ZMod 49480252510417)^3806173270032 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
              subst q
              change (19 : ZMod 49480252510417)^2910603088848 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
                subst q
                change (19 : ZMod 49480252510417)^480390801072 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 2011 := Nat.prime_eq_prime_of_dvd_pow hq prime_2011 hd
                  subst q
                  change (19 : ZMod 49480252510417)^24604799856 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 3217 := Nat.prime_eq_prime_of_dvd_pow hq prime_3217 hd
                  subst q
                  change (19 : ZMod 49480252510417)^15380868048 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_49677914604427 : Nat.Prime 49677914604427 := by
  apply lucas_primality 49677914604427 (2 : ZMod 49677914604427)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 49677914604427 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((405487 : ℕ)^1 * ((20419033 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 49677914604427)^24838957302213 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 49677914604427)^16559304868142 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 405487 := Nat.prime_eq_prime_of_dvd_pow hq prime_405487 hd
          subst q
          change (2 : ZMod 49677914604427)^122514198 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 20419033 := Nat.prime_eq_prime_of_dvd_pow hq prime_20419033 hd
          subst q
          change (2 : ZMod 49677914604427)^2432922 ≠ 1
          reduce_mod_char
          decide

theorem prime_49731917813393 : Nat.Prime 49731917813393 := by
  apply lucas_primality 49731917813393 (3 : ZMod 49731917813393)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 49731917813393 - 1 = (2 : ℕ)^4 * ((1047391 : ℕ)^1 * ((2967607 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 49731917813393)^24865958906696 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1047391 := Nat.prime_eq_prime_of_dvd_pow hq prime_1047391 hd
        subst q
        change (3 : ZMod 49731917813393)^47481712 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2967607 := Nat.prime_eq_prime_of_dvd_pow hq prime_2967607 hd
        subst q
        change (3 : ZMod 49731917813393)^16758256 ≠ 1
        reduce_mod_char
        decide

theorem prime_50096498540567 : Nat.Prime 50096498540567 := by
  apply lucas_primality 50096498540567 (5 : ZMod 50096498540567)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 50096498540567 - 1 = (2 : ℕ)^1 * ((32839 : ℕ)^1 * ((762759197 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 50096498540567)^25048249270283 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 32839 := Nat.prime_eq_prime_of_dvd_pow hq prime_32839 hd
        subst q
        change (5 : ZMod 50096498540567)^1525518394 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 762759197 := Nat.prime_eq_prime_of_dvd_pow hq prime_762759197 hd
        subst q
        change (5 : ZMod 50096498540567)^65678 ≠ 1
        reduce_mod_char
        decide

theorem prime_50466742329617 : Nat.Prime 50466742329617 := by
  apply lucas_primality 50466742329617 (3 : ZMod 50466742329617)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 50466742329617 - 1 = (2 : ℕ)^4 * ((73 : ℕ)^1 * ((137 : ℕ)^1 * ((315385601 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 50466742329617)^25233371164808 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
        subst q
        change (3 : ZMod 50466742329617)^691325237392 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
          subst q
          change (3 : ZMod 50466742329617)^368370381968 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 315385601 := Nat.prime_eq_prime_of_dvd_pow hq prime_315385601 hd
          subst q
          change (3 : ZMod 50466742329617)^160016 ≠ 1
          reduce_mod_char
          decide

theorem prime_51682540549319 : Nat.Prime 51682540549319 := by
  apply lucas_primality 51682540549319 (7 : ZMod 51682540549319)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 51682540549319 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((19 : ℕ)^1 * ((79 : ℕ)^1 * ((2459433737 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 51682540549319)^25841270274659 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 51682540549319)^7383220078474 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (7 : ZMod 51682540549319)^2720133713122 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
            subst q
            change (7 : ZMod 51682540549319)^654209374042 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2459433737 := Nat.prime_eq_prime_of_dvd_pow hq prime_2459433737 hd
            subst q
            change (7 : ZMod 51682540549319)^21014 ≠ 1
            reduce_mod_char
            decide

theorem prime_52685583422597 : Nat.Prime 52685583422597 := by
  apply lucas_primality 52685583422597 (2 : ZMod 52685583422597)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 52685583422597 - 1 = (2 : ℕ)^2 * ((31 : ℕ)^2 * ((13705927009 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 52685583422597)^26342791711298 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (2 : ZMod 52685583422597)^1699534949116 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13705927009 := Nat.prime_eq_prime_of_dvd_pow hq prime_13705927009 hd
        subst q
        change (2 : ZMod 52685583422597)^3844 ≠ 1
        reduce_mod_char
        decide

theorem prime_53310208315537 : Nat.Prime 53310208315537 := by
  apply lucas_primality 53310208315537 (29 : ZMod 53310208315537)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 53310208315537 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((22543 : ℕ)^1 * ((16422383 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (29 : ZMod 53310208315537)^26655104157768 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (29 : ZMod 53310208315537)^17770069438512 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 22543 := Nat.prime_eq_prime_of_dvd_pow hq prime_22543 hd
          subst q
          change (29 : ZMod 53310208315537)^2364823152 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 16422383 := Nat.prime_eq_prime_of_dvd_pow hq prime_16422383 hd
          subst q
          change (29 : ZMod 53310208315537)^3246192 ≠ 1
          reduce_mod_char
          decide

theorem prime_54589214894051 : Nat.Prime 54589214894051 := by
  apply lucas_primality 54589214894051 (2 : ZMod 54589214894051)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 54589214894051 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((7841 : ℕ)^1 * ((9041 : ℕ)^1 * ((15401 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 54589214894051)^27294607447025 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 54589214894051)^10917842978810 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7841 := Nat.prime_eq_prime_of_dvd_pow hq prime_7841 hd
          subst q
          change (2 : ZMod 54589214894051)^6962022050 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 9041 := Nat.prime_eq_prime_of_dvd_pow hq prime_9041 hd
            subst q
            change (2 : ZMod 54589214894051)^6037962050 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 15401 := Nat.prime_eq_prime_of_dvd_pow hq prime_15401 hd
            subst q
            change (2 : ZMod 54589214894051)^3544524050 ≠ 1
            reduce_mod_char
            decide

theorem prime_54980371265627 : Nat.Prime 54980371265627 := by
  apply lucas_primality 54980371265627 (2 : ZMod 54980371265627)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 54980371265627 - 1 = (2 : ℕ)^1 * ((73 : ℕ)^1 * ((19013 : ℕ)^1 * ((19806337 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 54980371265627)^27490185632813 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
        subst q
        change (2 : ZMod 54980371265627)^753155770762 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19013 := Nat.prime_eq_prime_of_dvd_pow hq prime_19013 hd
          subst q
          change (2 : ZMod 54980371265627)^2891725202 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 19806337 := Nat.prime_eq_prime_of_dvd_pow hq prime_19806337 hd
          subst q
          change (2 : ZMod 54980371265627)^2775898 ≠ 1
          reduce_mod_char
          decide

theorem prime_55711021043729 : Nat.Prime 55711021043729 := by
  apply lucas_primality 55711021043729 (3 : ZMod 55711021043729)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 55711021043729 - 1 = (2 : ℕ)^4 * ((31 : ℕ)^1 * ((991 : ℕ)^1 * ((113340673 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 55711021043729)^27855510521864 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (3 : ZMod 55711021043729)^1797129711088 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 991 := Nat.prime_eq_prime_of_dvd_pow hq prime_991 hd
          subst q
          change (3 : ZMod 55711021043729)^56216973808 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 113340673 := Nat.prime_eq_prime_of_dvd_pow hq prime_113340673 hd
          subst q
          change (3 : ZMod 55711021043729)^491536 ≠ 1
          reduce_mod_char
          decide

theorem prime_56693912375311 : Nat.Prime 56693912375311 := by
  apply lucas_primality 56693912375311 (3 : ZMod 56693912375311)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 56693912375311 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((23 : ℕ)^1 * ((11737870057 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 56693912375311)^28346956187655 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 56693912375311)^18897970791770 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 56693912375311)^11338782475062 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (3 : ZMod 56693912375311)^8099130339330 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
              subst q
              change (3 : ZMod 56693912375311)^2464952711970 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 11737870057 := Nat.prime_eq_prime_of_dvd_pow hq prime_11737870057 hd
              subst q
              change (3 : ZMod 56693912375311)^4830 ≠ 1
              reduce_mod_char
              decide

theorem prime_58451728309157 : Nat.Prime 58451728309157 := by
  apply lucas_primality 58451728309157 (2 : ZMod 58451728309157)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 58451728309157 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((31 : ℕ)^1 * ((37 : ℕ)^1 * ((313 : ℕ)^1 * ((433 : ℕ)^1 * ((1033 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 58451728309157)^29225864154578 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 58451728309157)^8350246901308 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 58451728309157)^4496286793012 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (2 : ZMod 58451728309157)^1885539622876 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
              subst q
              change (2 : ZMod 58451728309157)^1579776440788 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 313 := Nat.prime_eq_prime_of_dvd_pow hq prime_313 hd
                subst q
                change (2 : ZMod 58451728309157)^186746735812 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 433 := Nat.prime_eq_prime_of_dvd_pow hq prime_433 hd
                  subst q
                  change (2 : ZMod 58451728309157)^134992444132 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 1033 := Nat.prime_eq_prime_of_dvd_pow hq prime_1033 hd
                  subst q
                  change (2 : ZMod 58451728309157)^56584441732 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_59424534917971 : Nat.Prime 59424534917971 := by
  apply lucas_primality 59424534917971 (3 : ZMod 59424534917971)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 59424534917971 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((227459 : ℕ)^1 * ((8708461 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 59424534917971)^29712267458985 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 59424534917971)^19808178305990 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 59424534917971)^11884906983594 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 227459 := Nat.prime_eq_prime_of_dvd_pow hq prime_227459 hd
            subst q
            change (3 : ZMod 59424534917971)^261253830 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 8708461 := Nat.prime_eq_prime_of_dvd_pow hq prime_8708461 hd
            subst q
            change (3 : ZMod 59424534917971)^6823770 ≠ 1
            reduce_mod_char
            decide

theorem prime_60241271212721 : Nat.Prime 60241271212721 := by
  apply lucas_primality 60241271212721 (3 : ZMod 60241271212721)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 60241271212721 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((57924299243 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 60241271212721)^30120635606360 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 60241271212721)^12048254242544 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 60241271212721)^4633943939440 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 57924299243 := Nat.prime_eq_prime_of_dvd_pow hq prime_57924299243 hd
          subst q
          change (3 : ZMod 60241271212721)^1040 ≠ 1
          reduce_mod_char
          decide

theorem prime_60254729561723 : Nat.Prime 60254729561723 := by
  apply lucas_primality 60254729561723 (2 : ZMod 60254729561723)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 60254729561723 - 1 = (2 : ℕ)^1 * ((79 : ℕ)^1 * ((283 : ℕ)^1 * ((4931 : ℕ)^1 * ((273283 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 60254729561723)^30127364780861 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
        subst q
        change (2 : ZMod 60254729561723)^762718095718 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 283 := Nat.prime_eq_prime_of_dvd_pow hq prime_283 hd
          subst q
          change (2 : ZMod 60254729561723)^212914238734 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 4931 := Nat.prime_eq_prime_of_dvd_pow hq prime_4931 hd
            subst q
            change (2 : ZMod 60254729561723)^12219576062 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 273283 := Nat.prime_eq_prime_of_dvd_pow hq prime_273283 hd
            subst q
            change (2 : ZMod 60254729561723)^220484734 ≠ 1
            reduce_mod_char
            decide

theorem prime_60558059143279 : Nat.Prime 60558059143279 := by
  apply lucas_primality 60558059143279 (11 : ZMod 60558059143279)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 60558059143279 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((17 : ℕ)^1 * ((23 : ℕ)^1 * ((47 : ℕ)^1 * ((2341 : ℕ)^1 * ((78203 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 60558059143279)^30279029571639 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 60558059143279)^20186019714426 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (11 : ZMod 60558059143279)^3562238773134 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (11 : ZMod 60558059143279)^2632959093186 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
              subst q
              change (11 : ZMod 60558059143279)^1288469343474 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 2341 := Nat.prime_eq_prime_of_dvd_pow hq prime_2341 hd
                subst q
                change (11 : ZMod 60558059143279)^25868457558 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 78203 := Nat.prime_eq_prime_of_dvd_pow hq prime_78203 hd
                subst q
                change (11 : ZMod 60558059143279)^774370026 ≠ 1
                reduce_mod_char
                decide

theorem prime_62103840598873 : Nat.Prime 62103840598873 := by
  apply lucas_primality 62103840598873 (5 : ZMod 62103840598873)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 62103840598873 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((862553341651 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 62103840598873)^31051920299436 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 62103840598873)^20701280199624 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 862553341651 := Nat.prime_eq_prime_of_dvd_pow hq prime_862553341651 hd
        subst q
        change (5 : ZMod 62103840598873)^72 ≠ 1
        reduce_mod_char
        decide

theorem prime_62344001901403 : Nat.Prime 62344001901403 := by
  apply lucas_primality 62344001901403 (3 : ZMod 62344001901403)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 62344001901403 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((13 : ℕ)^1 * ((257 : ℕ)^1 * ((601 : ℕ)^1 * ((1724929 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 62344001901403)^31172000950701 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 62344001901403)^20781333967134 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 62344001901403)^4795692453954 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 257 := Nat.prime_eq_prime_of_dvd_pow hq prime_257 hd
            subst q
            change (3 : ZMod 62344001901403)^242583664986 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 601 := Nat.prime_eq_prime_of_dvd_pow hq prime_601 hd
              subst q
              change (3 : ZMod 62344001901403)^103733780202 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1724929 := Nat.prime_eq_prime_of_dvd_pow hq prime_1724929 hd
              subst q
              change (3 : ZMod 62344001901403)^36142938 ≠ 1
              reduce_mod_char
              decide

theorem prime_62758488578969 : Nat.Prime 62758488578969 := by
  apply lucas_primality 62758488578969 (3 : ZMod 62758488578969)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 62758488578969 - 1 = (2 : ℕ)^3 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((23 : ℕ)^1 * ((383 : ℕ)^1 * ((2243 : ℕ)^1 * ((4363 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 62758488578969)^31379244289484 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 62758488578969)^8965498368424 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 62758488578969)^4827576044536 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (3 : ZMod 62758488578969)^2728629938216 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 383 := Nat.prime_eq_prime_of_dvd_pow hq prime_383 hd
              subst q
              change (3 : ZMod 62758488578969)^163860283496 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 2243 := Nat.prime_eq_prime_of_dvd_pow hq prime_2243 hd
                subst q
                change (3 : ZMod 62758488578969)^27979709576 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 4363 := Nat.prime_eq_prime_of_dvd_pow hq prime_4363 hd
                subst q
                change (3 : ZMod 62758488578969)^14384251336 ≠ 1
                reduce_mod_char
                decide

theorem prime_63026998143673 : Nat.Prime 63026998143673 := by
  apply lucas_primality 63026998143673 (15 : ZMod 63026998143673)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 63026998143673 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((2626124922653 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (15 : ZMod 63026998143673)^31513499071836 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (15 : ZMod 63026998143673)^21008999381224 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2626124922653 := Nat.prime_eq_prime_of_dvd_pow hq prime_2626124922653 hd
        subst q
        change (15 : ZMod 63026998143673)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_64000000000007 : Nat.Prime 64000000000007 := by
  apply lucas_primality 64000000000007 (5 : ZMod 64000000000007)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 64000000000007 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((4571428571429 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 64000000000007)^32000000000003 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 64000000000007)^9142857142858 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4571428571429 := Nat.prime_eq_prime_of_dvd_pow hq prime_4571428571429 hd
        subst q
        change (5 : ZMod 64000000000007)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_64898731470589 : Nat.Prime 64898731470589 := by
  apply lucas_primality 64898731470589 (6 : ZMod 64898731470589)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 64898731470589 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5408227622549 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 64898731470589)^32449365735294 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 64898731470589)^21632910490196 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5408227622549 := Nat.prime_eq_prime_of_dvd_pow hq prime_5408227622549 hd
        subst q
        change (6 : ZMod 64898731470589)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_65944160601211 : Nat.Prime 65944160601211 := by
  apply lucas_primality 65944160601211 (3 : ZMod 65944160601211)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 65944160601211 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((73 : ℕ)^1 * ((10037162953 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 65944160601211)^32972080300605 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 65944160601211)^21981386867070 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 65944160601211)^13188832120242 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
            subst q
            change (3 : ZMod 65944160601211)^903344665770 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 10037162953 := Nat.prime_eq_prime_of_dvd_pow hq prime_10037162953 hd
            subst q
            change (3 : ZMod 65944160601211)^6570 ≠ 1
            reduce_mod_char
            decide

theorem prime_66168227176757 : Nat.Prime 66168227176757 := by
  apply lucas_primality 66168227176757 (2 : ZMod 66168227176757)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 66168227176757 - 1 = (2 : ℕ)^2 * ((16542056794189 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 66168227176757)^33084113588378 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 16542056794189 := Nat.prime_eq_prime_of_dvd_pow hq prime_16542056794189 hd
      subst q
      change (2 : ZMod 66168227176757)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_67937289638527 : Nat.Prime 67937289638527 := by
  apply lucas_primality 67937289638527 (3 : ZMod 67937289638527)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 67937289638527 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((5446311499 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 67937289638527)^33968644819263 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 67937289638527)^22645763212842 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 67937289638527)^9705327091218 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (3 : ZMod 67937289638527)^6176117239866 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 5446311499 := Nat.prime_eq_prime_of_dvd_pow hq prime_5446311499 hd
            subst q
            change (3 : ZMod 67937289638527)^12474 ≠ 1
            reduce_mod_char
            decide

theorem prime_68342746855309 : Nat.Prime 68342746855309 := by
  apply lucas_primality 68342746855309 (10 : ZMod 68342746855309)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 68342746855309 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((31 : ℕ)^1 * ((113 : ℕ)^1 * ((95636159 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 68342746855309)^34171373427654 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 68342746855309)^22780915618436 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (10 : ZMod 68342746855309)^4020161579724 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (10 : ZMod 68342746855309)^2204604737268 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
              subst q
              change (10 : ZMod 68342746855309)^604803069516 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 95636159 := Nat.prime_eq_prime_of_dvd_pow hq prime_95636159 hd
              subst q
              change (10 : ZMod 68342746855309)^714612 ≠ 1
              reduce_mod_char
              decide

theorem prime_69980368892333 : Nat.Prime 69980368892333 := by
  apply lucas_primality 69980368892333 (2 : ZMod 69980368892333)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 69980368892333 - 1 = (2 : ℕ)^2 * ((67 : ℕ)^1 * ((261120779449 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 69980368892333)^34990184446166 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
        subst q
        change (2 : ZMod 69980368892333)^1044483117796 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 261120779449 := Nat.prime_eq_prime_of_dvd_pow hq prime_261120779449 hd
        subst q
        change (2 : ZMod 69980368892333)^268 ≠ 1
        reduce_mod_char
        decide

theorem prime_71419404000947 : Nat.Prime 71419404000947 := by
  apply lucas_primality 71419404000947 (2 : ZMod 71419404000947)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 71419404000947 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((31 : ℕ)^1 * ((497509 : ℕ)^1 * ((100669 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 71419404000947)^35709702000473 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (2 : ZMod 71419404000947)^3105191478302 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (2 : ZMod 71419404000947)^2303851741966 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 497509 := Nat.prime_eq_prime_of_dvd_pow hq prime_497509 hd
            subst q
            change (2 : ZMod 71419404000947)^143553994 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 100669 := Nat.prime_eq_prime_of_dvd_pow hq prime_100669 hd
            subst q
            change (2 : ZMod 71419404000947)^709447834 ≠ 1
            reduce_mod_char
            decide

theorem prime_72074394832901 : Nat.Prime 72074394832901 := by
  apply lucas_primality 72074394832901 (2 : ZMod 72074394832901)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 72074394832901 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((720743948329 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 72074394832901)^36037197416450 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 72074394832901)^14414878966580 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 720743948329 := Nat.prime_eq_prime_of_dvd_pow hq prime_720743948329 hd
        subst q
        change (2 : ZMod 72074394832901)^100 ≠ 1
        reduce_mod_char
        decide

theorem prime_73565070460183 : Nat.Prime 73565070460183 := by
  apply lucas_primality 73565070460183 (3 : ZMod 73565070460183)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 73565070460183 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^6 * ((7 : ℕ)^1 * ((64679 : ℕ)^1 * ((111443 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 73565070460183)^36782535230091 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 73565070460183)^24521690153394 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 73565070460183)^10509295780026 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 64679 := Nat.prime_eq_prime_of_dvd_pow hq prime_64679 hd
            subst q
            change (3 : ZMod 73565070460183)^1137387258 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 111443 := Nat.prime_eq_prime_of_dvd_pow hq prime_111443 hd
            subst q
            change (3 : ZMod 73565070460183)^660113874 ≠ 1
            reduce_mod_char
            decide

theorem prime_74220378765667 : Nat.Prime 74220378765667 := by
  apply lucas_primality 74220378765667 (3 : ZMod 74220378765667)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 74220378765667 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((41 : ℕ)^1 * ((677 : ℕ)^1 * ((63665089 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 74220378765667)^37110189382833 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 74220378765667)^24740126255222 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 74220378765667)^10602911252238 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (3 : ZMod 74220378765667)^1810253140626 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 677 := Nat.prime_eq_prime_of_dvd_pow hq prime_677 hd
              subst q
              change (3 : ZMod 74220378765667)^109631283258 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 63665089 := Nat.prime_eq_prime_of_dvd_pow hq prime_63665089 hd
              subst q
              change (3 : ZMod 74220378765667)^1165794 ≠ 1
              reduce_mod_char
              decide

theorem prime_76419346977859 : Nat.Prime 76419346977859 := by
  apply lucas_primality 76419346977859 (2 : ZMod 76419346977859)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 76419346977859 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((449 : ℕ)^1 * ((63611 : ℕ)^1 * ((445937 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 76419346977859)^38209673488929 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 76419346977859)^25473115659286 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 449 := Nat.prime_eq_prime_of_dvd_pow hq prime_449 hd
          subst q
          change (2 : ZMod 76419346977859)^170198991042 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 63611 := Nat.prime_eq_prime_of_dvd_pow hq prime_63611 hd
            subst q
            change (2 : ZMod 76419346977859)^1201354278 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 445937 := Nat.prime_eq_prime_of_dvd_pow hq prime_445937 hd
            subst q
            change (2 : ZMod 76419346977859)^171368034 ≠ 1
            reduce_mod_char
            decide

theorem prime_78672340886089 : Nat.Prime 78672340886089 := by
  apply lucas_primality 78672340886089 (13 : ZMod 78672340886089)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 78672340886089 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((184417 : ℕ)^1 * ((17775011 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 78672340886089)^39336170443044 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 78672340886089)^26224113628696 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 184417 := Nat.prime_eq_prime_of_dvd_pow hq prime_184417 hd
          subst q
          change (13 : ZMod 78672340886089)^426600264 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17775011 := Nat.prime_eq_prime_of_dvd_pow hq prime_17775011 hd
          subst q
          change (13 : ZMod 78672340886089)^4426008 ≠ 1
          reduce_mod_char
          decide

theorem prime_80980417183769 : Nat.Prime 80980417183769 := by
  apply lucas_primality 80980417183769 (3 : ZMod 80980417183769)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 80980417183769 - 1 = (2 : ℕ)^3 * ((173 : ℕ)^1 * ((136709 : ℕ)^1 * ((428003 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 80980417183769)^40490208591884 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
        subst q
        change (3 : ZMod 80980417183769)^468094897016 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 136709 := Nat.prime_eq_prime_of_dvd_pow hq prime_136709 hd
          subst q
          change (3 : ZMod 80980417183769)^592356152 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 428003 := Nat.prime_eq_prime_of_dvd_pow hq prime_428003 hd
          subst q
          change (3 : ZMod 80980417183769)^189205256 ≠ 1
          reduce_mod_char
          decide

theorem prime_83344647990323 : Nat.Prime 83344647990323 := by
  apply lucas_primality 83344647990323 (2 : ZMod 83344647990323)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 83344647990323 - 1 = (2 : ℕ)^1 * ((193 : ℕ)^1 * ((215918777177 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 83344647990323)^41672323995161 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
        subst q
        change (2 : ZMod 83344647990323)^431837554354 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 215918777177 := Nat.prime_eq_prime_of_dvd_pow hq prime_215918777177 hd
        subst q
        change (2 : ZMod 83344647990323)^386 ≠ 1
        reduce_mod_char
        decide

theorem prime_85766121000047 : Nat.Prime 85766121000047 := by
  apply lucas_primality 85766121000047 (5 : ZMod 85766121000047)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 85766121000047 - 1 = (2 : ℕ)^1 * ((157 : ℕ)^1 * ((273140512739 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 85766121000047)^42883060500023 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
        subst q
        change (5 : ZMod 85766121000047)^546281025478 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 273140512739 := Nat.prime_eq_prime_of_dvd_pow hq prime_273140512739 hd
        subst q
        change (5 : ZMod 85766121000047)^314 ≠ 1
        reduce_mod_char
        decide

theorem prime_87785680062527 : Nat.Prime 87785680062527 := by
  apply lucas_primality 87785680062527 (5 : ZMod 87785680062527)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 87785680062527 - 1 = (2 : ℕ)^1 * ((173 : ℕ)^1 * ((253715838331 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 87785680062527)^43892840031263 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
        subst q
        change (5 : ZMod 87785680062527)^507431676662 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 253715838331 := Nat.prime_eq_prime_of_dvd_pow hq prime_253715838331 hd
        subst q
        change (5 : ZMod 87785680062527)^346 ≠ 1
        reduce_mod_char
        decide

theorem prime_88245939632821 : Nat.Prime 88245939632821 := by
  apply lucas_primality 88245939632821 (2 : ZMod 88245939632821)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 88245939632821 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((263 : ℕ)^1 * ((17881 : ℕ)^1 * ((18397 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 88245939632821)^44122969816410 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 88245939632821)^29415313210940 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 88245939632821)^17649187926564 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (2 : ZMod 88245939632821)^5190937625460 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 263 := Nat.prime_eq_prime_of_dvd_pow hq prime_263 hd
              subst q
              change (2 : ZMod 88245939632821)^335535892140 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 17881 := Nat.prime_eq_prime_of_dvd_pow hq prime_17881 hd
                subst q
                change (2 : ZMod 88245939632821)^4935179220 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 18397 := Nat.prime_eq_prime_of_dvd_pow hq prime_18397 hd
                subst q
                change (2 : ZMod 88245939632821)^4796757060 ≠ 1
                reduce_mod_char
                decide

theorem prime_90785223184391 : Nat.Prime 90785223184391 := by
  apply lucas_primality 90785223184391 (7 : ZMod 90785223184391)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 90785223184391 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((317 : ℕ)^1 * ((727 : ℕ)^1 * ((5627603 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 90785223184391)^45392611592195 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 90785223184391)^18157044636878 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 90785223184391)^12969317597770 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 317 := Nat.prime_eq_prime_of_dvd_pow hq prime_317 hd
            subst q
            change (7 : ZMod 90785223184391)^286388716670 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 727 := Nat.prime_eq_prime_of_dvd_pow hq prime_727 hd
              subst q
              change (7 : ZMod 90785223184391)^124876510570 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 5627603 := Nat.prime_eq_prime_of_dvd_pow hq prime_5627603 hd
              subst q
              change (7 : ZMod 90785223184391)^16132130 ≠ 1
              reduce_mod_char
              decide

theorem prime_92810576221829 : Nat.Prime 92810576221829 := by
  apply lucas_primality 92810576221829 (2 : ZMod 92810576221829)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 92810576221829 - 1 = (2 : ℕ)^2 * ((83 : ℕ)^1 * ((151 : ℕ)^1 * ((1851324029 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 92810576221829)^46405288110914 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
        subst q
        change (2 : ZMod 92810576221829)^1118199713516 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
          subst q
          change (2 : ZMod 92810576221829)^614639577628 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1851324029 := Nat.prime_eq_prime_of_dvd_pow hq prime_1851324029 hd
          subst q
          change (2 : ZMod 92810576221829)^50132 ≠ 1
          reduce_mod_char
          decide

theorem prime_93385106978411 : Nat.Prime 93385106978411 := by
  apply lucas_primality 93385106978411 (2 : ZMod 93385106978411)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 93385106978411 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((349 : ℕ)^1 * ((23929 : ℕ)^1 * ((86017 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 93385106978411)^46692553489205 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 93385106978411)^18677021395682 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 93385106978411)^7183469767570 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 349 := Nat.prime_eq_prime_of_dvd_pow hq prime_349 hd
            subst q
            change (2 : ZMod 93385106978411)^267579103090 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 23929 := Nat.prime_eq_prime_of_dvd_pow hq prime_23929 hd
              subst q
              change (2 : ZMod 93385106978411)^3902591290 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 86017 := Nat.prime_eq_prime_of_dvd_pow hq prime_86017 hd
              subst q
              change (2 : ZMod 93385106978411)^1085658730 ≠ 1
              reduce_mod_char
              decide

theorem prime_96046742518357 : Nat.Prime 96046742518357 := by
  apply lucas_primality 96046742518357 (15 : ZMod 96046742518357)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 96046742518357 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((29 : ℕ)^1 * ((61 : ℕ)^1 * ((2801 : ℕ)^1 * ((230761 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (15 : ZMod 96046742518357)^48023371259178 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (15 : ZMod 96046742518357)^32015580839452 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (15 : ZMod 96046742518357)^13720963216908 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (15 : ZMod 96046742518357)^3311956638564 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
              subst q
              change (15 : ZMod 96046742518357)^1574536762596 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 2801 := Nat.prime_eq_prime_of_dvd_pow hq prime_2801 hd
                subst q
                change (15 : ZMod 96046742518357)^34290161556 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 230761 := Nat.prime_eq_prime_of_dvd_pow hq prime_230761 hd
                subst q
                change (15 : ZMod 96046742518357)^416217396 ≠ 1
                reduce_mod_char
                decide

theorem prime_97434333934057 : Nat.Prime 97434333934057 := by
  apply lucas_primality 97434333934057 (5 : ZMod 97434333934057)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 97434333934057 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((3169 : ℕ)^1 * ((61004131 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 97434333934057)^48717166967028 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 97434333934057)^32478111311352 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 97434333934057)^13919190562008 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3169 := Nat.prime_eq_prime_of_dvd_pow hq prime_3169 hd
            subst q
            change (5 : ZMod 97434333934057)^30746082024 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 61004131 := Nat.prime_eq_prime_of_dvd_pow hq prime_61004131 hd
            subst q
            change (5 : ZMod 97434333934057)^1597176 ≠ 1
            reduce_mod_char
            decide

theorem prime_98031197533741 : Nat.Prime 98031197533741 := by
  apply lucas_primality 98031197533741 (2 : ZMod 98031197533741)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 98031197533741 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((8219 : ℕ)^1 * ((198789791 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 98031197533741)^49015598766870 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 98031197533741)^32677065844580 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 98031197533741)^19606239506748 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 8219 := Nat.prime_eq_prime_of_dvd_pow hq prime_8219 hd
            subst q
            change (2 : ZMod 98031197533741)^11927387460 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 198789791 := Nat.prime_eq_prime_of_dvd_pow hq prime_198789791 hd
            subst q
            change (2 : ZMod 98031197533741)^493140 ≠ 1
            reduce_mod_char
            decide

theorem prime_98686358478121 : Nat.Prime 98686358478121 := by
  apply lucas_primality 98686358478121 (13 : ZMod 98686358478121)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 98686358478121 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^4 * ((1153 : ℕ)^1 * ((297067 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 98686358478121)^49343179239060 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 98686358478121)^32895452826040 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 98686358478121)^19737271695624 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (13 : ZMod 98686358478121)^14098051211160 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1153 := Nat.prime_eq_prime_of_dvd_pow hq prime_1153 hd
              subst q
              change (13 : ZMod 98686358478121)^85590944040 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 297067 := Nat.prime_eq_prime_of_dvd_pow hq prime_297067 hd
              subst q
              change (13 : ZMod 98686358478121)^332202360 ≠ 1
              reduce_mod_char
              decide

theorem prime_98771297640637 : Nat.Prime 98771297640637 := by
  apply lucas_primality 98771297640637 (2 : ZMod 98771297640637)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 98771297640637 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((37 : ℕ)^1 * ((222457877569 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 98771297640637)^49385648820318 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 98771297640637)^32923765880212 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (2 : ZMod 98771297640637)^2669494530828 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 222457877569 := Nat.prime_eq_prime_of_dvd_pow hq prime_222457877569 hd
          subst q
          change (2 : ZMod 98771297640637)^444 ≠ 1
          reduce_mod_char
          decide

theorem prime_100405934644619 : Nat.Prime 100405934644619 := by
  apply lucas_primality 100405934644619 (2 : ZMod 100405934644619)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 100405934644619 - 1 = (2 : ℕ)^1 * ((37 : ℕ)^1 * ((6701 : ℕ)^1 * ((202482757 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 100405934644619)^50202967322309 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (2 : ZMod 100405934644619)^2713673909314 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 6701 := Nat.prime_eq_prime_of_dvd_pow hq prime_6701 hd
          subst q
          change (2 : ZMod 100405934644619)^14983724018 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 202482757 := Nat.prime_eq_prime_of_dvd_pow hq prime_202482757 hd
          subst q
          change (2 : ZMod 100405934644619)^495874 ≠ 1
          reduce_mod_char
          decide

theorem prime_100466574830051 : Nat.Prime 100466574830051 := by
  apply lucas_primality 100466574830051 (2 : ZMod 100466574830051)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 100466574830051 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((131 : ℕ)^1 * ((199 : ℕ)^1 * ((539003 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 100466574830051)^50233287415025 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 100466574830051)^20093314966010 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 100466574830051)^9133324984550 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (2 : ZMod 100466574830051)^7728198063850 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
              subst q
              change (2 : ZMod 100466574830051)^766920418550 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 199 := Nat.prime_eq_prime_of_dvd_pow hq prime_199 hd
                subst q
                change (2 : ZMod 100466574830051)^504857159950 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 539003 := Nat.prime_eq_prime_of_dvd_pow hq prime_539003 hd
                subst q
                change (2 : ZMod 100466574830051)^186393350 ≠ 1
                reduce_mod_char
                decide

theorem prime_101559956668421 : Nat.Prime 101559956668421 := by
  apply lucas_primality 101559956668421 (2 : ZMod 101559956668421)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 101559956668421 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((5077997833421 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 101559956668421)^50779978334210 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 101559956668421)^20311991333684 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5077997833421 := Nat.prime_eq_prime_of_dvd_pow hq prime_5077997833421 hd
        subst q
        change (2 : ZMod 101559956668421)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_104413920566027 : Nat.Prime 104413920566027 := by
  apply lucas_primality 104413920566027 (2 : ZMod 104413920566027)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 104413920566027 - 1 = (2 : ℕ)^1 * ((449 : ℕ)^1 * ((33997 : ℕ)^1 * ((3420121 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 104413920566027)^52206960283013 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 449 := Nat.prime_eq_prime_of_dvd_pow hq prime_449 hd
        subst q
        change (2 : ZMod 104413920566027)^232547707274 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 33997 := Nat.prime_eq_prime_of_dvd_pow hq prime_33997 hd
          subst q
          change (2 : ZMod 104413920566027)^3071268658 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3420121 := Nat.prime_eq_prime_of_dvd_pow hq prime_3420121 hd
          subst q
          change (2 : ZMod 104413920566027)^30529306 ≠ 1
          reduce_mod_char
          decide

theorem prime_106137297310193 : Nat.Prime 106137297310193 := by
  apply lucas_primality 106137297310193 (3 : ZMod 106137297310193)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 106137297310193 - 1 = (2 : ℕ)^4 * ((1499 : ℕ)^1 * ((4425337613 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 106137297310193)^53068648655096 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1499 := Nat.prime_eq_prime_of_dvd_pow hq prime_1499 hd
        subst q
        change (3 : ZMod 106137297310193)^70805401808 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4425337613 := Nat.prime_eq_prime_of_dvd_pow hq prime_4425337613 hd
        subst q
        change (3 : ZMod 106137297310193)^23984 ≠ 1
        reduce_mod_char
        decide

theorem prime_106267408103699 : Nat.Prime 106267408103699 := by
  apply lucas_primality 106267408103699 (2 : ZMod 106267408103699)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 106267408103699 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((1759 : ℕ)^1 * ((1589829869 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 106267408103699)^53133704051849 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 106267408103699)^5593021479142 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1759 := Nat.prime_eq_prime_of_dvd_pow hq prime_1759 hd
          subst q
          change (2 : ZMod 106267408103699)^60413535022 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1589829869 := Nat.prime_eq_prime_of_dvd_pow hq prime_1589829869 hd
          subst q
          change (2 : ZMod 106267408103699)^66842 ≠ 1
          reduce_mod_char
          decide

theorem prime_106617765127483 : Nat.Prime 106617765127483 := by
  apply lucas_primality 106617765127483 (2 : ZMod 106617765127483)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 106617765127483 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((846172739107 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 106617765127483)^53308882563741 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 106617765127483)^35539255042494 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 106617765127483)^15231109303926 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 846172739107 := Nat.prime_eq_prime_of_dvd_pow hq prime_846172739107 hd
          subst q
          change (2 : ZMod 106617765127483)^126 ≠ 1
          reduce_mod_char
          decide

theorem prime_107334407093887 : Nat.Prime 107334407093887 := by
  apply lucas_primality 107334407093887 (3 : ZMod 107334407093887)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 107334407093887 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((851860373761 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 107334407093887)^53667203546943 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 107334407093887)^35778135697962 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 107334407093887)^15333486727698 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 851860373761 := Nat.prime_eq_prime_of_dvd_pow hq prime_851860373761 hd
          subst q
          change (3 : ZMod 107334407093887)^126 ≠ 1
          reduce_mod_char
          decide

theorem prime_109445971509307 : Nat.Prime 109445971509307 := by
  apply lucas_primality 109445971509307 (14 : ZMod 109445971509307)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 109445971509307 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((541 : ℕ)^1 * ((5393 : ℕ)^1 * ((2084009 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 109445971509307)^54722985754653 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 109445971509307)^36481990503102 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 541 := Nat.prime_eq_prime_of_dvd_pow hq prime_541 hd
          subst q
          change (14 : ZMod 109445971509307)^202303089666 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 5393 := Nat.prime_eq_prime_of_dvd_pow hq prime_5393 hd
            subst q
            change (14 : ZMod 109445971509307)^20294079642 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2084009 := Nat.prime_eq_prime_of_dvd_pow hq prime_2084009 hd
            subst q
            change (14 : ZMod 109445971509307)^52517034 ≠ 1
            reduce_mod_char
            decide

theorem prime_110322650964683 : Nat.Prime 110322650964683 := by
  apply lucas_primality 110322650964683 (2 : ZMod 110322650964683)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 110322650964683 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((23981 : ℕ)^1 * ((176939197 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 110322650964683)^55161325482341 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 110322650964683)^8486357766514 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23981 := Nat.prime_eq_prime_of_dvd_pow hq prime_23981 hd
          subst q
          change (2 : ZMod 110322650964683)^4600419122 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 176939197 := Nat.prime_eq_prime_of_dvd_pow hq prime_176939197 hd
          subst q
          change (2 : ZMod 110322650964683)^623506 ≠ 1
          reduce_mod_char
          decide

theorem prime_111422042087459 : Nat.Prime 111422042087459 := by
  apply lucas_primality 111422042087459 (2 : ZMod 111422042087459)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 111422042087459 - 1 = (2 : ℕ)^1 * ((55711021043729 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 111422042087459)^55711021043729 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 55711021043729 := Nat.prime_eq_prime_of_dvd_pow hq prime_55711021043729 hd
      subst q
      change (2 : ZMod 111422042087459)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_113379904000003 : Nat.Prime 113379904000003 := by
  apply lucas_primality 113379904000003 (2 : ZMod 113379904000003)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 113379904000003 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((89 : ℕ)^1 * ((137 : ℕ)^1 * ((1549795019 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 113379904000003)^56689952000001 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 113379904000003)^37793301333334 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (2 : ZMod 113379904000003)^1273931505618 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
            subst q
            change (2 : ZMod 113379904000003)^827590540146 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1549795019 := Nat.prime_eq_prime_of_dvd_pow hq prime_1549795019 hd
            subst q
            change (2 : ZMod 113379904000003)^73158 ≠ 1
            reduce_mod_char
            decide

theorem prime_114924911015051 : Nat.Prime 114924911015051 := by
  apply lucas_primality 114924911015051 (2 : ZMod 114924911015051)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 114924911015051 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((241037 : ℕ)^1 * ((9535873 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 114924911015051)^57462455507525 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 114924911015051)^22984982203010 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 241037 := Nat.prime_eq_prime_of_dvd_pow hq prime_241037 hd
          subst q
          change (2 : ZMod 114924911015051)^476793650 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 9535873 := Nat.prime_eq_prime_of_dvd_pow hq prime_9535873 hd
          subst q
          change (2 : ZMod 114924911015051)^12051850 ≠ 1
          reduce_mod_char
          decide

theorem prime_116507435287343 : Nat.Prime 116507435287343 := by
  apply lucas_primality 116507435287343 (5 : ZMod 116507435287343)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 116507435287343 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((5295792513061 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 116507435287343)^58253717643671 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 116507435287343)^10591585026122 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5295792513061 := Nat.prime_eq_prime_of_dvd_pow hq prime_5295792513061 hd
        subst q
        change (5 : ZMod 116507435287343)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_119706531338309 : Nat.Prime 119706531338309 := by
  apply lucas_primality 119706531338309 (2 : ZMod 119706531338309)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 119706531338309 - 1 = (2 : ℕ)^2 * ((53 : ℕ)^1 * ((509 : ℕ)^1 * ((1109338801 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 119706531338309)^59853265669154 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
        subst q
        change (2 : ZMod 119706531338309)^2258613798836 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 509 := Nat.prime_eq_prime_of_dvd_pow hq prime_509 hd
          subst q
          change (2 : ZMod 119706531338309)^235179825812 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1109338801 := Nat.prime_eq_prime_of_dvd_pow hq prime_1109338801 hd
          subst q
          change (2 : ZMod 119706531338309)^107908 ≠ 1
          reduce_mod_char
          decide

theorem prime_121909124982529 : Nat.Prime 121909124982529 := by
  apply lucas_primality 121909124982529 (7 : ZMod 121909124982529)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 121909124982529 - 1 = (2 : ℕ)^8 * ((3 : ℕ)^2 * ((13 : ℕ)^1 * ((29 : ℕ)^1 * ((37 : ℕ)^1 * ((487 : ℕ)^1 * ((7789 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 121909124982529)^60954562491264 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 121909124982529)^40636374994176 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (7 : ZMod 121909124982529)^9377624998656 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (7 : ZMod 121909124982529)^4203762930432 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
              subst q
              change (7 : ZMod 121909124982529)^3294841215744 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 487 := Nat.prime_eq_prime_of_dvd_pow hq prime_487 hd
                subst q
                change (7 : ZMod 121909124982529)^250326745344 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 7789 := Nat.prime_eq_prime_of_dvd_pow hq prime_7789 hd
                subst q
                change (7 : ZMod 121909124982529)^15651447552 ≠ 1
                reduce_mod_char
                decide

theorem prime_122978496247511 : Nat.Prime 122978496247511 := by
  apply lucas_primality 122978496247511 (7 : ZMod 122978496247511)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 122978496247511 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((18433 : ℕ)^1 * ((39244991 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 122978496247511)^61489248123755 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 122978496247511)^24595699249502 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (7 : ZMod 122978496247511)^7234029191030 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 18433 := Nat.prime_eq_prime_of_dvd_pow hq prime_18433 hd
            subst q
            change (7 : ZMod 122978496247511)^6671648470 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 39244991 := Nat.prime_eq_prime_of_dvd_pow hq prime_39244991 hd
            subst q
            change (7 : ZMod 122978496247511)^3133610 ≠ 1
            reduce_mod_char
            decide

theorem prime_123008075595337 : Nat.Prime 123008075595337 := by
  apply lucas_primality 123008075595337 (10 : ZMod 123008075595337)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 123008075595337 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((426889 : ℕ)^1 * ((12006251 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 123008075595337)^61504037797668 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 123008075595337)^41002691865112 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 426889 := Nat.prime_eq_prime_of_dvd_pow hq prime_426889 hd
          subst q
          change (10 : ZMod 123008075595337)^288150024 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 12006251 := Nat.prime_eq_prime_of_dvd_pow hq prime_12006251 hd
          subst q
          change (10 : ZMod 123008075595337)^10245336 ≠ 1
          reduce_mod_char
          decide

theorem prime_126324651851869 : Nat.Prime 126324651851869 := by
  apply lucas_primality 126324651851869 (6 : ZMod 126324651851869)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 126324651851869 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((10527054320989 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 126324651851869)^63162325925934 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 126324651851869)^42108217283956 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 10527054320989 := Nat.prime_eq_prime_of_dvd_pow hq prime_10527054320989 hd
        subst q
        change (6 : ZMod 126324651851869)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_129746337890647 : Nat.Prime 129746337890647 := by
  apply lucas_primality 129746337890647 (3 : ZMod 129746337890647)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 129746337890647 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((21624389648441 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 129746337890647)^64873168945323 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 129746337890647)^43248779296882 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 21624389648441 := Nat.prime_eq_prime_of_dvd_pow hq prime_21624389648441 hd
        subst q
        change (3 : ZMod 129746337890647)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_131366515875869 : Nat.Prime 131366515875869 := by
  apply lucas_primality 131366515875869 (10 : ZMod 131366515875869)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 131366515875869 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((61 : ℕ)^1 * ((67 : ℕ)^1 * ((103 : ℕ)^1 * ((661 : ℕ)^1 * ((1297 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 131366515875869)^65683257937934 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (10 : ZMod 131366515875869)^18766645125124 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (10 : ZMod 131366515875869)^10105116605836 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
            subst q
            change (10 : ZMod 131366515875869)^2153549440588 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
              subst q
              change (10 : ZMod 131366515875869)^1960694266804 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
                subst q
                change (10 : ZMod 131366515875869)^1275403066756 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 661 := Nat.prime_eq_prime_of_dvd_pow hq prime_661 hd
                  subst q
                  change (10 : ZMod 131366515875869)^198739055788 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 1297 := Nat.prime_eq_prime_of_dvd_pow hq prime_1297 hd
                  subst q
                  change (10 : ZMod 131366515875869)^101284900444 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_133244912167001 : Nat.Prime 133244912167001 := by
  apply lucas_primality 133244912167001 (6 : ZMod 133244912167001)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 133244912167001 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^3 * ((133244912167 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 133244912167001)^66622456083500 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 133244912167001)^26648982433400 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 133244912167 := Nat.prime_eq_prime_of_dvd_pow hq prime_133244912167 hd
        subst q
        change (6 : ZMod 133244912167001)^1000 ≠ 1
        reduce_mod_char
        decide

theorem prime_136421052631579 : Nat.Prime 136421052631579 := by
  apply lucas_primality 136421052631579 (2 : ZMod 136421052631579)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 136421052631579 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((19 : ℕ)^1 * ((2557 : ℕ)^1 * ((1090909 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 136421052631579)^68210526315789 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 136421052631579)^45473684210526 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 136421052631579)^12401913875598 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (2 : ZMod 136421052631579)^10493927125506 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
              subst q
              change (2 : ZMod 136421052631579)^7180055401662 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 2557 := Nat.prime_eq_prime_of_dvd_pow hq prime_2557 hd
                subst q
                change (2 : ZMod 136421052631579)^53351995554 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 1090909 := Nat.prime_eq_prime_of_dvd_pow hq prime_1090909 hd
                subst q
                change (2 : ZMod 136421052631579)^125052642 ≠ 1
                reduce_mod_char
                decide

theorem prime_136821750708899 : Nat.Prime 136821750708899 := by
  apply lucas_primality 136821750708899 (2 : ZMod 136821750708899)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 136821750708899 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((61 : ℕ)^1 * ((101 : ℕ)^1 * ((11981 : ℕ)^1 * ((54517 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 136821750708899)^68410875354449 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 136821750708899)^8048338276994 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (2 : ZMod 136821750708899)^2242979519818 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
            subst q
            change (2 : ZMod 136821750708899)^1354670799098 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 11981 := Nat.prime_eq_prime_of_dvd_pow hq prime_11981 hd
              subst q
              change (2 : ZMod 136821750708899)^11419894058 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 54517 := Nat.prime_eq_prime_of_dvd_pow hq prime_54517 hd
              subst q
              change (2 : ZMod 136821750708899)^2509707994 ≠ 1
              reduce_mod_char
              decide

theorem prime_140478247932023 : Nat.Prime 140478247932023 := by
  apply lucas_primality 140478247932023 (10 : ZMod 140478247932023)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 140478247932023 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((71 : ℕ)^1 * ((988295141 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 140478247932023)^70239123966011 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (10 : ZMod 140478247932023)^20068321133146 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (10 : ZMod 140478247932023)^12770749812002 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (10 : ZMod 140478247932023)^10806019071694 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
              subst q
              change (10 : ZMod 140478247932023)^1978566872282 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 988295141 := Nat.prime_eq_prime_of_dvd_pow hq prime_988295141 hd
              subst q
              change (10 : ZMod 140478247932023)^142142 ≠ 1
              reduce_mod_char
              decide

theorem prime_144215816802149 : Nat.Prime 144215816802149 := by
  apply lucas_primality 144215816802149 (2 : ZMod 144215816802149)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 144215816802149 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((61 : ℕ)^1 * ((67 : ℕ)^1 * ((73 : ℕ)^1 * ((709 : ℕ)^1 * ((1873 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 144215816802149)^72107908401074 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 144215816802149)^20602259543164 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 144215816802149)^11093524369396 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
            subst q
            change (2 : ZMod 144215816802149)^2364193718068 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
              subst q
              change (2 : ZMod 144215816802149)^2152474877644 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
                subst q
                change (2 : ZMod 144215816802149)^1975559134276 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 709 := Nat.prime_eq_prime_of_dvd_pow hq prime_709 hd
                  subst q
                  change (2 : ZMod 144215816802149)^203407357972 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 1873 := Nat.prime_eq_prime_of_dvd_pow hq prime_1873 hd
                  subst q
                  change (2 : ZMod 144215816802149)^76997232676 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_148035889000037 : Nat.Prime 148035889000037 := by
  apply lucas_primality 148035889000037 (2 : ZMod 148035889000037)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 148035889000037 - 1 = (2 : ℕ)^2 * ((461 : ℕ)^1 * ((80279766269 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 148035889000037)^74017944500018 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 461 := Nat.prime_eq_prime_of_dvd_pow hq prime_461 hd
        subst q
        change (2 : ZMod 148035889000037)^321119065076 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 80279766269 := Nat.prime_eq_prime_of_dvd_pow hq prime_80279766269 hd
        subst q
        change (2 : ZMod 148035889000037)^1844 ≠ 1
        reduce_mod_char
        decide

theorem prime_151939915084883 : Nat.Prime 151939915084883 := by
  apply lucas_primality 151939915084883 (2 : ZMod 151939915084883)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 151939915084883 - 1 = (2 : ℕ)^1 * ((26681 : ℕ)^1 * ((2847342961 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 151939915084883)^75969957542441 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 26681 := Nat.prime_eq_prime_of_dvd_pow hq prime_26681 hd
        subst q
        change (2 : ZMod 151939915084883)^5694685922 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2847342961 := Nat.prime_eq_prime_of_dvd_pow hq prime_2847342961 hd
        subst q
        change (2 : ZMod 151939915084883)^53362 ≠ 1
        reduce_mod_char
        decide

theorem prime_154580528914657 : Nat.Prime 154580528914657 := by
  apply lucas_primality 154580528914657 (5 : ZMod 154580528914657)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 154580528914657 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((123862603297 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 154580528914657)^77290264457328 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 154580528914657)^51526842971552 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (5 : ZMod 154580528914657)^11890809916512 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 123862603297 := Nat.prime_eq_prime_of_dvd_pow hq prime_123862603297 hd
          subst q
          change (5 : ZMod 154580528914657)^1248 ≠ 1
          reduce_mod_char
          decide

theorem prime_155929364660243 : Nat.Prime 155929364660243 := by
  apply lucas_primality 155929364660243 (2 : ZMod 155929364660243)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 155929364660243 - 1 = (2 : ℕ)^1 * ((347 : ℕ)^1 * ((401 : ℕ)^1 * ((3089 : ℕ)^1 * ((181387 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 155929364660243)^77964682330121 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 347 := Nat.prime_eq_prime_of_dvd_pow hq prime_347 hd
        subst q
        change (2 : ZMod 155929364660243)^449364163286 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 401 := Nat.prime_eq_prime_of_dvd_pow hq prime_401 hd
          subst q
          change (2 : ZMod 155929364660243)^388851283442 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3089 := Nat.prime_eq_prime_of_dvd_pow hq prime_3089 hd
            subst q
            change (2 : ZMod 155929364660243)^50478913778 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 181387 := Nat.prime_eq_prime_of_dvd_pow hq prime_181387 hd
            subst q
            change (2 : ZMod 155929364660243)^859650166 ≠ 1
            reduce_mod_char
            decide

theorem prime_160005726539591 : Nat.Prime 160005726539591 := by
  apply lucas_primality 160005726539591 (7 : ZMod 160005726539591)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 160005726539591 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((16000572653959 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 160005726539591)^80002863269795 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 160005726539591)^32001145307918 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 16000572653959 := Nat.prime_eq_prime_of_dvd_pow hq prime_16000572653959 hd
        subst q
        change (7 : ZMod 160005726539591)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_164170508913247 : Nat.Prime 164170508913247 := by
  apply lucas_primality 164170508913247 (3 : ZMod 164170508913247)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 164170508913247 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((2487431953231 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 164170508913247)^82085254456623 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 164170508913247)^54723502971082 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 164170508913247)^14924591719386 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2487431953231 := Nat.prime_eq_prime_of_dvd_pow hq prime_2487431953231 hd
          subst q
          change (3 : ZMod 164170508913247)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_165852463492979 : Nat.Prime 165852463492979 := by
  apply lucas_primality 165852463492979 (2 : ZMod 165852463492979)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 165852463492979 - 1 = (2 : ℕ)^1 * ((10069 : ℕ)^1 * ((8235796181 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 165852463492979)^82926231746489 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 10069 := Nat.prime_eq_prime_of_dvd_pow hq prime_10069 hd
        subst q
        change (2 : ZMod 165852463492979)^16471592362 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 8235796181 := Nat.prime_eq_prime_of_dvd_pow hq prime_8235796181 hd
        subst q
        change (2 : ZMod 165852463492979)^20138 ≠ 1
        reduce_mod_char
        decide

theorem prime_168425239515629 : Nat.Prime 168425239515629 := by
  apply lucas_primality 168425239515629 (2 : ZMod 168425239515629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 168425239515629 - 1 = (2 : ℕ)^2 * ((193 : ℕ)^1 * ((218167408699 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 168425239515629)^84212619757814 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
        subst q
        change (2 : ZMod 168425239515629)^872669634796 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 218167408699 := Nat.prime_eq_prime_of_dvd_pow hq prime_218167408699 hd
        subst q
        change (2 : ZMod 168425239515629)^772 ≠ 1
        reduce_mod_char
        decide

theorem prime_168905955973343 : Nat.Prime 168905955973343 := by
  apply lucas_primality 168905955973343 (7 : ZMod 168905955973343)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 168905955973343 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((12064711140953 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 168905955973343)^84452977986671 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 168905955973343)^24129422281906 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 12064711140953 := Nat.prime_eq_prime_of_dvd_pow hq prime_12064711140953 hd
        subst q
        change (7 : ZMod 168905955973343)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_172771465793579 : Nat.Prime 172771465793579 := by
  apply lucas_primality 172771465793579 (2 : ZMod 172771465793579)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 172771465793579 - 1 = (2 : ℕ)^1 * ((67 : ℕ)^1 * ((419 : ℕ)^1 * ((3077182093 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 172771465793579)^86385732896789 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
        subst q
        change (2 : ZMod 172771465793579)^2578678593934 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 419 := Nat.prime_eq_prime_of_dvd_pow hq prime_419 hd
          subst q
          change (2 : ZMod 172771465793579)^412342400462 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3077182093 := Nat.prime_eq_prime_of_dvd_pow hq prime_3077182093 hd
          subst q
          change (2 : ZMod 172771465793579)^56146 ≠ 1
          reduce_mod_char
          decide

theorem prime_177210755074831 : Nat.Prime 177210755074831 := by
  apply lucas_primality 177210755074831 (6 : ZMod 177210755074831)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 177210755074831 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((173 : ℕ)^1 * ((34144654157 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 177210755074831)^88605377537415 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 177210755074831)^59070251691610 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 177210755074831)^35442151014966 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
            subst q
            change (6 : ZMod 177210755074831)^1024339624710 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 34144654157 := Nat.prime_eq_prime_of_dvd_pow hq prime_34144654157 hd
            subst q
            change (6 : ZMod 177210755074831)^5190 ≠ 1
            reduce_mod_char
            decide

theorem prime_181744694737997 : Nat.Prime 181744694737997 := by
  apply lucas_primality 181744694737997 (5 : ZMod 181744694737997)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 181744694737997 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((112663 : ℕ)^1 * ((31022521 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 181744694737997)^90872347368998 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (5 : ZMod 181744694737997)^13980361133692 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 112663 := Nat.prime_eq_prime_of_dvd_pow hq prime_112663 hd
          subst q
          change (5 : ZMod 181744694737997)^1613171092 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 31022521 := Nat.prime_eq_prime_of_dvd_pow hq prime_31022521 hd
          subst q
          change (5 : ZMod 181744694737997)^5858476 ≠ 1
          reduce_mod_char
          decide

theorem prime_182977400695021 : Nat.Prime 182977400695021 := by
  apply lucas_primality 182977400695021 (2 : ZMod 182977400695021)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 182977400695021 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((3049623344917 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 182977400695021)^91488700347510 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 182977400695021)^60992466898340 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 182977400695021)^36595480139004 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3049623344917 := Nat.prime_eq_prime_of_dvd_pow hq prime_3049623344917 hd
          subst q
          change (2 : ZMod 182977400695021)^60 ≠ 1
          reduce_mod_char
          decide

theorem prime_186374892382573 : Nat.Prime 186374892382573 := by
  apply lucas_primality 186374892382573 (2 : ZMod 186374892382573)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 186374892382573 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((467 : ℕ)^1 * ((33257475443 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 186374892382573)^93187446191286 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 186374892382573)^62124964127524 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 467 := Nat.prime_eq_prime_of_dvd_pow hq prime_467 hd
          subst q
          change (2 : ZMod 186374892382573)^399089705316 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 33257475443 := Nat.prime_eq_prime_of_dvd_pow hq prime_33257475443 hd
          subst q
          change (2 : ZMod 186374892382573)^5604 ≠ 1
          reduce_mod_char
          decide

theorem prime_191102976000007 : Nat.Prime 191102976000007 := by
  apply lucas_primality 191102976000007 (3 : ZMod 191102976000007)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 191102976000007 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((53 : ℕ)^1 * ((12264341933 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 191102976000007)^95551488000003 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 191102976000007)^63700992000002 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 191102976000007)^27300425142858 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
            subst q
            change (3 : ZMod 191102976000007)^3605716528302 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 12264341933 := Nat.prime_eq_prime_of_dvd_pow hq prime_12264341933 hd
            subst q
            change (3 : ZMod 191102976000007)^15582 ≠ 1
            reduce_mod_char
            decide

theorem prime_195930594145549 : Nat.Prime 195930594145549 := by
  apply lucas_primality 195930594145549 (6 : ZMod 195930594145549)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 195930594145549 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5442516504043 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 195930594145549)^97965297072774 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 195930594145549)^65310198048516 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5442516504043 := Nat.prime_eq_prime_of_dvd_pow hq prime_5442516504043 hd
        subst q
        change (6 : ZMod 195930594145549)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_200859416110169 : Nat.Prime 200859416110169 := by
  apply lucas_primality 200859416110169 (3 : ZMod 200859416110169)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 200859416110169 - 1 = (2 : ℕ)^3 * ((10399 : ℕ)^1 * ((2414407829 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 200859416110169)^100429708055084 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 10399 := Nat.prime_eq_prime_of_dvd_pow hq prime_10399 hd
        subst q
        change (3 : ZMod 200859416110169)^19315262632 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2414407829 := Nat.prime_eq_prime_of_dvd_pow hq prime_2414407829 hd
        subst q
        change (3 : ZMod 200859416110169)^83192 ≠ 1
        reduce_mod_char
        decide

theorem prime_202386922327973 : Nat.Prime 202386922327973 := by
  apply lucas_primality 202386922327973 (2 : ZMod 202386922327973)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 202386922327973 - 1 = (2 : ℕ)^2 * ((17 : ℕ)^1 * ((23 : ℕ)^1 * ((406631 : ℕ)^1 * ((318233 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 202386922327973)^101193461163986 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 202386922327973)^11905113078116 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 202386922327973)^8799431405564 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 406631 := Nat.prime_eq_prime_of_dvd_pow hq prime_406631 hd
            subst q
            change (2 : ZMod 202386922327973)^497716412 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 318233 := Nat.prime_eq_prime_of_dvd_pow hq prime_318233 hd
            subst q
            change (2 : ZMod 202386922327973)^635970884 ≠ 1
            reduce_mod_char
            decide

theorem prime_202559010445369 : Nat.Prime 202559010445369 := by
  apply lucas_primality 202559010445369 (13 : ZMod 202559010445369)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 202559010445369 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((2813319589519 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 202559010445369)^101279505222684 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 202559010445369)^67519670148456 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2813319589519 := Nat.prime_eq_prime_of_dvd_pow hq prime_2813319589519 hd
        subst q
        change (13 : ZMod 202559010445369)^72 ≠ 1
        reduce_mod_char
        decide

theorem prime_204994552401733 : Nat.Prime 204994552401733 := by
  apply lucas_primality 204994552401733 (5 : ZMod 204994552401733)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 204994552401733 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((17082879366811 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 204994552401733)^102497276200866 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 204994552401733)^68331517467244 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 17082879366811 := Nat.prime_eq_prime_of_dvd_pow hq prime_17082879366811 hd
        subst q
        change (5 : ZMod 204994552401733)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_205891132094653 : Nat.Prime 205891132094653 := by
  apply lucas_primality 205891132094653 (7 : ZMod 205891132094653)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 205891132094653 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((523 : ℕ)^1 * ((6091 : ℕ)^1 * ((5385997 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 205891132094653)^102945566047326 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 205891132094653)^68630377364884 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 523 := Nat.prime_eq_prime_of_dvd_pow hq prime_523 hd
          subst q
          change (7 : ZMod 205891132094653)^393673292724 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 6091 := Nat.prime_eq_prime_of_dvd_pow hq prime_6091 hd
            subst q
            change (7 : ZMod 205891132094653)^33802517172 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 5385997 := Nat.prime_eq_prime_of_dvd_pow hq prime_5385997 hd
            subst q
            change (7 : ZMod 205891132094653)^38227116 ≠ 1
            reduce_mod_char
            decide

theorem prime_210200119635371 : Nat.Prime 210200119635371 := by
  apply lucas_primality 210200119635371 (2 : ZMod 210200119635371)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 210200119635371 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((167 : ℕ)^1 * ((2293 : ℕ)^1 * ((54892427 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 210200119635371)^105100059817685 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 210200119635371)^42040023927074 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
          subst q
          change (2 : ZMod 210200119635371)^1258683351110 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2293 := Nat.prime_eq_prime_of_dvd_pow hq prime_2293 hd
            subst q
            change (2 : ZMod 210200119635371)^91670353090 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 54892427 := Nat.prime_eq_prime_of_dvd_pow hq prime_54892427 hd
            subst q
            change (2 : ZMod 210200119635371)^3829310 ≠ 1
            reduce_mod_char
            decide

theorem prime_211027453382677 : Nat.Prime 211027453382677 := by
  apply lucas_primality 211027453382677 (2 : ZMod 211027453382677)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 211027453382677 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((23 : ℕ)^1 * ((109227460343 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 211027453382677)^105513726691338 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 211027453382677)^70342484460892 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 211027453382677)^30146779054668 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (2 : ZMod 211027453382677)^9175106668812 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 109227460343 := Nat.prime_eq_prime_of_dvd_pow hq prime_109227460343 hd
            subst q
            change (2 : ZMod 211027453382677)^1932 ≠ 1
            reduce_mod_char
            decide

theorem prime_216270112515683 : Nat.Prime 216270112515683 := by
  apply lucas_primality 216270112515683 (2 : ZMod 216270112515683)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 216270112515683 - 1 = (2 : ℕ)^1 * ((79 : ℕ)^1 * ((1368798180479 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 216270112515683)^108135056257841 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
        subst q
        change (2 : ZMod 216270112515683)^2737596360958 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1368798180479 := Nat.prime_eq_prime_of_dvd_pow hq prime_1368798180479 hd
        subst q
        change (2 : ZMod 216270112515683)^158 ≠ 1
        reduce_mod_char
        decide

theorem prime_218169020025017 : Nat.Prime 218169020025017 := by
  apply lucas_primality 218169020025017 (3 : ZMod 218169020025017)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 218169020025017 - 1 = (2 : ℕ)^3 * ((59 : ℕ)^1 * ((139 : ℕ)^1 * ((733 : ℕ)^1 * ((4536619 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 218169020025017)^109084510012508 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
        subst q
        change (3 : ZMod 218169020025017)^3697780000424 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
          subst q
          change (3 : ZMod 218169020025017)^1569561295144 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 733 := Nat.prime_eq_prime_of_dvd_pow hq prime_733 hd
            subst q
            change (3 : ZMod 218169020025017)^297638499352 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 4536619 := Nat.prime_eq_prime_of_dvd_pow hq prime_4536619 hd
            subst q
            change (3 : ZMod 218169020025017)^48090664 ≠ 1
            reduce_mod_char
            decide

theorem prime_221620863468101 : Nat.Prime 221620863468101 := by
  apply lucas_primality 221620863468101 (7 : ZMod 221620863468101)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 221620863468101 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((109 : ℕ)^1 * ((20332189309 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 221620863468101)^110810431734050 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 221620863468101)^44324172693620 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
          subst q
          change (7 : ZMod 221620863468101)^2033218930900 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 20332189309 := Nat.prime_eq_prime_of_dvd_pow hq prime_20332189309 hd
          subst q
          change (7 : ZMod 221620863468101)^10900 ≠ 1
          reduce_mod_char
          decide

theorem prime_227081481823733 : Nat.Prime 227081481823733 := by
  apply lucas_primality 227081481823733 (2 : ZMod 227081481823733)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 227081481823733 - 1 = (2 : ℕ)^2 * ((61 : ℕ)^1 * ((193 : ℕ)^1 * ((1021 : ℕ)^1 * ((1549 : ℕ)^1 * ((3049 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 227081481823733)^113540740911866 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
        subst q
        change (2 : ZMod 227081481823733)^3722647243012 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
          subst q
          change (2 : ZMod 227081481823733)^1176587988724 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1021 := Nat.prime_eq_prime_of_dvd_pow hq prime_1021 hd
            subst q
            change (2 : ZMod 227081481823733)^222410853892 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1549 := Nat.prime_eq_prime_of_dvd_pow hq prime_1549 hd
              subst q
              change (2 : ZMod 227081481823733)^146598761668 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 3049 := Nat.prime_eq_prime_of_dvd_pow hq prime_3049 hd
              subst q
              change (2 : ZMod 227081481823733)^74477363668 ≠ 1
              reduce_mod_char
              decide

theorem prime_232653764952083 : Nat.Prime 232653764952083 := by
  apply lucas_primality 232653764952083 (5 : ZMod 232653764952083)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 232653764952083 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((41 : ℕ)^1 * ((353 : ℕ)^1 * ((423026843 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 232653764952083)^116326882476041 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (5 : ZMod 232653764952083)^12244934997478 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (5 : ZMod 232653764952083)^5674482072002 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 353 := Nat.prime_eq_prime_of_dvd_pow hq prime_353 hd
            subst q
            change (5 : ZMod 232653764952083)^659075821394 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 423026843 := Nat.prime_eq_prime_of_dvd_pow hq prime_423026843 hd
            subst q
            change (5 : ZMod 232653764952083)^549974 ≠ 1
            reduce_mod_char
            decide

theorem prime_238339532186039 : Nat.Prime 238339532186039 := by
  apply lucas_primality 238339532186039 (7 : ZMod 238339532186039)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 238339532186039 - 1 = (2 : ℕ)^1 * ((349 : ℕ)^1 * ((341460647831 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 238339532186039)^119169766093019 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 349 := Nat.prime_eq_prime_of_dvd_pow hq prime_349 hd
        subst q
        change (7 : ZMod 238339532186039)^682921295662 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 341460647831 := Nat.prime_eq_prime_of_dvd_pow hq prime_341460647831 hd
        subst q
        change (7 : ZMod 238339532186039)^698 ≠ 1
        reduce_mod_char
        decide

theorem prime_244140625000003 : Nat.Prime 244140625000003 := by
  apply lucas_primality 244140625000003 (2 : ZMod 244140625000003)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 244140625000003 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((3334819 : ℕ)^1 * ((12201593 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 244140625000003)^122070312500001 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 244140625000003)^81380208333334 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 3334819 := Nat.prime_eq_prime_of_dvd_pow hq prime_3334819 hd
          subst q
          change (2 : ZMod 244140625000003)^73209558 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 12201593 := Nat.prime_eq_prime_of_dvd_pow hq prime_12201593 hd
          subst q
          change (2 : ZMod 244140625000003)^20008914 ≠ 1
          reduce_mod_char
          decide

theorem prime_250058907189011 : Nat.Prime 250058907189011 := by
  apply lucas_primality 250058907189011 (6 : ZMod 250058907189011)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 250058907189011 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((137 : ℕ)^1 * ((182524749773 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 250058907189011)^125029453594505 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 250058907189011)^50011781437802 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
          subst q
          change (6 : ZMod 250058907189011)^1825247497730 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 182524749773 := Nat.prime_eq_prime_of_dvd_pow hq prime_182524749773 hd
          subst q
          change (6 : ZMod 250058907189011)^1370 ≠ 1
          reduce_mod_char
          decide

theorem prime_256096265048081 : Nat.Prime 256096265048081 := by
  apply lucas_primality 256096265048081 (3 : ZMod 256096265048081)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 256096265048081 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((229 : ℕ)^1 * ((15289 : ℕ)^1 * ((914321 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 256096265048081)^128048132524040 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 256096265048081)^51219253009616 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 229 := Nat.prime_eq_prime_of_dvd_pow hq prime_229 hd
          subst q
          change (3 : ZMod 256096265048081)^1118324301520 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 15289 := Nat.prime_eq_prime_of_dvd_pow hq prime_15289 hd
            subst q
            change (3 : ZMod 256096265048081)^16750360720 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 914321 := Nat.prime_eq_prime_of_dvd_pow hq prime_914321 hd
            subst q
            change (3 : ZMod 256096265048081)^280094480 ≠ 1
            reduce_mod_char
            decide

theorem prime_256842052743191 : Nat.Prime 256842052743191 := by
  apply lucas_primality 256842052743191 (11 : ZMod 256842052743191)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 256842052743191 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((2420611 : ℕ)^1 * ((10610629 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 256842052743191)^128421026371595 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 256842052743191)^51368410548638 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2420611 := Nat.prime_eq_prime_of_dvd_pow hq prime_2420611 hd
          subst q
          change (11 : ZMod 256842052743191)^106106290 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 10610629 := Nat.prime_eq_prime_of_dvd_pow hq prime_10610629 hd
          subst q
          change (11 : ZMod 256842052743191)^24206110 ≠ 1
          reduce_mod_char
          decide

theorem prime_260789763095293 : Nat.Prime 260789763095293 := by
  apply lucas_primality 260789763095293 (2 : ZMod 260789763095293)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 260789763095293 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((167 : ℕ)^1 * ((130134612323 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 260789763095293)^130394881547646 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 260789763095293)^86929921031764 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
          subst q
          change (2 : ZMod 260789763095293)^1561615347876 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 130134612323 := Nat.prime_eq_prime_of_dvd_pow hq prime_130134612323 hd
          subst q
          change (2 : ZMod 260789763095293)^2004 ≠ 1
          reduce_mod_char
          decide

theorem prime_262254607552753 : Nat.Prime 262254607552753 := by
  apply lucas_primality 262254607552753 (5 : ZMod 262254607552753)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 262254607552753 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((1013 : ℕ)^1 * ((234500951 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 262254607552753)^131127303776376 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 262254607552753)^87418202517584 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (5 : ZMod 262254607552753)^11402374241424 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1013 := Nat.prime_eq_prime_of_dvd_pow hq prime_1013 hd
            subst q
            change (5 : ZMod 262254607552753)^258889049904 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 234500951 := Nat.prime_eq_prime_of_dvd_pow hq prime_234500951 hd
            subst q
            change (5 : ZMod 262254607552753)^1118352 ≠ 1
            reduce_mod_char
            decide

theorem prime_268535866540127 : Nat.Prime 268535866540127 := by
  apply lucas_primality 268535866540127 (5 : ZMod 268535866540127)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 268535866540127 - 1 = (2 : ℕ)^1 * ((31 : ℕ)^1 * ((8741 : ℕ)^1 * ((495506653 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 268535866540127)^134267933270063 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (5 : ZMod 268535866540127)^8662447307746 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 8741 := Nat.prime_eq_prime_of_dvd_pow hq prime_8741 hd
          subst q
          change (5 : ZMod 268535866540127)^30721412486 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 495506653 := Nat.prime_eq_prime_of_dvd_pow hq prime_495506653 hd
          subst q
          change (5 : ZMod 268535866540127)^541942 ≠ 1
          reduce_mod_char
          decide

end LegendreK6.Pratt
