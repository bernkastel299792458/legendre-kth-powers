import LegendreK6.Pratt.Block017

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LegendreK6.Pratt

theorem prime_59313279827 : Nat.Prime 59313279827 := by
  apply lucas_primality 59313279827 (2 : ZMod 59313279827)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 59313279827 - 1 = (2 : ℕ)^1 * ((107 : ℕ)^1 * ((3637 : ℕ)^1 * ((76207 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 59313279827)^29656639913 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
        subst q
        change (2 : ZMod 59313279827)^554329718 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 3637 := Nat.prime_eq_prime_of_dvd_pow hq prime_3637 hd
          subst q
          change (2 : ZMod 59313279827)^16308298 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 76207 := Nat.prime_eq_prime_of_dvd_pow hq prime_76207 hd
          subst q
          change (2 : ZMod 59313279827)^778318 ≠ 1
          reduce_mod_char
          decide

theorem prime_60526172761 : Nat.Prime 60526172761 := by
  apply lucas_primality 60526172761 (7 : ZMod 60526172761)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 60526172761 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((19 : ℕ)^1 * ((26546567 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 60526172761)^30263086380 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 60526172761)^20175390920 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 60526172761)^12105234552 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (7 : ZMod 60526172761)^3185588040 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 26546567 := Nat.prime_eq_prime_of_dvd_pow hq prime_26546567 hd
            subst q
            change (7 : ZMod 60526172761)^2280 ≠ 1
            reduce_mod_char
            decide

theorem prime_61746811163 : Nat.Prime 61746811163 := by
  apply lucas_primality 61746811163 (2 : ZMod 61746811163)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 61746811163 - 1 = (2 : ℕ)^1 * ((41771 : ℕ)^1 * ((739111 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 61746811163)^30873405581 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 41771 := Nat.prime_eq_prime_of_dvd_pow hq prime_41771 hd
        subst q
        change (2 : ZMod 61746811163)^1478222 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 739111 := Nat.prime_eq_prime_of_dvd_pow hq prime_739111 hd
        subst q
        change (2 : ZMod 61746811163)^83542 ≠ 1
        reduce_mod_char
        decide

theorem prime_62523502271 : Nat.Prime 62523502271 := by
  apply lucas_primality 62523502271 (19 : ZMod 62523502271)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 62523502271 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((31 : ℕ)^1 * ((41 : ℕ)^1 * ((257 : ℕ)^1 * ((19141 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 62523502271)^31261751135 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (19 : ZMod 62523502271)^12504700454 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (19 : ZMod 62523502271)^2016887170 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (19 : ZMod 62523502271)^1524963470 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 257 := Nat.prime_eq_prime_of_dvd_pow hq prime_257 hd
              subst q
              change (19 : ZMod 62523502271)^243282110 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 19141 := Nat.prime_eq_prime_of_dvd_pow hq prime_19141 hd
              subst q
              change (19 : ZMod 62523502271)^3266470 ≠ 1
              reduce_mod_char
              decide

theorem prime_63084556739 : Nat.Prime 63084556739 := by
  apply lucas_primality 63084556739 (2 : ZMod 63084556739)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 63084556739 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((4506039767 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 63084556739)^31542278369 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 63084556739)^9012079534 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4506039767 := Nat.prime_eq_prime_of_dvd_pow hq prime_4506039767 hd
        subst q
        change (2 : ZMod 63084556739)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_63519918421 : Nat.Prime 63519918421 := by
  apply lucas_primality 63519918421 (6 : ZMod 63519918421)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 63519918421 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((1847 : ℕ)^1 * ((81883 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 63519918421)^31759959210 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 63519918421)^21173306140 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 63519918421)^12703983684 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (6 : ZMod 63519918421)^9074274060 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1847 := Nat.prime_eq_prime_of_dvd_pow hq prime_1847 hd
              subst q
              change (6 : ZMod 63519918421)^34390860 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 81883 := Nat.prime_eq_prime_of_dvd_pow hq prime_81883 hd
              subst q
              change (6 : ZMod 63519918421)^775740 ≠ 1
              reduce_mod_char
              decide

theorem prime_63837021163 : Nat.Prime 63837021163 := by
  apply lucas_primality 63837021163 (2 : ZMod 63837021163)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 63837021163 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13933 : ℕ)^1 * ((763619 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 63837021163)^31918510581 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 63837021163)^21279007054 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13933 := Nat.prime_eq_prime_of_dvd_pow hq prime_13933 hd
          subst q
          change (2 : ZMod 63837021163)^4581714 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 763619 := Nat.prime_eq_prime_of_dvd_pow hq prime_763619 hd
          subst q
          change (2 : ZMod 63837021163)^83598 ≠ 1
          reduce_mod_char
          decide

theorem prime_63882219623 : Nat.Prime 63882219623 := by
  apply lucas_primality 63882219623 (10 : ZMod 63882219623)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 63882219623 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((31 : ℕ)^1 * ((61 : ℕ)^1 * ((1299317 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 63882219623)^31941109811 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (10 : ZMod 63882219623)^4914016894 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (10 : ZMod 63882219623)^2060716762 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
            subst q
            change (10 : ZMod 63882219623)^1047249502 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1299317 := Nat.prime_eq_prime_of_dvd_pow hq prime_1299317 hd
            subst q
            change (10 : ZMod 63882219623)^49166 ≠ 1
            reduce_mod_char
            decide

theorem prime_65465843557 : Nat.Prime 65465843557 := by
  apply lucas_primality 65465843557 (2 : ZMod 65465843557)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 65465843557 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((79 : ℕ)^1 * ((69056797 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 65465843557)^32732921778 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 65465843557)^21821947852 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (2 : ZMod 65465843557)^828681564 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 69056797 := Nat.prime_eq_prime_of_dvd_pow hq prime_69056797 hd
          subst q
          change (2 : ZMod 65465843557)^948 ≠ 1
          reduce_mod_char
          decide

theorem prime_67355556781 : Nat.Prime 67355556781 := by
  apply lucas_primality 67355556781 (2 : ZMod 67355556781)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 67355556781 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((73 : ℕ)^1 * ((15377981 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 67355556781)^33677778390 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 67355556781)^22451852260 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 67355556781)^13471111356 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
            subst q
            change (2 : ZMod 67355556781)^922678860 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 15377981 := Nat.prime_eq_prime_of_dvd_pow hq prime_15377981 hd
            subst q
            change (2 : ZMod 67355556781)^4380 ≠ 1
            reduce_mod_char
            decide

theorem prime_67571967613 : Nat.Prime 67571967613 := by
  apply lucas_primality 67571967613 (2 : ZMod 67571967613)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 67571967613 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((107 : ℕ)^1 * ((211 : ℕ)^1 * ((13127 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 67571967613)^33785983806 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 67571967613)^22523989204 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 67571967613)^3556419348 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
            subst q
            change (2 : ZMod 67571967613)^631513716 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 211 := Nat.prime_eq_prime_of_dvd_pow hq prime_211 hd
              subst q
              change (2 : ZMod 67571967613)^320246292 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 13127 := Nat.prime_eq_prime_of_dvd_pow hq prime_13127 hd
              subst q
              change (2 : ZMod 67571967613)^5147556 ≠ 1
              reduce_mod_char
              decide

theorem prime_68719476767 : Nat.Prime 68719476767 := by
  apply lucas_primality 68719476767 (5 : ZMod 68719476767)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 68719476767 - 1 = (2 : ℕ)^1 * ((163 : ℕ)^1 * ((883 : ℕ)^1 * ((238727 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 68719476767)^34359738383 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
        subst q
        change (5 : ZMod 68719476767)^421591882 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 883 := Nat.prime_eq_prime_of_dvd_pow hq prime_883 hd
          subst q
          change (5 : ZMod 68719476767)^77825002 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 238727 := Nat.prime_eq_prime_of_dvd_pow hq prime_238727 hd
          subst q
          change (5 : ZMod 68719476767)^287858 ≠ 1
          reduce_mod_char
          decide

theorem prime_70232989241 : Nat.Prime 70232989241 := by
  apply lucas_primality 70232989241 (3 : ZMod 70232989241)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 70232989241 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((47 : ℕ)^1 * ((37357973 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 70232989241)^35116494620 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 70232989241)^14046597848 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (3 : ZMod 70232989241)^1494318920 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 37357973 := Nat.prime_eq_prime_of_dvd_pow hq prime_37357973 hd
          subst q
          change (3 : ZMod 70232989241)^1880 ≠ 1
          reduce_mod_char
          decide

theorem prime_71563512737 : Nat.Prime 71563512737 := by
  apply lucas_primality 71563512737 (3 : ZMod 71563512737)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 71563512737 - 1 = (2 : ℕ)^5 * ((257 : ℕ)^1 * ((8701789 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 71563512737)^35781756368 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 257 := Nat.prime_eq_prime_of_dvd_pow hq prime_257 hd
        subst q
        change (3 : ZMod 71563512737)^278457248 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 8701789 := Nat.prime_eq_prime_of_dvd_pow hq prime_8701789 hd
        subst q
        change (3 : ZMod 71563512737)^8224 ≠ 1
        reduce_mod_char
        decide

theorem prime_71668989107 : Nat.Prime 71668989107 := by
  apply lucas_primality 71668989107 (2 : ZMod 71668989107)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 71668989107 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((179 : ℕ)^1 * ((263 : ℕ)^1 * ((5323 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 71668989107)^35834494553 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 71668989107)^6515362646 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 71668989107)^5512999162 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 179 := Nat.prime_eq_prime_of_dvd_pow hq prime_179 hd
            subst q
            change (2 : ZMod 71668989107)^400385414 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 263 := Nat.prime_eq_prime_of_dvd_pow hq prime_263 hd
              subst q
              change (2 : ZMod 71668989107)^272505662 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 5323 := Nat.prime_eq_prime_of_dvd_pow hq prime_5323 hd
              subst q
              change (2 : ZMod 71668989107)^13464022 ≠ 1
              reduce_mod_char
              decide

theorem prime_71675707223 : Nat.Prime 71675707223 := by
  apply lucas_primality 71675707223 (7 : ZMod 71675707223)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 71675707223 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((113 : ℕ)^1 * ((45307021 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 71675707223)^35837853611 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 71675707223)^10239386746 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
          subst q
          change (7 : ZMod 71675707223)^634298294 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 45307021 := Nat.prime_eq_prime_of_dvd_pow hq prime_45307021 hd
          subst q
          change (7 : ZMod 71675707223)^1582 ≠ 1
          reduce_mod_char
          decide

theorem prime_75418890637 : Nat.Prime 75418890637 := by
  apply lucas_primality 75418890637 (2 : ZMod 75418890637)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 75418890637 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((6284907553 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 75418890637)^37709445318 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 75418890637)^25139630212 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 6284907553 := Nat.prime_eq_prime_of_dvd_pow hq prime_6284907553 hd
        subst q
        change (2 : ZMod 75418890637)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_79485616429 : Nat.Prime 79485616429 := by
  apply lucas_primality 79485616429 (2 : ZMod 79485616429)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 79485616429 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((67 : ℕ)^1 * ((98862707 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 79485616429)^39742808214 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 79485616429)^26495205476 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (2 : ZMod 79485616429)^1186352484 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 98862707 := Nat.prime_eq_prime_of_dvd_pow hq prime_98862707 hd
          subst q
          change (2 : ZMod 79485616429)^804 ≠ 1
          reduce_mod_char
          decide

theorem prime_79846528199 : Nat.Prime 79846528199 := by
  apply lucas_primality 79846528199 (7 : ZMod 79846528199)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 79846528199 - 1 = (2 : ℕ)^1 * ((31 : ℕ)^2 * ((523 : ℕ)^1 * ((79433 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 79846528199)^39923264099 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (7 : ZMod 79846528199)^2575694458 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 523 := Nat.prime_eq_prime_of_dvd_pow hq prime_523 hd
          subst q
          change (7 : ZMod 79846528199)^152670226 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 79433 := Nat.prime_eq_prime_of_dvd_pow hq prime_79433 hd
          subst q
          change (7 : ZMod 79846528199)^1005206 ≠ 1
          reduce_mod_char
          decide

theorem prime_80279766269 : Nat.Prime 80279766269 := by
  apply lucas_primality 80279766269 (3 : ZMod 80279766269)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 80279766269 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((1543841659 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 80279766269)^40139883134 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 80279766269)^6175366636 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1543841659 := Nat.prime_eq_prime_of_dvd_pow hq prime_1543841659 hd
        subst q
        change (3 : ZMod 80279766269)^52 ≠ 1
        reduce_mod_char
        decide

theorem prime_82653950047 : Nat.Prime 82653950047 := by
  apply lucas_primality 82653950047 (3 : ZMod 82653950047)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 82653950047 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((821 : ℕ)^1 * ((729527 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 82653950047)^41326975023 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 82653950047)^27551316682 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (3 : ZMod 82653950047)^3593650002 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 821 := Nat.prime_eq_prime_of_dvd_pow hq prime_821 hd
            subst q
            change (3 : ZMod 82653950047)^100674726 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 729527 := Nat.prime_eq_prime_of_dvd_pow hq prime_729527 hd
            subst q
            change (3 : ZMod 82653950047)^113298 ≠ 1
            reduce_mod_char
            decide

theorem prime_82851921967 : Nat.Prime 82851921967 := by
  apply lucas_primality 82851921967 (3 : ZMod 82851921967)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 82851921967 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((1255332151 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 82851921967)^41425960983 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 82851921967)^27617307322 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 82851921967)^7531992906 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1255332151 := Nat.prime_eq_prime_of_dvd_pow hq prime_1255332151 hd
          subst q
          change (3 : ZMod 82851921967)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_84901186351 : Nat.Prime 84901186351 := by
  apply lucas_primality 84901186351 (6 : ZMod 84901186351)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 84901186351 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^2 * ((73 : ℕ)^1 * ((2584511 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 84901186351)^42450593175 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 84901186351)^28300395450 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 84901186351)^16980237270 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
            subst q
            change (6 : ZMod 84901186351)^1163029950 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2584511 := Nat.prime_eq_prime_of_dvd_pow hq prime_2584511 hd
            subst q
            change (6 : ZMod 84901186351)^32850 ≠ 1
            reduce_mod_char
            decide

theorem prime_86420732689 : Nat.Prime 86420732689 := by
  apply lucas_primality 86420732689 (13 : ZMod 86420732689)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 86420732689 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((600143977 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 86420732689)^43210366344 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 86420732689)^28806910896 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 600143977 := Nat.prime_eq_prime_of_dvd_pow hq prime_600143977 hd
        subst q
        change (13 : ZMod 86420732689)^144 ≠ 1
        reduce_mod_char
        decide

theorem prime_87058328509 : Nat.Prime 87058328509 := by
  apply lucas_primality 87058328509 (2 : ZMod 87058328509)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 87058328509 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((16561 : ℕ)^1 * ((146023 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 87058328509)^43529164254 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 87058328509)^29019442836 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 16561 := Nat.prime_eq_prime_of_dvd_pow hq prime_16561 hd
          subst q
          change (2 : ZMod 87058328509)^5256828 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 146023 := Nat.prime_eq_prime_of_dvd_pow hq prime_146023 hd
          subst q
          change (2 : ZMod 87058328509)^596196 ≠ 1
          reduce_mod_char
          decide

theorem prime_90458382251 : Nat.Prime 90458382251 := by
  apply lucas_primality 90458382251 (2 : ZMod 90458382251)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 90458382251 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^3 * ((1609 : ℕ)^1 * ((224881 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 90458382251)^45229191125 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 90458382251)^18091676450 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1609 := Nat.prime_eq_prime_of_dvd_pow hq prime_1609 hd
          subst q
          change (2 : ZMod 90458382251)^56220250 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 224881 := Nat.prime_eq_prime_of_dvd_pow hq prime_224881 hd
          subst q
          change (2 : ZMod 90458382251)^402250 ≠ 1
          reduce_mod_char
          decide

theorem prime_90672357691 : Nat.Prime 90672357691 := by
  apply lucas_primality 90672357691 (13 : ZMod 90672357691)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 90672357691 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((151 : ℕ)^1 * ((479 : ℕ)^1 * ((4643 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 90672357691)^45336178845 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 90672357691)^30224119230 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 90672357691)^18134471538 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
            subst q
            change (13 : ZMod 90672357691)^600479190 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 479 := Nat.prime_eq_prime_of_dvd_pow hq prime_479 hd
              subst q
              change (13 : ZMod 90672357691)^189295110 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 4643 := Nat.prime_eq_prime_of_dvd_pow hq prime_4643 hd
              subst q
              change (13 : ZMod 90672357691)^19528830 ≠ 1
              reduce_mod_char
              decide

theorem prime_92598005743 : Nat.Prime 92598005743 := by
  apply lucas_primality 92598005743 (6 : ZMod 92598005743)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 92598005743 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((43 : ℕ)^1 * ((3371 : ℕ)^1 * ((9679 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 92598005743)^46299002871 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 92598005743)^30866001914 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (6 : ZMod 92598005743)^8418000522 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (6 : ZMod 92598005743)^2153441994 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 3371 := Nat.prime_eq_prime_of_dvd_pow hq prime_3371 hd
              subst q
              change (6 : ZMod 92598005743)^27469002 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 9679 := Nat.prime_eq_prime_of_dvd_pow hq prime_9679 hd
              subst q
              change (6 : ZMod 92598005743)^9566898 ≠ 1
              reduce_mod_char
              decide

theorem prime_92717670211 : Nat.Prime 92717670211 := by
  apply lucas_primality 92717670211 (2 : ZMod 92717670211)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 92717670211 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((167 : ℕ)^1 * ((263 : ℕ)^1 * ((6397 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 92717670211)^46358835105 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 92717670211)^30905890070 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 92717670211)^18543534042 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (2 : ZMod 92717670211)^8428879110 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
              subst q
              change (2 : ZMod 92717670211)^555195630 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 263 := Nat.prime_eq_prime_of_dvd_pow hq prime_263 hd
                subst q
                change (2 : ZMod 92717670211)^352538670 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 6397 := Nat.prime_eq_prime_of_dvd_pow hq prime_6397 hd
                subst q
                change (2 : ZMod 92717670211)^14493930 ≠ 1
                reduce_mod_char
                decide

theorem prime_92733067643 : Nat.Prime 92733067643 := by
  apply lucas_primality 92733067643 (2 : ZMod 92733067643)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 92733067643 - 1 = (2 : ℕ)^1 * ((941 : ℕ)^1 * ((49273681 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 92733067643)^46366533821 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 941 := Nat.prime_eq_prime_of_dvd_pow hq prime_941 hd
        subst q
        change (2 : ZMod 92733067643)^98547362 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 49273681 := Nat.prime_eq_prime_of_dvd_pow hq prime_49273681 hd
        subst q
        change (2 : ZMod 92733067643)^1882 ≠ 1
        reduce_mod_char
        decide

theorem prime_94675383559 : Nat.Prime 94675383559 := by
  apply lucas_primality 94675383559 (11 : ZMod 94675383559)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 94675383559 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((43 : ℕ)^1 * ((17474231 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 94675383559)^47337691779 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 94675383559)^31558461186 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (11 : ZMod 94675383559)^13525054794 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (11 : ZMod 94675383559)^2201753106 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 17474231 := Nat.prime_eq_prime_of_dvd_pow hq prime_17474231 hd
            subst q
            change (11 : ZMod 94675383559)^5418 ≠ 1
            reduce_mod_char
            decide

theorem prime_98867482663 : Nat.Prime 98867482663 := by
  apply lucas_primality 98867482663 (5 : ZMod 98867482663)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 98867482663 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((37 : ℕ)^1 * ((34257617 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 98867482663)^49433741331 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 98867482663)^32955827554 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (5 : ZMod 98867482663)^7605190974 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
            subst q
            change (5 : ZMod 98867482663)^2672094126 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 34257617 := Nat.prime_eq_prime_of_dvd_pow hq prime_34257617 hd
            subst q
            change (5 : ZMod 98867482663)^2886 ≠ 1
            reduce_mod_char
            decide

theorem prime_101771429563 : Nat.Prime 101771429563 := by
  apply lucas_primality 101771429563 (5 : ZMod 101771429563)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 101771429563 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((11 : ℕ)^1 * ((139 : ℕ)^1 * ((157 : ℕ)^1 * ((2617 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 101771429563)^50885714781 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 101771429563)^33923809854 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 101771429563)^9251948142 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
            subst q
            change (5 : ZMod 101771429563)^732168558 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
              subst q
              change (5 : ZMod 101771429563)^648225666 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 2617 := Nat.prime_eq_prime_of_dvd_pow hq prime_2617 hd
              subst q
              change (5 : ZMod 101771429563)^38888586 ≠ 1
              reduce_mod_char
              decide

theorem prime_103779216143 : Nat.Prime 103779216143 := by
  apply lucas_primality 103779216143 (5 : ZMod 103779216143)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 103779216143 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((7412801153 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 103779216143)^51889608071 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 103779216143)^14825602306 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7412801153 := Nat.prime_eq_prime_of_dvd_pow hq prime_7412801153 hd
        subst q
        change (5 : ZMod 103779216143)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_103898075227 : Nat.Prime 103898075227 := by
  apply lucas_primality 103898075227 (2 : ZMod 103898075227)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 103898075227 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((53 : ℕ)^1 * ((709 : ℕ)^1 * ((41893 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 103898075227)^51949037613 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 103898075227)^34632691742 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 103898075227)^9445279566 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
            subst q
            change (2 : ZMod 103898075227)^1960341042 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 709 := Nat.prime_eq_prime_of_dvd_pow hq prime_709 hd
              subst q
              change (2 : ZMod 103898075227)^146541714 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 41893 := Nat.prime_eq_prime_of_dvd_pow hq prime_41893 hd
              subst q
              change (2 : ZMod 103898075227)^2480082 ≠ 1
              reduce_mod_char
              decide

theorem prime_104053808567 : Nat.Prime 104053808567 := by
  apply lucas_primality 104053808567 (5 : ZMod 104053808567)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 104053808567 - 1 = (2 : ℕ)^1 * ((59 : ℕ)^1 * ((167 : ℕ)^1 * ((887 : ℕ)^1 * ((5953 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 104053808567)^52026904283 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
        subst q
        change (5 : ZMod 104053808567)^1763623874 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
          subst q
          change (5 : ZMod 104053808567)^623076698 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 887 := Nat.prime_eq_prime_of_dvd_pow hq prime_887 hd
            subst q
            change (5 : ZMod 104053808567)^117309818 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 5953 := Nat.prime_eq_prime_of_dvd_pow hq prime_5953 hd
            subst q
            change (5 : ZMod 104053808567)^17479222 ≠ 1
            reduce_mod_char
            decide

theorem prime_107918163109 : Nat.Prime 107918163109 := by
  apply lucas_primality 107918163109 (18 : ZMod 107918163109)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 107918163109 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((7 : ℕ)^2 * ((31 : ℕ)^1 * ((397 : ℕ)^1 * ((1657 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (18 : ZMod 107918163109)^53959081554 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (18 : ZMod 107918163109)^35972721036 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (18 : ZMod 107918163109)^15416880444 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (18 : ZMod 107918163109)^3481231068 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 397 := Nat.prime_eq_prime_of_dvd_pow hq prime_397 hd
              subst q
              change (18 : ZMod 107918163109)^271834164 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1657 := Nat.prime_eq_prime_of_dvd_pow hq prime_1657 hd
              subst q
              change (18 : ZMod 107918163109)^65128644 ≠ 1
              reduce_mod_char
              decide

theorem prime_109227460343 : Nat.Prime 109227460343 := by
  apply lucas_primality 109227460343 (5 : ZMod 109227460343)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 109227460343 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((17 : ℕ)^1 * ((3209363 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 109227460343)^54613730171 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 109227460343)^15603922906 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 109227460343)^9929769122 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (5 : ZMod 109227460343)^8402112334 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
              subst q
              change (5 : ZMod 109227460343)^6425144726 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 3209363 := Nat.prime_eq_prime_of_dvd_pow hq prime_3209363 hd
              subst q
              change (5 : ZMod 109227460343)^34034 ≠ 1
              reduce_mod_char
              decide

theorem prime_112449041239 : Nat.Prime 112449041239 := by
  apply lucas_primality 112449041239 (15 : ZMod 112449041239)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 112449041239 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((2671 : ℕ)^1 * ((7016663 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (15 : ZMod 112449041239)^56224520619 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (15 : ZMod 112449041239)^37483013746 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2671 := Nat.prime_eq_prime_of_dvd_pow hq prime_2671 hd
          subst q
          change (15 : ZMod 112449041239)^42099978 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7016663 := Nat.prime_eq_prime_of_dvd_pow hq prime_7016663 hd
          subst q
          change (15 : ZMod 112449041239)^16026 ≠ 1
          reduce_mod_char
          decide

theorem prime_112694600813 : Nat.Prime 112694600813 := by
  apply lucas_primality 112694600813 (2 : ZMod 112694600813)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 112694600813 - 1 = (2 : ℕ)^2 * ((28173650203 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 112694600813)^56347300406 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 28173650203 := Nat.prime_eq_prime_of_dvd_pow hq prime_28173650203 hd
      subst q
      change (2 : ZMod 112694600813)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_112892356033 : Nat.Prime 112892356033 := by
  apply lucas_primality 112892356033 (5 : ZMod 112892356033)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 112892356033 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^1 * ((509 : ℕ)^1 * ((1155169 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 112892356033)^56446178016 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 112892356033)^37630785344 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 509 := Nat.prime_eq_prime_of_dvd_pow hq prime_509 hd
          subst q
          change (5 : ZMod 112892356033)^221792448 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1155169 := Nat.prime_eq_prime_of_dvd_pow hq prime_1155169 hd
          subst q
          change (5 : ZMod 112892356033)^97728 ≠ 1
          reduce_mod_char
          decide

theorem prime_114375824411 : Nat.Prime 114375824411 := by
  apply lucas_primality 114375824411 (2 : ZMod 114375824411)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 114375824411 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((109 : ℕ)^1 * ((104931949 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 114375824411)^57187912205 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 114375824411)^22875164882 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
          subst q
          change (2 : ZMod 114375824411)^1049319490 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 104931949 := Nat.prime_eq_prime_of_dvd_pow hq prime_104931949 hd
          subst q
          change (2 : ZMod 114375824411)^1090 ≠ 1
          reduce_mod_char
          decide

theorem prime_117649000013 : Nat.Prime 117649000013 := by
  apply lucas_primality 117649000013 (2 : ZMod 117649000013)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 117649000013 - 1 = (2 : ℕ)^2 * ((3301 : ℕ)^1 * ((8910103 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 117649000013)^58824500006 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3301 := Nat.prime_eq_prime_of_dvd_pow hq prime_3301 hd
        subst q
        change (2 : ZMod 117649000013)^35640412 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 8910103 := Nat.prime_eq_prime_of_dvd_pow hq prime_8910103 hd
        subst q
        change (2 : ZMod 117649000013)^13204 ≠ 1
        reduce_mod_char
        decide

theorem prime_117685018679 : Nat.Prime 117685018679 := by
  apply lucas_primality 117685018679 (7 : ZMod 117685018679)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 117685018679 - 1 = (2 : ℕ)^1 * ((463 : ℕ)^1 * ((1787 : ℕ)^1 * ((71119 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 117685018679)^58842509339 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 463 := Nat.prime_eq_prime_of_dvd_pow hq prime_463 hd
        subst q
        change (7 : ZMod 117685018679)^254179306 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1787 := Nat.prime_eq_prime_of_dvd_pow hq prime_1787 hd
          subst q
          change (7 : ZMod 117685018679)^65856194 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 71119 := Nat.prime_eq_prime_of_dvd_pow hq prime_71119 hd
          subst q
          change (7 : ZMod 117685018679)^1654762 ≠ 1
          reduce_mod_char
          decide

theorem prime_118571675003 : Nat.Prime 118571675003 := by
  apply lucas_primality 118571675003 (2 : ZMod 118571675003)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 118571675003 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((31 : ℕ)^1 * ((43 : ℕ)^1 * ((607 : ℕ)^1 * ((6661 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 118571675003)^59285837501 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 118571675003)^10779243182 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (2 : ZMod 118571675003)^3824892742 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (2 : ZMod 118571675003)^2757480814 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 607 := Nat.prime_eq_prime_of_dvd_pow hq prime_607 hd
              subst q
              change (2 : ZMod 118571675003)^195340486 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 6661 := Nat.prime_eq_prime_of_dvd_pow hq prime_6661 hd
              subst q
              change (2 : ZMod 118571675003)^17800882 ≠ 1
              reduce_mod_char
              decide

theorem prime_119202813493 : Nat.Prime 119202813493 := by
  apply lucas_primality 119202813493 (2 : ZMod 119202813493)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 119202813493 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((173 : ℕ)^1 * ((449 : ℕ)^1 * ((18269 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 119202813493)^59601406746 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 119202813493)^39734271164 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 119202813493)^17028973356 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
            subst q
            change (2 : ZMod 119202813493)^689033604 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 449 := Nat.prime_eq_prime_of_dvd_pow hq prime_449 hd
              subst q
              change (2 : ZMod 119202813493)^265485108 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 18269 := Nat.prime_eq_prime_of_dvd_pow hq prime_18269 hd
              subst q
              change (2 : ZMod 119202813493)^6524868 ≠ 1
              reduce_mod_char
              decide

theorem prime_120959317697 : Nat.Prime 120959317697 := by
  apply lucas_primality 120959317697 (3 : ZMod 120959317697)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 120959317697 - 1 = (2 : ℕ)^6 * ((7 : ℕ)^3 * ((5510173 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 120959317697)^60479658848 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 120959317697)^17279902528 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5510173 := Nat.prime_eq_prime_of_dvd_pow hq prime_5510173 hd
        subst q
        change (3 : ZMod 120959317697)^21952 ≠ 1
        reduce_mod_char
        decide

theorem prime_121821894221 : Nat.Prime 121821894221 := by
  apply lucas_primality 121821894221 (2 : ZMod 121821894221)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 121821894221 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((468545747 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 121821894221)^60910947110 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 121821894221)^24364378844 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 121821894221)^9370914940 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 468545747 := Nat.prime_eq_prime_of_dvd_pow hq prime_468545747 hd
          subst q
          change (2 : ZMod 121821894221)^260 ≠ 1
          reduce_mod_char
          decide

theorem prime_123276089291 : Nat.Prime 123276089291 := by
  apply lucas_primality 123276089291 (2 : ZMod 123276089291)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 123276089291 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((12327608929 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 123276089291)^61638044645 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 123276089291)^24655217858 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 12327608929 := Nat.prime_eq_prime_of_dvd_pow hq prime_12327608929 hd
        subst q
        change (2 : ZMod 123276089291)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_123291819137 : Nat.Prime 123291819137 := by
  apply lucas_primality 123291819137 (3 : ZMod 123291819137)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 123291819137 - 1 = (2 : ℕ)^7 * ((31 : ℕ)^1 * ((37 : ℕ)^1 * ((839771 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 123291819137)^61645909568 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (3 : ZMod 123291819137)^3977155456 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (3 : ZMod 123291819137)^3332211328 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 839771 := Nat.prime_eq_prime_of_dvd_pow hq prime_839771 hd
          subst q
          change (3 : ZMod 123291819137)^146816 ≠ 1
          reduce_mod_char
          decide

theorem prime_123862603297 : Nat.Prime 123862603297 := by
  apply lucas_primality 123862603297 (5 : ZMod 123862603297)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 123862603297 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((19 : ℕ)^1 * ((3994537 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 123862603297)^61931301648 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 123862603297)^41287534432 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (5 : ZMod 123862603297)^7286035488 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (5 : ZMod 123862603297)^6519084384 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3994537 := Nat.prime_eq_prime_of_dvd_pow hq prime_3994537 hd
            subst q
            change (5 : ZMod 123862603297)^31008 ≠ 1
            reduce_mod_char
            decide

theorem prime_124149964579 : Nat.Prime 124149964579 := by
  apply lucas_primality 124149964579 (2 : ZMod 124149964579)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 124149964579 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((233 : ℕ)^1 * ((1283 : ℕ)^1 * ((3643 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 124149964579)^62074982289 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 124149964579)^41383321526 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 124149964579)^6534208662 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
            subst q
            change (2 : ZMod 124149964579)^532832466 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1283 := Nat.prime_eq_prime_of_dvd_pow hq prime_1283 hd
              subst q
              change (2 : ZMod 124149964579)^96765366 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 3643 := Nat.prime_eq_prime_of_dvd_pow hq prime_3643 hd
              subst q
              change (2 : ZMod 124149964579)^34079046 ≠ 1
              reduce_mod_char
              decide

theorem prime_126672945283 : Nat.Prime 126672945283 := by
  apply lucas_primality 126672945283 (2 : ZMod 126672945283)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 126672945283 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((13 : ℕ)^1 * ((127 : ℕ)^1 * ((473611 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 126672945283)^63336472641 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 126672945283)^42224315094 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 126672945283)^9744072714 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
            subst q
            change (2 : ZMod 126672945283)^997424766 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 473611 := Nat.prime_eq_prime_of_dvd_pow hq prime_473611 hd
            subst q
            change (2 : ZMod 126672945283)^267462 ≠ 1
            reduce_mod_char
            decide

theorem prime_127445478827 : Nat.Prime 127445478827 := by
  apply lucas_primality 127445478827 (2 : ZMod 127445478827)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 127445478827 - 1 = (2 : ℕ)^1 * ((677 : ℕ)^1 * ((94125169 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 127445478827)^63722739413 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 677 := Nat.prime_eq_prime_of_dvd_pow hq prime_677 hd
        subst q
        change (2 : ZMod 127445478827)^188250338 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 94125169 := Nat.prime_eq_prime_of_dvd_pow hq prime_94125169 hd
        subst q
        change (2 : ZMod 127445478827)^1354 ≠ 1
        reduce_mod_char
        decide

theorem prime_128100283939 : Nat.Prime 128100283939 := by
  apply lucas_primality 128100283939 (2 : ZMod 128100283939)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 128100283939 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((646971131 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 128100283939)^64050141969 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 128100283939)^42700094646 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 128100283939)^11645480358 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 646971131 := Nat.prime_eq_prime_of_dvd_pow hq prime_646971131 hd
          subst q
          change (2 : ZMod 128100283939)^198 ≠ 1
          reduce_mod_char
          decide

theorem prime_130134612323 : Nat.Prime 130134612323 := by
  apply lucas_primality 130134612323 (2 : ZMod 130134612323)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 130134612323 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((455016127 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 130134612323)^65067306161 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 130134612323)^11830419302 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 130134612323)^10010354794 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 455016127 := Nat.prime_eq_prime_of_dvd_pow hq prime_455016127 hd
          subst q
          change (2 : ZMod 130134612323)^286 ≠ 1
          reduce_mod_char
          decide

theorem prime_130809809737 : Nat.Prime 130809809737 := by
  apply lucas_primality 130809809737 (7 : ZMod 130809809737)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 130809809737 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((23 : ℕ)^1 * ((26330477 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 130809809737)^65404904868 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 130809809737)^43603269912 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (7 : ZMod 130809809737)^5687383032 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 26330477 := Nat.prime_eq_prime_of_dvd_pow hq prime_26330477 hd
          subst q
          change (7 : ZMod 130809809737)^4968 ≠ 1
          reduce_mod_char
          decide

theorem prime_131388302069 : Nat.Prime 131388302069 := by
  apply lucas_primality 131388302069 (2 : ZMod 131388302069)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 131388302069 - 1 = (2 : ℕ)^2 * ((32847075517 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 131388302069)^65694151034 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 32847075517 := Nat.prime_eq_prime_of_dvd_pow hq prime_32847075517 hd
      subst q
      change (2 : ZMod 131388302069)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_133244912167 : Nat.Prime 133244912167 := by
  apply lucas_primality 133244912167 (11 : ZMod 133244912167)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 133244912167 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((21121 : ℕ)^1 * ((55339 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 133244912167)^66622456083 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 133244912167)^44414970722 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (11 : ZMod 133244912167)^7012890114 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 21121 := Nat.prime_eq_prime_of_dvd_pow hq prime_21121 hd
            subst q
            change (11 : ZMod 133244912167)^6308646 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 55339 := Nat.prime_eq_prime_of_dvd_pow hq prime_55339 hd
            subst q
            change (11 : ZMod 133244912167)^2407794 ≠ 1
            reduce_mod_char
            decide

theorem prime_134697636313 : Nat.Prime 134697636313 := by
  apply lucas_primality 134697636313 (5 : ZMod 134697636313)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 134697636313 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((12239 : ℕ)^1 * ((458567 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 134697636313)^67348818156 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 134697636313)^44899212104 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 12239 := Nat.prime_eq_prime_of_dvd_pow hq prime_12239 hd
          subst q
          change (5 : ZMod 134697636313)^11005608 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 458567 := Nat.prime_eq_prime_of_dvd_pow hq prime_458567 hd
          subst q
          change (5 : ZMod 134697636313)^293736 ≠ 1
          reduce_mod_char
          decide

theorem prime_136570256369 : Nat.Prime 136570256369 := by
  apply lucas_primality 136570256369 (3 : ZMod 136570256369)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 136570256369 - 1 = (2 : ℕ)^4 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((93798253 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 136570256369)^68285128184 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 136570256369)^19510036624 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 136570256369)^10505404336 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 93798253 := Nat.prime_eq_prime_of_dvd_pow hq prime_93798253 hd
          subst q
          change (3 : ZMod 136570256369)^1456 ≠ 1
          reduce_mod_char
          decide

theorem prime_136951900717 : Nat.Prime 136951900717 := by
  apply lucas_primality 136951900717 (5 : ZMod 136951900717)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 136951900717 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((47 : ℕ)^1 * ((14657 : ℕ)^1 * ((16567 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 136951900717)^68475950358 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 136951900717)^45650633572 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (5 : ZMod 136951900717)^2913870228 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 14657 := Nat.prime_eq_prime_of_dvd_pow hq prime_14657 hd
            subst q
            change (5 : ZMod 136951900717)^9343788 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 16567 := Nat.prime_eq_prime_of_dvd_pow hq prime_16567 hd
            subst q
            change (5 : ZMod 136951900717)^8266548 ≠ 1
            reduce_mod_char
            decide

theorem prime_139135677007 : Nat.Prime 139135677007 := by
  apply lucas_primality 139135677007 (3 : ZMod 139135677007)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 139135677007 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((23189279501 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 139135677007)^69567838503 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 139135677007)^46378559002 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 23189279501 := Nat.prime_eq_prime_of_dvd_pow hq prime_23189279501 hd
        subst q
        change (3 : ZMod 139135677007)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_139314069577 : Nat.Prime 139314069577 := by
  apply lucas_primality 139314069577 (5 : ZMod 139314069577)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 139314069577 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((41 : ℕ)^1 * ((73 : ℕ)^1 * ((58771 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 139314069577)^69657034788 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 139314069577)^46438023192 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 139314069577)^12664915416 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (5 : ZMod 139314069577)^3397904136 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
              subst q
              change (5 : ZMod 139314069577)^1908411912 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 58771 := Nat.prime_eq_prime_of_dvd_pow hq prime_58771 hd
              subst q
              change (5 : ZMod 139314069577)^2370456 ≠ 1
              reduce_mod_char
              decide

theorem prime_142618665557 : Nat.Prime 142618665557 := by
  apply lucas_primality 142618665557 (2 : ZMod 142618665557)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 142618665557 - 1 = (2 : ℕ)^2 * ((17 : ℕ)^1 * ((79 : ℕ)^1 * ((337 : ℕ)^1 * ((78779 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 142618665557)^71309332778 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 142618665557)^8389333268 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (2 : ZMod 142618665557)^1805299564 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 337 := Nat.prime_eq_prime_of_dvd_pow hq prime_337 hd
            subst q
            change (2 : ZMod 142618665557)^423200788 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 78779 := Nat.prime_eq_prime_of_dvd_pow hq prime_78779 hd
            subst q
            change (2 : ZMod 142618665557)^1810364 ≠ 1
            reduce_mod_char
            decide

theorem prime_144114709391 : Nat.Prime 144114709391 := by
  apply lucas_primality 144114709391 (7 : ZMod 144114709391)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 144114709391 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((23 : ℕ)^1 * ((2617 : ℕ)^1 * ((239429 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 144114709391)^72057354695 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 144114709391)^28822941878 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (7 : ZMod 144114709391)^6265856930 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2617 := Nat.prime_eq_prime_of_dvd_pow hq prime_2617 hd
            subst q
            change (7 : ZMod 144114709391)^55068670 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 239429 := Nat.prime_eq_prime_of_dvd_pow hq prime_239429 hd
            subst q
            change (7 : ZMod 144114709391)^601910 ≠ 1
            reduce_mod_char
            decide

theorem prime_150952051013 : Nat.Prime 150952051013 := by
  apply lucas_primality 150952051013 (2 : ZMod 150952051013)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 150952051013 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((3137 : ℕ)^1 * ((1718567 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 150952051013)^75476025506 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 150952051013)^21564578716 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 3137 := Nat.prime_eq_prime_of_dvd_pow hq prime_3137 hd
          subst q
          change (2 : ZMod 150952051013)^48119876 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1718567 := Nat.prime_eq_prime_of_dvd_pow hq prime_1718567 hd
          subst q
          change (2 : ZMod 150952051013)^87836 ≠ 1
          reduce_mod_char
          decide

theorem prime_151334226341 : Nat.Prime 151334226341 := by
  apply lucas_primality 151334226341 (2 : ZMod 151334226341)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 151334226341 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((9601 : ℕ)^1 * ((71647 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 151334226341)^75667113170 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 151334226341)^30266845268 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 151334226341)^13757656940 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 9601 := Nat.prime_eq_prime_of_dvd_pow hq prime_9601 hd
            subst q
            change (2 : ZMod 151334226341)^15762340 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 71647 := Nat.prime_eq_prime_of_dvd_pow hq prime_71647 hd
            subst q
            change (2 : ZMod 151334226341)^2112220 ≠ 1
            reduce_mod_char
            decide

theorem prime_151680495877 : Nat.Prime 151680495877 := by
  apply lucas_primality 151680495877 (2 : ZMod 151680495877)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 151680495877 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((13 : ℕ)^1 * ((73 : ℕ)^1 * ((229 : ℕ)^1 * ((1187 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 151680495877)^75840247938 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 151680495877)^50560165292 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 151680495877)^21668642268 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (2 : ZMod 151680495877)^11667730452 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
              subst q
              change (2 : ZMod 151680495877)^2077815012 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 229 := Nat.prime_eq_prime_of_dvd_pow hq prime_229 hd
                subst q
                change (2 : ZMod 151680495877)^662360244 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 1187 := Nat.prime_eq_prime_of_dvd_pow hq prime_1187 hd
                subst q
                change (2 : ZMod 151680495877)^127784748 ≠ 1
                reduce_mod_char
                decide

theorem prime_155209189361 : Nat.Prime 155209189361 := by
  apply lucas_primality 155209189361 (3 : ZMod 155209189361)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 155209189361 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((5639 : ℕ)^1 * ((344053 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 155209189361)^77604594680 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 155209189361)^31041837872 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5639 := Nat.prime_eq_prime_of_dvd_pow hq prime_5639 hd
          subst q
          change (3 : ZMod 155209189361)^27524240 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 344053 := Nat.prime_eq_prime_of_dvd_pow hq prime_344053 hd
          subst q
          change (3 : ZMod 155209189361)^451120 ≠ 1
          reduce_mod_char
          decide

theorem prime_157221785573 : Nat.Prime 157221785573 := by
  apply lucas_primality 157221785573 (2 : ZMod 157221785573)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 157221785573 - 1 = (2 : ℕ)^2 * ((39305446393 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 157221785573)^78610892786 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 39305446393 := Nat.prime_eq_prime_of_dvd_pow hq prime_39305446393 hd
      subst q
      change (2 : ZMod 157221785573)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_157847728253 : Nat.Prime 157847728253 := by
  apply lucas_primality 157847728253 (2 : ZMod 157847728253)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 157847728253 - 1 = (2 : ℕ)^2 * ((39461932063 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 157847728253)^78923864126 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 39461932063 := Nat.prime_eq_prime_of_dvd_pow hq prime_39461932063 hd
      subst q
      change (2 : ZMod 157847728253)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_159925716523 : Nat.Prime 159925716523 := by
  apply lucas_primality 159925716523 (3 : ZMod 159925716523)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 159925716523 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((6903467 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 159925716523)^79962858261 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 159925716523)^53308572174 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 159925716523)^14538701502 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (3 : ZMod 159925716523)^12301978194 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 6903467 := Nat.prime_eq_prime_of_dvd_pow hq prime_6903467 hd
            subst q
            change (3 : ZMod 159925716523)^23166 ≠ 1
            reduce_mod_char
            decide

theorem prime_161020922033 : Nat.Prime 161020922033 := by
  apply lucas_primality 161020922033 (3 : ZMod 161020922033)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 161020922033 - 1 = (2 : ℕ)^4 * ((14401 : ℕ)^1 * ((698827 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 161020922033)^80510461016 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 14401 := Nat.prime_eq_prime_of_dvd_pow hq prime_14401 hd
        subst q
        change (3 : ZMod 161020922033)^11181232 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 698827 := Nat.prime_eq_prime_of_dvd_pow hq prime_698827 hd
        subst q
        change (3 : ZMod 161020922033)^230416 ≠ 1
        reduce_mod_char
        decide

theorem prime_163379650381 : Nat.Prime 163379650381 := by
  apply lucas_primality 163379650381 (2 : ZMod 163379650381)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 163379650381 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((23 : ℕ)^2 * ((127 : ℕ)^1 * ((40531 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 163379650381)^81689825190 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 163379650381)^54459883460 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 163379650381)^32675930076 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (2 : ZMod 163379650381)^7103463060 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
              subst q
              change (2 : ZMod 163379650381)^1286453940 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 40531 := Nat.prime_eq_prime_of_dvd_pow hq prime_40531 hd
              subst q
              change (2 : ZMod 163379650381)^4030980 ≠ 1
              reduce_mod_char
              decide

theorem prime_164206490183 : Nat.Prime 164206490183 := by
  apply lucas_primality 164206490183 (5 : ZMod 164206490183)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 164206490183 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((15031 : ℕ)^1 * ((780323 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 164206490183)^82103245091 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 164206490183)^23458070026 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 15031 := Nat.prime_eq_prime_of_dvd_pow hq prime_15031 hd
          subst q
          change (5 : ZMod 164206490183)^10924522 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 780323 := Nat.prime_eq_prime_of_dvd_pow hq prime_780323 hd
          subst q
          change (5 : ZMod 164206490183)^210434 ≠ 1
          reduce_mod_char
          decide

theorem prime_164291778757 : Nat.Prime 164291778757 := by
  apply lucas_primality 164291778757 (5 : ZMod 164291778757)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 164291778757 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((7 : ℕ)^2 * ((19 : ℕ)^1 * ((683 : ℕ)^1 * ((7177 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 164291778757)^82145889378 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 164291778757)^54763926252 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 164291778757)^23470254108 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (5 : ZMod 164291778757)^8646935724 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 683 := Nat.prime_eq_prime_of_dvd_pow hq prime_683 hd
              subst q
              change (5 : ZMod 164291778757)^240544332 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 7177 := Nat.prime_eq_prime_of_dvd_pow hq prime_7177 hd
              subst q
              change (5 : ZMod 164291778757)^22891428 ≠ 1
              reduce_mod_char
              decide

theorem prime_164441203207 : Nat.Prime 164441203207 := by
  apply lucas_primality 164441203207 (3 : ZMod 164441203207)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 164441203207 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((73 : ℕ)^1 * ((2707 : ℕ)^1 * ((19813 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 164441203207)^82220601603 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 164441203207)^54813734402 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 164441203207)^23491600458 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
            subst q
            change (3 : ZMod 164441203207)^2252619222 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 2707 := Nat.prime_eq_prime_of_dvd_pow hq prime_2707 hd
              subst q
              change (3 : ZMod 164441203207)^60746658 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 19813 := Nat.prime_eq_prime_of_dvd_pow hq prime_19813 hd
              subst q
              change (3 : ZMod 164441203207)^8299662 ≠ 1
              reduce_mod_char
              decide

theorem prime_165594764389 : Nat.Prime 165594764389 := by
  apply lucas_primality 165594764389 (2 : ZMod 165594764389)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 165594764389 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((13799563699 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 165594764389)^82797382194 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 165594764389)^55198254796 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13799563699 := Nat.prime_eq_prime_of_dvd_pow hq prime_13799563699 hd
        subst q
        change (2 : ZMod 165594764389)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_167205381377 : Nat.Prime 167205381377 := by
  apply lucas_primality 167205381377 (3 : ZMod 167205381377)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 167205381377 - 1 = (2 : ℕ)^8 * ((11 : ℕ)^2 * ((2027 : ℕ)^1 * ((2663 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 167205381377)^83602690688 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 167205381377)^15200489216 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2027 := Nat.prime_eq_prime_of_dvd_pow hq prime_2027 hd
          subst q
          change (3 : ZMod 167205381377)^82489088 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2663 := Nat.prime_eq_prime_of_dvd_pow hq prime_2663 hd
          subst q
          change (3 : ZMod 167205381377)^62788352 ≠ 1
          reduce_mod_char
          decide

theorem prime_168336217109 : Nat.Prime 168336217109 := by
  apply lucas_primality 168336217109 (2 : ZMod 168336217109)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 168336217109 - 1 = (2 : ℕ)^2 * ((197 : ℕ)^1 * ((9907 : ℕ)^1 * ((21563 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 168336217109)^84168108554 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
        subst q
        change (2 : ZMod 168336217109)^854498564 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 9907 := Nat.prime_eq_prime_of_dvd_pow hq prime_9907 hd
          subst q
          change (2 : ZMod 168336217109)^16991644 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 21563 := Nat.prime_eq_prime_of_dvd_pow hq prime_21563 hd
          subst q
          change (2 : ZMod 168336217109)^7806716 ≠ 1
          reduce_mod_char
          decide

theorem prime_170859666343 : Nat.Prime 170859666343 := by
  apply lucas_primality 170859666343 (3 : ZMod 170859666343)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 170859666343 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((677 : ℕ)^1 * ((2213839 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 170859666343)^85429833171 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 170859666343)^56953222114 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (3 : ZMod 170859666343)^8992614018 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 677 := Nat.prime_eq_prime_of_dvd_pow hq prime_677 hd
            subst q
            change (3 : ZMod 170859666343)^252377646 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2213839 := Nat.prime_eq_prime_of_dvd_pow hq prime_2213839 hd
            subst q
            change (3 : ZMod 170859666343)^77178 ≠ 1
            reduce_mod_char
            decide

theorem prime_176552334589 : Nat.Prime 176552334589 := by
  apply lucas_primality 176552334589 (2 : ZMod 176552334589)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 176552334589 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((2101813507 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 176552334589)^88276167294 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 176552334589)^58850778196 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 176552334589)^25221762084 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2101813507 := Nat.prime_eq_prime_of_dvd_pow hq prime_2101813507 hd
          subst q
          change (2 : ZMod 176552334589)^84 ≠ 1
          reduce_mod_char
          decide

theorem prime_177454041931 : Nat.Prime 177454041931 := by
  apply lucas_primality 177454041931 (3 : ZMod 177454041931)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 177454041931 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((11 : ℕ)^2 * ((67 : ℕ)^1 * ((107 : ℕ)^1 * ((2273 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 177454041931)^88727020965 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 177454041931)^59151347310 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 177454041931)^35490808386 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (3 : ZMod 177454041931)^16132185630 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
              subst q
              change (3 : ZMod 177454041931)^2648567790 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
                subst q
                change (3 : ZMod 177454041931)^1658448990 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 2273 := Nat.prime_eq_prime_of_dvd_pow hq prime_2273 hd
                subst q
                change (3 : ZMod 177454041931)^78070410 ≠ 1
                reduce_mod_char
                decide

theorem prime_177978515699 : Nat.Prime 177978515699 := by
  apply lucas_primality 177978515699 (2 : ZMod 177978515699)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 177978515699 - 1 = (2 : ℕ)^1 * ((37 : ℕ)^1 * ((107 : ℕ)^1 * ((239 : ℕ)^1 * ((94049 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 177978515699)^88989257849 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (2 : ZMod 177978515699)^4810230154 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
          subst q
          change (2 : ZMod 177978515699)^1663350614 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 239 := Nat.prime_eq_prime_of_dvd_pow hq prime_239 hd
            subst q
            change (2 : ZMod 177978515699)^744679982 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 94049 := Nat.prime_eq_prime_of_dvd_pow hq prime_94049 hd
            subst q
            change (2 : ZMod 177978515699)^1892402 ≠ 1
            reduce_mod_char
            decide

theorem prime_182524749773 : Nat.Prime 182524749773 := by
  apply lucas_primality 182524749773 (2 : ZMod 182524749773)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 182524749773 - 1 = (2 : ℕ)^2 * ((45631187443 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 182524749773)^91262374886 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 45631187443 := Nat.prime_eq_prime_of_dvd_pow hq prime_45631187443 hd
      subst q
      change (2 : ZMod 182524749773)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_183397707817 : Nat.Prime 183397707817 := by
  apply lucas_primality 183397707817 (5 : ZMod 183397707817)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 183397707817 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((4211 : ℕ)^1 * ((1814669 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 183397707817)^91698853908 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 183397707817)^61132569272 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 4211 := Nat.prime_eq_prime_of_dvd_pow hq prime_4211 hd
          subst q
          change (5 : ZMod 183397707817)^43552056 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1814669 := Nat.prime_eq_prime_of_dvd_pow hq prime_1814669 hd
          subst q
          change (5 : ZMod 183397707817)^101064 ≠ 1
          reduce_mod_char
          decide

theorem prime_185217368569 : Nat.Prime 185217368569 := by
  apply lucas_primality 185217368569 (11 : ZMod 185217368569)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 185217368569 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((593 : ℕ)^1 * ((2903 : ℕ)^1 * ((4483 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 185217368569)^92608684284 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 185217368569)^61739122856 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 593 := Nat.prime_eq_prime_of_dvd_pow hq prime_593 hd
          subst q
          change (11 : ZMod 185217368569)^312339576 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2903 := Nat.prime_eq_prime_of_dvd_pow hq prime_2903 hd
            subst q
            change (11 : ZMod 185217368569)^63802056 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 4483 := Nat.prime_eq_prime_of_dvd_pow hq prime_4483 hd
            subst q
            change (11 : ZMod 185217368569)^41315496 ≠ 1
            reduce_mod_char
            decide

theorem prime_185601039931 : Nat.Prime 185601039931 := by
  apply lucas_primality 185601039931 (2 : ZMod 185601039931)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 185601039931 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((687411259 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 185601039931)^92800519965 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 185601039931)^61867013310 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 185601039931)^37120207986 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 687411259 := Nat.prime_eq_prime_of_dvd_pow hq prime_687411259 hd
          subst q
          change (2 : ZMod 185601039931)^270 ≠ 1
          reduce_mod_char
          decide

theorem prime_186810772867 : Nat.Prime 186810772867 := by
  apply lucas_primality 186810772867 (3 : ZMod 186810772867)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 186810772867 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((71 : ℕ)^1 * ((438522941 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 186810772867)^93405386433 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 186810772867)^62270257622 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
          subst q
          change (3 : ZMod 186810772867)^2631137646 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 438522941 := Nat.prime_eq_prime_of_dvd_pow hq prime_438522941 hd
          subst q
          change (3 : ZMod 186810772867)^426 ≠ 1
          reduce_mod_char
          decide

theorem prime_190479300029 : Nat.Prime 190479300029 := by
  apply lucas_primality 190479300029 (2 : ZMod 190479300029)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 190479300029 - 1 = (2 : ℕ)^2 * ((97 : ℕ)^1 * ((2819 : ℕ)^1 * ((174149 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 190479300029)^95239650014 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
        subst q
        change (2 : ZMod 190479300029)^1963704124 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2819 := Nat.prime_eq_prime_of_dvd_pow hq prime_2819 hd
          subst q
          change (2 : ZMod 190479300029)^67569812 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 174149 := Nat.prime_eq_prime_of_dvd_pow hq prime_174149 hd
          subst q
          change (2 : ZMod 190479300029)^1093772 ≠ 1
          reduce_mod_char
          decide

theorem prime_192699928591 : Nat.Prime 192699928591 := by
  apply lucas_primality 192699928591 (3 : ZMod 192699928591)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 192699928591 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((494102381 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 192699928591)^96349964295 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 192699928591)^64233309530 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 192699928591)^38539985718 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (3 : ZMod 192699928591)^14823071430 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 494102381 := Nat.prime_eq_prime_of_dvd_pow hq prime_494102381 hd
            subst q
            change (3 : ZMod 192699928591)^390 ≠ 1
            reduce_mod_char
            decide

theorem prime_196753960439 : Nat.Prime 196753960439 := by
  apply lucas_primality 196753960439 (7 : ZMod 196753960439)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 196753960439 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((19 : ℕ)^1 * ((601 : ℕ)^1 * ((1230743 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 196753960439)^98376980219 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 196753960439)^28107708634 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (7 : ZMod 196753960439)^10355471602 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 601 := Nat.prime_eq_prime_of_dvd_pow hq prime_601 hd
            subst q
            change (7 : ZMod 196753960439)^327377638 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1230743 := Nat.prime_eq_prime_of_dvd_pow hq prime_1230743 hd
            subst q
            change (7 : ZMod 196753960439)^159866 ≠ 1
            reduce_mod_char
            decide

theorem prime_199700302547 : Nat.Prime 199700302547 := by
  apply lucas_primality 199700302547 (2 : ZMod 199700302547)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 199700302547 - 1 = (2 : ℕ)^1 * ((2297 : ℕ)^1 * ((43469809 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 199700302547)^99850151273 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 2297 := Nat.prime_eq_prime_of_dvd_pow hq prime_2297 hd
        subst q
        change (2 : ZMod 199700302547)^86939618 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 43469809 := Nat.prime_eq_prime_of_dvd_pow hq prime_43469809 hd
        subst q
        change (2 : ZMod 199700302547)^4594 ≠ 1
        reduce_mod_char
        decide

theorem prime_203606582027 : Nat.Prime 203606582027 := by
  apply lucas_primality 203606582027 (2 : ZMod 203606582027)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 203606582027 - 1 = (2 : ℕ)^1 * ((4831 : ℕ)^1 * ((21072923 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 203606582027)^101803291013 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 4831 := Nat.prime_eq_prime_of_dvd_pow hq prime_4831 hd
        subst q
        change (2 : ZMod 203606582027)^42145846 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 21072923 := Nat.prime_eq_prime_of_dvd_pow hq prime_21072923 hd
        subst q
        change (2 : ZMod 203606582027)^9662 ≠ 1
        reduce_mod_char
        decide

theorem prime_204881209459 : Nat.Prime 204881209459 := by
  apply lucas_primality 204881209459 (3 : ZMod 204881209459)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 204881209459 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((34146868243 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 204881209459)^102440604729 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 204881209459)^68293736486 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 34146868243 := Nat.prime_eq_prime_of_dvd_pow hq prime_34146868243 hd
        subst q
        change (3 : ZMod 204881209459)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_206403114077 : Nat.Prime 206403114077 := by
  apply lucas_primality 206403114077 (2 : ZMod 206403114077)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 206403114077 - 1 = (2 : ℕ)^2 * ((2609 : ℕ)^1 * ((19777991 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 206403114077)^103201557038 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 2609 := Nat.prime_eq_prime_of_dvd_pow hq prime_2609 hd
        subst q
        change (2 : ZMod 206403114077)^79111964 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 19777991 := Nat.prime_eq_prime_of_dvd_pow hq prime_19777991 hd
        subst q
        change (2 : ZMod 206403114077)^10436 ≠ 1
        reduce_mod_char
        decide

theorem prime_208195175263 : Nat.Prime 208195175263 := by
  apply lucas_primality 208195175263 (11 : ZMod 208195175263)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 208195175263 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((53 : ℕ)^1 * ((654701809 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 208195175263)^104097587631 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 208195175263)^69398391754 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (11 : ZMod 208195175263)^3928210854 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 654701809 := Nat.prime_eq_prime_of_dvd_pow hq prime_654701809 hd
          subst q
          change (11 : ZMod 208195175263)^318 ≠ 1
          reduce_mod_char
          decide

theorem prime_208422380141 : Nat.Prime 208422380141 := by
  apply lucas_primality 208422380141 (2 : ZMod 208422380141)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 208422380141 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((1549 : ℕ)^1 * ((517511 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 208422380141)^104211190070 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 208422380141)^41684476028 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 208422380141)^16032490780 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1549 := Nat.prime_eq_prime_of_dvd_pow hq prime_1549 hd
            subst q
            change (2 : ZMod 208422380141)^134552860 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 517511 := Nat.prime_eq_prime_of_dvd_pow hq prime_517511 hd
            subst q
            change (2 : ZMod 208422380141)^402740 ≠ 1
            reduce_mod_char
            decide

theorem prime_213070147403 : Nat.Prime 213070147403 := by
  apply lucas_primality 213070147403 (2 : ZMod 213070147403)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 213070147403 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((643 : ℕ)^1 * ((647 : ℕ)^1 * ((36583 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 213070147403)^106535073701 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 213070147403)^30438592486 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 643 := Nat.prime_eq_prime_of_dvd_pow hq prime_643 hd
          subst q
          change (2 : ZMod 213070147403)^331368814 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 647 := Nat.prime_eq_prime_of_dvd_pow hq prime_647 hd
            subst q
            change (2 : ZMod 213070147403)^329320166 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 36583 := Nat.prime_eq_prime_of_dvd_pow hq prime_36583 hd
            subst q
            change (2 : ZMod 213070147403)^5824294 ≠ 1
            reduce_mod_char
            decide

theorem prime_213626483467 : Nat.Prime 213626483467 := by
  apply lucas_primality 213626483467 (2 : ZMod 213626483467)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 213626483467 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((31 : ℕ)^1 * ((3457 : ℕ)^1 * ((30203 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 213626483467)^106813241733 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 213626483467)^71208827822 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 213626483467)^19420589406 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (2 : ZMod 213626483467)^6891176886 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 3457 := Nat.prime_eq_prime_of_dvd_pow hq prime_3457 hd
              subst q
              change (2 : ZMod 213626483467)^61795338 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 30203 := Nat.prime_eq_prime_of_dvd_pow hq prime_30203 hd
              subst q
              change (2 : ZMod 213626483467)^7073022 ≠ 1
              reduce_mod_char
              decide

theorem prime_215106235457 : Nat.Prime 215106235457 := by
  apply lucas_primality 215106235457 (3 : ZMod 215106235457)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 215106235457 - 1 = (2 : ℕ)^6 * ((7 : ℕ)^1 * ((17 : ℕ)^1 * ((43 : ℕ)^1 * ((701 : ℕ)^1 * ((937 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 215106235457)^107553117728 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 215106235457)^30729462208 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (3 : ZMod 215106235457)^12653307968 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (3 : ZMod 215106235457)^5002470592 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 701 := Nat.prime_eq_prime_of_dvd_pow hq prime_701 hd
              subst q
              change (3 : ZMod 215106235457)^306856256 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 937 := Nat.prime_eq_prime_of_dvd_pow hq prime_937 hd
              subst q
              change (3 : ZMod 215106235457)^229569088 ≠ 1
              reduce_mod_char
              decide

theorem prime_215918777177 : Nat.Prime 215918777177 := by
  apply lucas_primality 215918777177 (3 : ZMod 215918777177)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 215918777177 - 1 = (2 : ℕ)^3 * ((53 : ℕ)^1 * ((241 : ℕ)^1 * ((2113039 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 215918777177)^107959388588 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
        subst q
        change (3 : ZMod 215918777177)^4073939192 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 241 := Nat.prime_eq_prime_of_dvd_pow hq prime_241 hd
          subst q
          change (3 : ZMod 215918777177)^895928536 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2113039 := Nat.prime_eq_prime_of_dvd_pow hq prime_2113039 hd
          subst q
          change (3 : ZMod 215918777177)^102184 ≠ 1
          reduce_mod_char
          decide

theorem prime_218167408699 : Nat.Prime 218167408699 := by
  apply lucas_primality 218167408699 (7 : ZMod 218167408699)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 218167408699 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((158243 : ℕ)^1 * ((229781 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 218167408699)^109083704349 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 218167408699)^72722469566 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 158243 := Nat.prime_eq_prime_of_dvd_pow hq prime_158243 hd
          subst q
          change (7 : ZMod 218167408699)^1378686 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 229781 := Nat.prime_eq_prime_of_dvd_pow hq prime_229781 hd
          subst q
          change (7 : ZMod 218167408699)^949458 ≠ 1
          reduce_mod_char
          decide

theorem prime_221437123769 : Nat.Prime 221437123769 := by
  apply lucas_primality 221437123769 (3 : ZMod 221437123769)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 221437123769 - 1 = (2 : ℕ)^3 * ((7 : ℕ)^1 * ((3954234353 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 221437123769)^110718561884 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 221437123769)^31633874824 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3954234353 := Nat.prime_eq_prime_of_dvd_pow hq prime_3954234353 hd
        subst q
        change (3 : ZMod 221437123769)^56 ≠ 1
        reduce_mod_char
        decide

theorem prime_222457877569 : Nat.Prime 222457877569 := by
  apply lucas_primality 222457877569 (23 : ZMod 222457877569)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 222457877569 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^2 * ((17 : ℕ)^1 * ((787 : ℕ)^1 * ((28867 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (23 : ZMod 222457877569)^111228938784 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (23 : ZMod 222457877569)^74152625856 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (23 : ZMod 222457877569)^13085757504 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 787 := Nat.prime_eq_prime_of_dvd_pow hq prime_787 hd
            subst q
            change (23 : ZMod 222457877569)^282665664 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 28867 := Nat.prime_eq_prime_of_dvd_pow hq prime_28867 hd
            subst q
            change (23 : ZMod 222457877569)^7706304 ≠ 1
            reduce_mod_char
            decide

theorem prime_225199600721 : Nat.Prime 225199600721 := by
  apply lucas_primality 225199600721 (3 : ZMod 225199600721)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 225199600721 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((5581 : ℕ)^1 * ((504389 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 225199600721)^112599800360 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 225199600721)^45039920144 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5581 := Nat.prime_eq_prime_of_dvd_pow hq prime_5581 hd
          subst q
          change (3 : ZMod 225199600721)^40351120 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 504389 := Nat.prime_eq_prime_of_dvd_pow hq prime_504389 hd
          subst q
          change (3 : ZMod 225199600721)^446480 ≠ 1
          reduce_mod_char
          decide

theorem prime_226046458093 : Nat.Prime 226046458093 := by
  apply lucas_primality 226046458093 (5 : ZMod 226046458093)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 226046458093 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((17 : ℕ)^1 * ((12176603 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 226046458093)^113023229046 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 226046458093)^75348819364 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 226046458093)^32292351156 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (5 : ZMod 226046458093)^17388189084 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
              subst q
              change (5 : ZMod 226046458093)^13296850476 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 12176603 := Nat.prime_eq_prime_of_dvd_pow hq prime_12176603 hd
              subst q
              change (5 : ZMod 226046458093)^18564 ≠ 1
              reduce_mod_char
              decide

theorem prime_233672741179 : Nat.Prime 233672741179 := by
  apply lucas_primality 233672741179 (3 : ZMod 233672741179)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 233672741179 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((641 : ℕ)^1 * ((60757343 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 233672741179)^116836370589 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 233672741179)^77890913726 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 641 := Nat.prime_eq_prime_of_dvd_pow hq prime_641 hd
          subst q
          change (3 : ZMod 233672741179)^364544058 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 60757343 := Nat.prime_eq_prime_of_dvd_pow hq prime_60757343 hd
          subst q
          change (3 : ZMod 233672741179)^3846 ≠ 1
          reduce_mod_char
          decide

theorem prime_243087455623 : Nat.Prime 243087455623 := by
  apply lucas_primality 243087455623 (3 : ZMod 243087455623)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 243087455623 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((3683143267 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 243087455623)^121543727811 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 243087455623)^81029151874 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 243087455623)^22098859602 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3683143267 := Nat.prime_eq_prime_of_dvd_pow hq prime_3683143267 hd
          subst q
          change (3 : ZMod 243087455623)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_253715838331 : Nat.Prime 253715838331 := by
  apply lucas_primality 253715838331 (2 : ZMod 253715838331)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 253715838331 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((2029 : ℕ)^1 * ((4168159 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 253715838331)^126857919165 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 253715838331)^84571946110 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 253715838331)^50743167666 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2029 := Nat.prime_eq_prime_of_dvd_pow hq prime_2029 hd
            subst q
            change (2 : ZMod 253715838331)^125044770 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 4168159 := Nat.prime_eq_prime_of_dvd_pow hq prime_4168159 hd
            subst q
            change (2 : ZMod 253715838331)^60870 ≠ 1
            reduce_mod_char
            decide

theorem prime_256337977873 : Nat.Prime 256337977873 := by
  apply lucas_primality 256337977873 (7 : ZMod 256337977873)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 256337977873 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((37 : ℕ)^2 * ((3900931 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 256337977873)^128168988936 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 256337977873)^85445992624 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (7 : ZMod 256337977873)^6928053456 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3900931 := Nat.prime_eq_prime_of_dvd_pow hq prime_3900931 hd
          subst q
          change (7 : ZMod 256337977873)^65712 ≠ 1
          reduce_mod_char
          decide

theorem prime_261120779449 : Nat.Prime 261120779449 := by
  apply lucas_primality 261120779449 (7 : ZMod 261120779449)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 261120779449 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((10880032477 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 261120779449)^130560389724 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 261120779449)^87040259816 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 10880032477 := Nat.prime_eq_prime_of_dvd_pow hq prime_10880032477 hd
        subst q
        change (7 : ZMod 261120779449)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_262144000007 : Nat.Prime 262144000007 := by
  apply lucas_primality 262144000007 (5 : ZMod 262144000007)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 262144000007 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((18724571429 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 262144000007)^131072000003 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 262144000007)^37449142858 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 18724571429 := Nat.prime_eq_prime_of_dvd_pow hq prime_18724571429 hd
        subst q
        change (5 : ZMod 262144000007)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_270738095869 : Nat.Prime 270738095869 := by
  apply lucas_primality 270738095869 (2 : ZMod 270738095869)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 270738095869 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^4 * ((835611407 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 270738095869)^135369047934 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 270738095869)^90246031956 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 835611407 := Nat.prime_eq_prime_of_dvd_pow hq prime_835611407 hd
        subst q
        change (2 : ZMod 270738095869)^324 ≠ 1
        reduce_mod_char
        decide

theorem prime_273140512739 : Nat.Prime 273140512739 := by
  apply lucas_primality 273140512739 (2 : ZMod 273140512739)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 273140512739 - 1 = (2 : ℕ)^1 * ((136570256369 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 273140512739)^136570256369 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 136570256369 := Nat.prime_eq_prime_of_dvd_pow hq prime_136570256369 hd
      subst q
      change (2 : ZMod 273140512739)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_280128680617 : Nat.Prime 280128680617 := by
  apply lucas_primality 280128680617 (13 : ZMod 280128680617)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 280128680617 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((42299 : ℕ)^1 * ((275941 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 280128680617)^140064340308 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 280128680617)^93376226872 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 42299 := Nat.prime_eq_prime_of_dvd_pow hq prime_42299 hd
          subst q
          change (13 : ZMod 280128680617)^6622584 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 275941 := Nat.prime_eq_prime_of_dvd_pow hq prime_275941 hd
          subst q
          change (13 : ZMod 280128680617)^1015176 ≠ 1
          reduce_mod_char
          decide

theorem prime_280772952461 : Nat.Prime 280772952461 := by
  apply lucas_primality 280772952461 (3 : ZMod 280772952461)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 280772952461 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((811 : ℕ)^1 * ((17293 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 280772952461)^140386476230 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 280772952461)^56154590492 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 280772952461)^40110421780 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (3 : ZMod 280772952461)^25524813860 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
              subst q
              change (3 : ZMod 280772952461)^21597919420 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 811 := Nat.prime_eq_prime_of_dvd_pow hq prime_811 hd
                subst q
                change (3 : ZMod 280772952461)^346205860 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 17293 := Nat.prime_eq_prime_of_dvd_pow hq prime_17293 hd
                subst q
                change (3 : ZMod 280772952461)^16236220 ≠ 1
                reduce_mod_char
                decide

theorem prime_282429005041 : Nat.Prime 282429005041 := by
  apply lucas_primality 282429005041 (23 : ZMod 282429005041)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 282429005041 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^12 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((73 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (23 : ZMod 282429005041)^141214502520 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (23 : ZMod 282429005041)^94143001680 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (23 : ZMod 282429005041)^56485801008 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (23 : ZMod 282429005041)^40347000720 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
              subst q
              change (23 : ZMod 282429005041)^21725308080 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
              subst q
              change (23 : ZMod 282429005041)^3868890480 ≠ 1
              reduce_mod_char
              decide

theorem prime_282429536483 : Nat.Prime 282429536483 := by
  apply lucas_primality 282429536483 (2 : ZMod 282429536483)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 282429536483 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((97 : ℕ)^1 * ((193 : ℕ)^1 * ((577 : ℕ)^1 * ((769 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 282429536483)^141214768241 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 282429536483)^16613502146 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
          subst q
          change (2 : ZMod 282429536483)^2911644706 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
            subst q
            change (2 : ZMod 282429536483)^1463365474 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 577 := Nat.prime_eq_prime_of_dvd_pow hq prime_577 hd
              subst q
              change (2 : ZMod 282429536483)^489479266 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 769 := Nat.prime_eq_prime_of_dvd_pow hq prime_769 hd
              subst q
              change (2 : ZMod 282429536483)^367268578 ≠ 1
              reduce_mod_char
              decide

theorem prime_288229418783 : Nat.Prime 288229418783 := by
  apply lucas_primality 288229418783 (5 : ZMod 288229418783)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 288229418783 - 1 = (2 : ℕ)^1 * ((144114709391 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 288229418783)^144114709391 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 144114709391 := Nat.prime_eq_prime_of_dvd_pow hq prime_144114709391 hd
      subst q
      change (5 : ZMod 288229418783)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_290358534497 : Nat.Prime 290358534497 := by
  apply lucas_primality 290358534497 (3 : ZMod 290358534497)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 290358534497 - 1 = (2 : ℕ)^5 * ((9073704203 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 290358534497)^145179267248 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 9073704203 := Nat.prime_eq_prime_of_dvd_pow hq prime_9073704203 hd
      subst q
      change (3 : ZMod 290358534497)^32 ≠ 1
      reduce_mod_char
      decide

theorem prime_303404755397 : Nat.Prime 303404755397 := by
  apply lucas_primality 303404755397 (2 : ZMod 303404755397)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 303404755397 - 1 = (2 : ℕ)^2 * ((79 : ℕ)^1 * ((239 : ℕ)^1 * ((1381 : ℕ)^1 * ((2909 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 303404755397)^151702377698 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
        subst q
        change (2 : ZMod 303404755397)^3840566524 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 239 := Nat.prime_eq_prime_of_dvd_pow hq prime_239 hd
          subst q
          change (2 : ZMod 303404755397)^1269475964 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1381 := Nat.prime_eq_prime_of_dvd_pow hq prime_1381 hd
            subst q
            change (2 : ZMod 303404755397)^219699316 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2909 := Nat.prime_eq_prime_of_dvd_pow hq prime_2909 hd
            subst q
            change (2 : ZMod 303404755397)^104298644 ≠ 1
            reduce_mod_char
            decide

theorem prime_304006671497 : Nat.Prime 304006671497 := by
  apply lucas_primality 304006671497 (3 : ZMod 304006671497)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 304006671497 - 1 = (2 : ℕ)^3 * ((11 : ℕ)^1 * ((73 : ℕ)^1 * ((47323579 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 304006671497)^152003335748 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 304006671497)^27636970136 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
          subst q
          change (3 : ZMod 304006671497)^4164474952 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 47323579 := Nat.prime_eq_prime_of_dvd_pow hq prime_47323579 hd
          subst q
          change (3 : ZMod 304006671497)^6424 ≠ 1
          reduce_mod_char
          decide

theorem prime_304893723269 : Nat.Prime 304893723269 := by
  apply lucas_primality 304893723269 (2 : ZMod 304893723269)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 304893723269 - 1 = (2 : ℕ)^2 * ((11057 : ℕ)^1 * ((6893681 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 304893723269)^152446861634 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11057 := Nat.prime_eq_prime_of_dvd_pow hq prime_11057 hd
        subst q
        change (2 : ZMod 304893723269)^27574724 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 6893681 := Nat.prime_eq_prime_of_dvd_pow hq prime_6893681 hd
        subst q
        change (2 : ZMod 304893723269)^44228 ≠ 1
        reduce_mod_char
        decide

theorem prime_307810529791 : Nat.Prime 307810529791 := by
  apply lucas_primality 307810529791 (3 : ZMod 307810529791)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 307810529791 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((10260350993 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 307810529791)^153905264895 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 307810529791)^102603509930 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 307810529791)^61562105958 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 10260350993 := Nat.prime_eq_prime_of_dvd_pow hq prime_10260350993 hd
          subst q
          change (3 : ZMod 307810529791)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_313418895893 : Nat.Prime 313418895893 := by
  apply lucas_primality 313418895893 (2 : ZMod 313418895893)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 313418895893 - 1 = (2 : ℕ)^2 * ((89 : ℕ)^1 * ((1789 : ℕ)^1 * ((492113 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 313418895893)^156709447946 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
        subst q
        change (2 : ZMod 313418895893)^3521560628 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1789 := Nat.prime_eq_prime_of_dvd_pow hq prime_1789 hd
          subst q
          change (2 : ZMod 313418895893)^175192228 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 492113 := Nat.prime_eq_prime_of_dvd_pow hq prime_492113 hd
          subst q
          change (2 : ZMod 313418895893)^636884 ≠ 1
          reduce_mod_char
          decide

theorem prime_320262609169 : Nat.Prime 320262609169 := by
  apply lucas_primality 320262609169 (11 : ZMod 320262609169)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 320262609169 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((2224045897 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 320262609169)^160131304584 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 320262609169)^106754203056 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2224045897 := Nat.prime_eq_prime_of_dvd_pow hq prime_2224045897 hd
        subst q
        change (11 : ZMod 320262609169)^144 ≠ 1
        reduce_mod_char
        decide

theorem prime_326940373411 : Nat.Prime 326940373411 := by
  apply lucas_primality 326940373411 (2 : ZMod 326940373411)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 326940373411 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((853 : ℕ)^1 * ((1825157 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 326940373411)^163470186705 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 326940373411)^108980124470 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 326940373411)^65388074682 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (2 : ZMod 326940373411)^46705767630 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 853 := Nat.prime_eq_prime_of_dvd_pow hq prime_853 hd
              subst q
              change (2 : ZMod 326940373411)^383282970 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1825157 := Nat.prime_eq_prime_of_dvd_pow hq prime_1825157 hd
              subst q
              change (2 : ZMod 326940373411)^179130 ≠ 1
              reduce_mod_char
              decide

theorem prime_330253666643 : Nat.Prime 330253666643 := by
  apply lucas_primality 330253666643 (2 : ZMod 330253666643)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 330253666643 - 1 = (2 : ℕ)^1 * ((18371 : ℕ)^1 * ((8988451 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 330253666643)^165126833321 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 18371 := Nat.prime_eq_prime_of_dvd_pow hq prime_18371 hd
        subst q
        change (2 : ZMod 330253666643)^17976902 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 8988451 := Nat.prime_eq_prime_of_dvd_pow hq prime_8988451 hd
        subst q
        change (2 : ZMod 330253666643)^36742 ≠ 1
        reduce_mod_char
        decide

theorem prime_340178920171 : Nat.Prime 340178920171 := by
  apply lucas_primality 340178920171 (2 : ZMod 340178920171)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 340178920171 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((3733 : ℕ)^1 * ((3037583 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 340178920171)^170089460085 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 340178920171)^113392973390 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 340178920171)^68035784034 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3733 := Nat.prime_eq_prime_of_dvd_pow hq prime_3733 hd
            subst q
            change (2 : ZMod 340178920171)^91127490 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3037583 := Nat.prime_eq_prime_of_dvd_pow hq prime_3037583 hd
            subst q
            change (2 : ZMod 340178920171)^111990 ≠ 1
            reduce_mod_char
            decide

theorem prime_341460647831 : Nat.Prime 341460647831 := by
  apply lucas_primality 341460647831 (7 : ZMod 341460647831)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 341460647831 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((17483 : ℕ)^1 * ((1953101 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 341460647831)^170730323915 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 341460647831)^68292129566 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17483 := Nat.prime_eq_prime_of_dvd_pow hq prime_17483 hd
          subst q
          change (7 : ZMod 341460647831)^19531010 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1953101 := Nat.prime_eq_prime_of_dvd_pow hq prime_1953101 hd
          subst q
          change (7 : ZMod 341460647831)^174830 ≠ 1
          reduce_mod_char
          decide

theorem prime_351298031629 : Nat.Prime 351298031629 := by
  apply lucas_primality 351298031629 (2 : ZMod 351298031629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 351298031629 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((16921 : ℕ)^1 * ((1730089 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 351298031629)^175649015814 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 351298031629)^117099343876 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 16921 := Nat.prime_eq_prime_of_dvd_pow hq prime_16921 hd
          subst q
          change (2 : ZMod 351298031629)^20761068 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1730089 := Nat.prime_eq_prime_of_dvd_pow hq prime_1730089 hd
          subst q
          change (2 : ZMod 351298031629)^203052 ≠ 1
          reduce_mod_char
          decide

theorem prime_354906323269 : Nat.Prime 354906323269 := by
  apply lucas_primality 354906323269 (2 : ZMod 354906323269)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 354906323269 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((19 : ℕ)^1 * ((222372383 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 354906323269)^177453161634 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 354906323269)^118302107756 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 354906323269)^50700903324 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (2 : ZMod 354906323269)^18679280172 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 222372383 := Nat.prime_eq_prime_of_dvd_pow hq prime_222372383 hd
            subst q
            change (2 : ZMod 354906323269)^1596 ≠ 1
            reduce_mod_char
            decide

theorem prime_357377036537 : Nat.Prime 357377036537 := by
  apply lucas_primality 357377036537 (3 : ZMod 357377036537)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 357377036537 - 1 = (2 : ℕ)^3 * ((13 : ℕ)^1 * ((3793 : ℕ)^1 * ((905963 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 357377036537)^178688518268 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (3 : ZMod 357377036537)^27490541272 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 3793 := Nat.prime_eq_prime_of_dvd_pow hq prime_3793 hd
          subst q
          change (3 : ZMod 357377036537)^94220152 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 905963 := Nat.prime_eq_prime_of_dvd_pow hq prime_905963 hd
          subst q
          change (3 : ZMod 357377036537)^394472 ≠ 1
          reduce_mod_char
          decide

theorem prime_358681734217 : Nat.Prime 358681734217 := by
  apply lucas_primality 358681734217 (5 : ZMod 358681734217)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 358681734217 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((13 : ℕ)^1 * ((3499 : ℕ)^1 * ((109519 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 358681734217)^179340867108 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 358681734217)^119560578072 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (5 : ZMod 358681734217)^27590902632 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3499 := Nat.prime_eq_prime_of_dvd_pow hq prime_3499 hd
            subst q
            change (5 : ZMod 358681734217)^102509784 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 109519 := Nat.prime_eq_prime_of_dvd_pow hq prime_109519 hd
            subst q
            change (5 : ZMod 358681734217)^3275064 ≠ 1
            reduce_mod_char
            decide

theorem prime_372026154931 : Nat.Prime 372026154931 := by
  apply lucas_primality 372026154931 (2 : ZMod 372026154931)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 372026154931 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((12400871831 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 372026154931)^186013077465 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 372026154931)^124008718310 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 372026154931)^74405230986 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 12400871831 := Nat.prime_eq_prime_of_dvd_pow hq prime_12400871831 hd
          subst q
          change (2 : ZMod 372026154931)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_375182587963 : Nat.Prime 375182587963 := by
  apply lucas_primality 375182587963 (23 : ZMod 375182587963)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 375182587963 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((19 : ℕ)^1 * ((53 : ℕ)^1 * ((127 : ℕ)^1 * ((199 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (23 : ZMod 375182587963)^187591293981 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (23 : ZMod 375182587963)^125060862654 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (23 : ZMod 375182587963)^53597512566 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (23 : ZMod 375182587963)^28860199074 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
              subst q
              change (23 : ZMod 375182587963)^19746451998 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
                subst q
                change (23 : ZMod 375182587963)^7078916754 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
                  subst q
                  change (23 : ZMod 375182587963)^2954193606 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 199 := Nat.prime_eq_prime_of_dvd_pow hq prime_199 hd
                  subst q
                  change (23 : ZMod 375182587963)^1885339638 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_377149515643 : Nat.Prime 377149515643 := by
  apply lucas_primality 377149515643 (2 : ZMod 377149515643)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 377149515643 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((17 : ℕ)^1 * ((1232514757 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 377149515643)^188574757821 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 377149515643)^125716505214 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 377149515643)^22185265626 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1232514757 := Nat.prime_eq_prime_of_dvd_pow hq prime_1232514757 hd
          subst q
          change (2 : ZMod 377149515643)^306 ≠ 1
          reduce_mod_char
          decide

theorem prime_377820668359 : Nat.Prime 377820668359 := by
  apply lucas_primality 377820668359 (14 : ZMod 377820668359)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 377820668359 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((2998576733 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 377820668359)^188910334179 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 377820668359)^125940222786 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (14 : ZMod 377820668359)^53974381194 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2998576733 := Nat.prime_eq_prime_of_dvd_pow hq prime_2998576733 hd
          subst q
          change (14 : ZMod 377820668359)^126 ≠ 1
          reduce_mod_char
          decide

theorem prime_378682489093 : Nat.Prime 378682489093 := by
  apply lucas_primality 378682489093 (6 : ZMod 378682489093)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 378682489093 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((47 : ℕ)^1 * ((89 : ℕ)^1 * ((7544077 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 378682489093)^189341244546 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 378682489093)^126227496364 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (6 : ZMod 378682489093)^8057074236 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
            subst q
            change (6 : ZMod 378682489093)^4254859428 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 7544077 := Nat.prime_eq_prime_of_dvd_pow hq prime_7544077 hd
            subst q
            change (6 : ZMod 378682489093)^50196 ≠ 1
            reduce_mod_char
            decide

theorem prime_382233793993 : Nat.Prime 382233793993 := by
  apply lucas_primality 382233793993 (5 : ZMod 382233793993)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 382233793993 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((2099 : ℕ)^1 * ((7587617 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 382233793993)^191116896996 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 382233793993)^127411264664 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2099 := Nat.prime_eq_prime_of_dvd_pow hq prime_2099 hd
          subst q
          change (5 : ZMod 382233793993)^182102808 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7587617 := Nat.prime_eq_prime_of_dvd_pow hq prime_7587617 hd
          subst q
          change (5 : ZMod 382233793993)^50376 ≠ 1
          reduce_mod_char
          decide

theorem prime_392583532151 : Nat.Prime 392583532151 := by
  apply lucas_primality 392583532151 (13 : ZMod 392583532151)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 392583532151 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((17 : ℕ)^1 * ((113 : ℕ)^1 * ((263 : ℕ)^1 * ((15541 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 392583532151)^196291766075 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (13 : ZMod 392583532151)^78516706430 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (13 : ZMod 392583532151)^23093148950 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
            subst q
            change (13 : ZMod 392583532151)^3474190550 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 263 := Nat.prime_eq_prime_of_dvd_pow hq prime_263 hd
              subst q
              change (13 : ZMod 392583532151)^1492713050 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 15541 := Nat.prime_eq_prime_of_dvd_pow hq prime_15541 hd
              subst q
              change (13 : ZMod 392583532151)^25261150 ≠ 1
              reduce_mod_char
              decide

theorem prime_393662724517 : Nat.Prime 393662724517 := by
  apply lucas_primality 393662724517 (2 : ZMod 393662724517)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 393662724517 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^5 * ((19 : ℕ)^1 * ((2797 : ℕ)^1 * ((7621 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 393662724517)^196831362258 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 393662724517)^131220908172 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 393662724517)^20719090764 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2797 := Nat.prime_eq_prime_of_dvd_pow hq prime_2797 hd
            subst q
            change (2 : ZMod 393662724517)^140744628 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 7621 := Nat.prime_eq_prime_of_dvd_pow hq prime_7621 hd
            subst q
            change (2 : ZMod 393662724517)^51654996 ≠ 1
            reduce_mod_char
            decide

theorem prime_404567235143 : Nat.Prime 404567235143 := by
  apply lucas_primality 404567235143 (7 : ZMod 404567235143)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 404567235143 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((35257 : ℕ)^1 * ((819629 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 404567235143)^202283617571 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 404567235143)^57795319306 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 35257 := Nat.prime_eq_prime_of_dvd_pow hq prime_35257 hd
          subst q
          change (7 : ZMod 404567235143)^11474806 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 819629 := Nat.prime_eq_prime_of_dvd_pow hq prime_819629 hd
          subst q
          change (7 : ZMod 404567235143)^493598 ≠ 1
          reduce_mod_char
          decide

theorem prime_413338689329 : Nat.Prime 413338689329 := by
  apply lucas_primality 413338689329 (3 : ZMod 413338689329)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 413338689329 - 1 = (2 : ℕ)^4 * ((433 : ℕ)^1 * ((59662051 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 413338689329)^206669344664 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 433 := Nat.prime_eq_prime_of_dvd_pow hq prime_433 hd
        subst q
        change (3 : ZMod 413338689329)^954592816 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 59662051 := Nat.prime_eq_prime_of_dvd_pow hq prime_59662051 hd
        subst q
        change (3 : ZMod 413338689329)^6928 ≠ 1
        reduce_mod_char
        decide

theorem prime_414056883547 : Nat.Prime 414056883547 := by
  apply lucas_primality 414056883547 (2 : ZMod 414056883547)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 414056883547 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((79 : ℕ)^1 * ((291179243 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 414056883547)^207028441773 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 414056883547)^138018961182 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (2 : ZMod 414056883547)^5241226374 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 291179243 := Nat.prime_eq_prime_of_dvd_pow hq prime_291179243 hd
          subst q
          change (2 : ZMod 414056883547)^1422 ≠ 1
          reduce_mod_char
          decide

theorem prime_433626201031 : Nat.Prime 433626201031 := by
  apply lucas_primality 433626201031 (11 : ZMod 433626201031)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 433626201031 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((77295223 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 433626201031)^216813100515 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 433626201031)^144542067010 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 433626201031)^86725240206 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (11 : ZMod 433626201031)^39420563730 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
              subst q
              change (11 : ZMod 433626201031)^25507423590 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 77295223 := Nat.prime_eq_prime_of_dvd_pow hq prime_77295223 hd
              subst q
              change (11 : ZMod 433626201031)^5610 ≠ 1
              reduce_mod_char
              decide

theorem prime_438206352739 : Nat.Prime 438206352739 := by
  apply lucas_primality 438206352739 (7 : ZMod 438206352739)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 438206352739 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((31 : ℕ)^1 * ((30596729 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 438206352739)^219103176369 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 438206352739)^146068784246 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 438206352739)^62600907534 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (7 : ZMod 438206352739)^39836941158 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
              subst q
              change (7 : ZMod 438206352739)^14135688798 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 30596729 := Nat.prime_eq_prime_of_dvd_pow hq prime_30596729 hd
              subst q
              change (7 : ZMod 438206352739)^14322 ≠ 1
              reduce_mod_char
              decide

theorem prime_438318908707 : Nat.Prime 438318908707 := by
  apply lucas_primality 438318908707 (2 : ZMod 438318908707)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 438318908707 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((17 : ℕ)^1 * ((12157 : ℕ)^1 * ((50497 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 438318908707)^219159454353 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 438318908707)^146106302902 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 438318908707)^62616986958 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (2 : ZMod 438318908707)^25783465218 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 12157 := Nat.prime_eq_prime_of_dvd_pow hq prime_12157 hd
              subst q
              change (2 : ZMod 438318908707)^36054858 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 50497 := Nat.prime_eq_prime_of_dvd_pow hq prime_50497 hd
              subst q
              change (2 : ZMod 438318908707)^8680098 ≠ 1
              reduce_mod_char
              decide

theorem prime_449071510733 : Nat.Prime 449071510733 := by
  apply lucas_primality 449071510733 (2 : ZMod 449071510733)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 449071510733 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((29 : ℕ)^1 * ((16103 : ℕ)^1 * ((18493 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 449071510733)^224535755366 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 449071510733)^34543962364 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (2 : ZMod 449071510733)^15485224508 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 16103 := Nat.prime_eq_prime_of_dvd_pow hq prime_16103 hd
            subst q
            change (2 : ZMod 449071510733)^27887444 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 18493 := Nat.prime_eq_prime_of_dvd_pow hq prime_18493 hd
            subst q
            change (2 : ZMod 449071510733)^24283324 ≠ 1
            reduce_mod_char
            decide

theorem prime_449505960229 : Nat.Prime 449505960229 := by
  apply lucas_primality 449505960229 (2 : ZMod 449505960229)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 449505960229 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((13 : ℕ)^1 * ((109 : ℕ)^1 * ((8811769 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 449505960229)^224752980114 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 449505960229)^149835320076 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 449505960229)^34577381556 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
            subst q
            change (2 : ZMod 449505960229)^4123907892 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 8811769 := Nat.prime_eq_prime_of_dvd_pow hq prime_8811769 hd
            subst q
            change (2 : ZMod 449505960229)^51012 ≠ 1
            reduce_mod_char
            decide

theorem prime_454349926553 : Nat.Prime 454349926553 := by
  apply lucas_primality 454349926553 (3 : ZMod 454349926553)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 454349926553 - 1 = (2 : ℕ)^3 * ((105733 : ℕ)^1 * ((537143 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 454349926553)^227174963276 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 105733 := Nat.prime_eq_prime_of_dvd_pow hq prime_105733 hd
        subst q
        change (3 : ZMod 454349926553)^4297144 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 537143 := Nat.prime_eq_prime_of_dvd_pow hq prime_537143 hd
        subst q
        change (3 : ZMod 454349926553)^845864 ≠ 1
        reduce_mod_char
        decide

theorem prime_464404086793 : Nat.Prime 464404086793 := by
  apply lucas_primality 464404086793 (7 : ZMod 464404086793)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 464404086793 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((241 : ℕ)^1 * ((1291 : ℕ)^1 * ((20731 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 464404086793)^232202043396 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 464404086793)^154801362264 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 241 := Nat.prime_eq_prime_of_dvd_pow hq prime_241 hd
          subst q
          change (7 : ZMod 464404086793)^1926987912 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1291 := Nat.prime_eq_prime_of_dvd_pow hq prime_1291 hd
            subst q
            change (7 : ZMod 464404086793)^359724312 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 20731 := Nat.prime_eq_prime_of_dvd_pow hq prime_20731 hd
            subst q
            change (7 : ZMod 464404086793)^22401432 ≠ 1
            reduce_mod_char
            decide

theorem prime_472783056253 : Nat.Prime 472783056253 := by
  apply lucas_primality 472783056253 (11 : ZMod 472783056253)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 472783056253 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((107 : ℕ)^1 * ((3677 : ℕ)^1 * ((7703 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 472783056253)^236391528126 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 472783056253)^157594352084 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (11 : ZMod 472783056253)^36367927404 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
            subst q
            change (11 : ZMod 472783056253)^4418533236 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 3677 := Nat.prime_eq_prime_of_dvd_pow hq prime_3677 hd
              subst q
              change (11 : ZMod 472783056253)^128578476 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 7703 := Nat.prime_eq_prime_of_dvd_pow hq prime_7703 hd
              subst q
              change (11 : ZMod 472783056253)^61376484 ≠ 1
              reduce_mod_char
              decide

theorem prime_472889041579 : Nat.Prime 472889041579 := by
  apply lucas_primality 472889041579 (3 : ZMod 472889041579)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 472889041579 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((1187 : ℕ)^1 * ((22132783 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 472889041579)^236444520789 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 472889041579)^157629680526 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1187 := Nat.prime_eq_prime_of_dvd_pow hq prime_1187 hd
          subst q
          change (3 : ZMod 472889041579)^398390094 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 22132783 := Nat.prime_eq_prime_of_dvd_pow hq prime_22132783 hd
          subst q
          change (3 : ZMod 472889041579)^21366 ≠ 1
          reduce_mod_char
          decide

theorem prime_479695572953 : Nat.Prime 479695572953 := by
  apply lucas_primality 479695572953 (3 : ZMod 479695572953)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 479695572953 - 1 = (2 : ℕ)^3 * ((223 : ℕ)^1 * ((3499 : ℕ)^1 * ((76847 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 479695572953)^239847786476 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 223 := Nat.prime_eq_prime_of_dvd_pow hq prime_223 hd
        subst q
        change (3 : ZMod 479695572953)^2151101224 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 3499 := Nat.prime_eq_prime_of_dvd_pow hq prime_3499 hd
          subst q
          change (3 : ZMod 479695572953)^137095048 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 76847 := Nat.prime_eq_prime_of_dvd_pow hq prime_76847 hd
          subst q
          change (3 : ZMod 479695572953)^6242216 ≠ 1
          reduce_mod_char
          decide

theorem prime_495149143913 : Nat.Prime 495149143913 := by
  apply lucas_primality 495149143913 (3 : ZMod 495149143913)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 495149143913 - 1 = (2 : ℕ)^3 * ((15131 : ℕ)^1 * ((4090519 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 495149143913)^247574571956 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 15131 := Nat.prime_eq_prime_of_dvd_pow hq prime_15131 hd
        subst q
        change (3 : ZMod 495149143913)^32724152 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4090519 := Nat.prime_eq_prime_of_dvd_pow hq prime_4090519 hd
        subst q
        change (3 : ZMod 495149143913)^121048 ≠ 1
        reduce_mod_char
        decide

theorem prime_496981290977 : Nat.Prime 496981290977 := by
  apply lucas_primality 496981290977 (3 : ZMod 496981290977)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 496981290977 - 1 = (2 : ℕ)^5 * ((15530665343 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 496981290977)^248490645488 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 15530665343 := Nat.prime_eq_prime_of_dvd_pow hq prime_15530665343 hd
      subst q
      change (3 : ZMod 496981290977)^32 ≠ 1
      reduce_mod_char
      decide

theorem prime_514566097657 : Nat.Prime 514566097657 := by
  apply lucas_primality 514566097657 (7 : ZMod 514566097657)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 514566097657 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((31 : ℕ)^1 * ((197 : ℕ)^1 * ((270059 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 514566097657)^257283048828 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 514566097657)^171522032552 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (7 : ZMod 514566097657)^39582007512 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (7 : ZMod 514566097657)^16598906376 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
              subst q
              change (7 : ZMod 514566097657)^2612010648 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 270059 := Nat.prime_eq_prime_of_dvd_pow hq prime_270059 hd
              subst q
              change (7 : ZMod 514566097657)^1905384 ≠ 1
              reduce_mod_char
              decide

theorem prime_523586061017 : Nat.Prime 523586061017 := by
  apply lucas_primality 523586061017 (3 : ZMod 523586061017)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 523586061017 - 1 = (2 : ℕ)^3 * ((31 : ℕ)^1 * ((2111234117 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 523586061017)^261793030508 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (3 : ZMod 523586061017)^16889872936 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2111234117 := Nat.prime_eq_prime_of_dvd_pow hq prime_2111234117 hd
        subst q
        change (3 : ZMod 523586061017)^248 ≠ 1
        reduce_mod_char
        decide

theorem prime_531441000061 : Nat.Prime 531441000061 := by
  apply lucas_primality 531441000061 (2 : ZMod 531441000061)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 531441000061 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((227 : ℕ)^1 * ((39019163 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 531441000061)^265720500030 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 531441000061)^177147000020 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 531441000061)^106288200012 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 227 := Nat.prime_eq_prime_of_dvd_pow hq prime_227 hd
            subst q
            change (2 : ZMod 531441000061)^2341149780 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 39019163 := Nat.prime_eq_prime_of_dvd_pow hq prime_39019163 hd
            subst q
            change (2 : ZMod 531441000061)^13620 ≠ 1
            reduce_mod_char
            decide

theorem prime_553516713221 : Nat.Prime 553516713221 := by
  apply lucas_primality 553516713221 (10 : ZMod 553516713221)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 553516713221 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((293 : ℕ)^1 * ((997 : ℕ)^1 * ((5573 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 553516713221)^276758356610 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (10 : ZMod 553516713221)^110703342644 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (10 : ZMod 553516713221)^32559806660 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 293 := Nat.prime_eq_prime_of_dvd_pow hq prime_293 hd
            subst q
            change (10 : ZMod 553516713221)^1889135540 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 997 := Nat.prime_eq_prime_of_dvd_pow hq prime_997 hd
              subst q
              change (10 : ZMod 553516713221)^555182260 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 5573 := Nat.prime_eq_prime_of_dvd_pow hq prime_5573 hd
              subst q
              change (10 : ZMod 553516713221)^99321140 ≠ 1
              reduce_mod_char
              decide

theorem prime_556398405859 : Nat.Prime 556398405859 := by
  apply lucas_primality 556398405859 (2 : ZMod 556398405859)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 556398405859 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((92733067643 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 556398405859)^278199202929 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 556398405859)^185466135286 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 92733067643 := Nat.prime_eq_prime_of_dvd_pow hq prime_92733067643 hd
        subst q
        change (2 : ZMod 556398405859)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_560909068073 : Nat.Prime 560909068073 := by
  apply lucas_primality 560909068073 (3 : ZMod 560909068073)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 560909068073 - 1 = (2 : ℕ)^3 * ((73 : ℕ)^1 * ((960460733 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 560909068073)^280454534036 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
        subst q
        change (3 : ZMod 560909068073)^7683685864 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 960460733 := Nat.prime_eq_prime_of_dvd_pow hq prime_960460733 hd
        subst q
        change (3 : ZMod 560909068073)^584 ≠ 1
        reduce_mod_char
        decide

theorem prime_567869252057 : Nat.Prime 567869252057 := by
  apply lucas_primality 567869252057 (3 : ZMod 567869252057)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 567869252057 - 1 = (2 : ℕ)^3 * ((587 : ℕ)^1 * ((120926161 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 567869252057)^283934626028 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 587 := Nat.prime_eq_prime_of_dvd_pow hq prime_587 hd
        subst q
        change (3 : ZMod 567869252057)^967409288 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 120926161 := Nat.prime_eq_prime_of_dvd_pow hq prime_120926161 hd
        subst q
        change (3 : ZMod 567869252057)^4696 ≠ 1
        reduce_mod_char
        decide

theorem prime_574641130639 : Nat.Prime 574641130639 := by
  apply lucas_primality 574641130639 (3 : ZMod 574641130639)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 574641130639 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((197 : ℕ)^1 * ((486160009 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 574641130639)^287320565319 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 574641130639)^191547043546 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
          subst q
          change (3 : ZMod 574641130639)^2916960054 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 486160009 := Nat.prime_eq_prime_of_dvd_pow hq prime_486160009 hd
          subst q
          change (3 : ZMod 574641130639)^1182 ≠ 1
          reduce_mod_char
          decide

theorem prime_581517384743 : Nat.Prime 581517384743 := by
  apply lucas_primality 581517384743 (5 : ZMod 581517384743)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 581517384743 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((23 : ℕ)^1 * ((1805954611 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 581517384743)^290758692371 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 581517384743)^83073912106 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (5 : ZMod 581517384743)^25283364554 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1805954611 := Nat.prime_eq_prime_of_dvd_pow hq prime_1805954611 hd
          subst q
          change (5 : ZMod 581517384743)^322 ≠ 1
          reduce_mod_char
          decide

theorem prime_586138144763 : Nat.Prime 586138144763 := by
  apply lucas_primality 586138144763 (2 : ZMod 586138144763)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 586138144763 - 1 = (2 : ℕ)^1 * ((509 : ℕ)^1 * ((575774209 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 586138144763)^293069072381 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 509 := Nat.prime_eq_prime_of_dvd_pow hq prime_509 hd
        subst q
        change (2 : ZMod 586138144763)^1151548418 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 575774209 := Nat.prime_eq_prime_of_dvd_pow hq prime_575774209 hd
        subst q
        change (2 : ZMod 586138144763)^1018 ≠ 1
        reduce_mod_char
        decide

theorem prime_589954115497 : Nat.Prime 589954115497 := by
  apply lucas_primality 589954115497 (10 : ZMod 589954115497)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 589954115497 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((233 : ℕ)^1 * ((105499663 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 589954115497)^294977057748 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 589954115497)^196651371832 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
          subst q
          change (10 : ZMod 589954115497)^2531991912 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 105499663 := Nat.prime_eq_prime_of_dvd_pow hq prime_105499663 hd
          subst q
          change (10 : ZMod 589954115497)^5592 ≠ 1
          reduce_mod_char
          decide

theorem prime_606299279323 : Nat.Prime 606299279323 := by
  apply lucas_primality 606299279323 (3 : ZMod 606299279323)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 606299279323 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((1009 : ℕ)^1 * ((9104413 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 606299279323)^303149639661 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 606299279323)^202099759774 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 606299279323)^55118116302 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1009 := Nat.prime_eq_prime_of_dvd_pow hq prime_1009 hd
            subst q
            change (3 : ZMod 606299279323)^600891258 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 9104413 := Nat.prime_eq_prime_of_dvd_pow hq prime_9104413 hd
            subst q
            change (3 : ZMod 606299279323)^66594 ≠ 1
            reduce_mod_char
            decide

theorem prime_606355001401 : Nat.Prime 606355001401 := by
  apply lucas_primality 606355001401 (11 : ZMod 606355001401)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 606355001401 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((1010591669 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 606355001401)^303177500700 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 606355001401)^202118333800 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 606355001401)^121271000280 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1010591669 := Nat.prime_eq_prime_of_dvd_pow hq prime_1010591669 hd
          subst q
          change (11 : ZMod 606355001401)^600 ≠ 1
          reduce_mod_char
          decide

theorem prime_623622349073 : Nat.Prime 623622349073 := by
  apply lucas_primality 623622349073 (3 : ZMod 623622349073)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 623622349073 - 1 = (2 : ℕ)^4 * ((439 : ℕ)^1 * ((88784503 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 623622349073)^311811174536 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 439 := Nat.prime_eq_prime_of_dvd_pow hq prime_439 hd
        subst q
        change (3 : ZMod 623622349073)^1420552048 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 88784503 := Nat.prime_eq_prime_of_dvd_pow hq prime_88784503 hd
        subst q
        change (3 : ZMod 623622349073)^7024 ≠ 1
        reduce_mod_char
        decide

theorem prime_625450523303 : Nat.Prime 625450523303 := by
  apply lucas_primality 625450523303 (5 : ZMod 625450523303)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 625450523303 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((48017 : ℕ)^1 * ((592073 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 625450523303)^312725261651 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 625450523303)^56859138482 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 48017 := Nat.prime_eq_prime_of_dvd_pow hq prime_48017 hd
          subst q
          change (5 : ZMod 625450523303)^13025606 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 592073 := Nat.prime_eq_prime_of_dvd_pow hq prime_592073 hd
          subst q
          change (5 : ZMod 625450523303)^1056374 ≠ 1
          reduce_mod_char
          decide

theorem prime_635199184211 : Nat.Prime 635199184211 := by
  apply lucas_primality 635199184211 (2 : ZMod 635199184211)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 635199184211 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((63519918421 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 635199184211)^317599592105 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 635199184211)^127039836842 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 63519918421 := Nat.prime_eq_prime_of_dvd_pow hq prime_63519918421 hd
        subst q
        change (2 : ZMod 635199184211)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_642344401541 : Nat.Prime 642344401541 := by
  apply lucas_primality 642344401541 (2 : ZMod 642344401541)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 642344401541 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((227 : ℕ)^1 * ((141485551 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 642344401541)^321172200770 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 642344401541)^128468880308 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 227 := Nat.prime_eq_prime_of_dvd_pow hq prime_227 hd
          subst q
          change (2 : ZMod 642344401541)^2829711020 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 141485551 := Nat.prime_eq_prime_of_dvd_pow hq prime_141485551 hd
          subst q
          change (2 : ZMod 642344401541)^4540 ≠ 1
          reduce_mod_char
          decide

theorem prime_643821603889 : Nat.Prime 643821603889 := by
  apply lucas_primality 643821603889 (11 : ZMod 643821603889)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 643821603889 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((827 : ℕ)^1 * ((16218803 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 643821603889)^321910801944 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 643821603889)^214607201296 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 827 := Nat.prime_eq_prime_of_dvd_pow hq prime_827 hd
          subst q
          change (11 : ZMod 643821603889)^778502544 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 16218803 := Nat.prime_eq_prime_of_dvd_pow hq prime_16218803 hd
          subst q
          change (11 : ZMod 643821603889)^39696 ≠ 1
          reduce_mod_char
          decide

theorem prime_646990183453 : Nat.Prime 646990183453 := by
  apply lucas_primality 646990183453 (5 : ZMod 646990183453)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 646990183453 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((14821 : ℕ)^1 * ((3637801 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 646990183453)^323495091726 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 646990183453)^215663394484 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 14821 := Nat.prime_eq_prime_of_dvd_pow hq prime_14821 hd
          subst q
          change (5 : ZMod 646990183453)^43653612 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3637801 := Nat.prime_eq_prime_of_dvd_pow hq prime_3637801 hd
          subst q
          change (5 : ZMod 646990183453)^177852 ≠ 1
          reduce_mod_char
          decide

theorem prime_652715343151 : Nat.Prime 652715343151 := by
  apply lucas_primality 652715343151 (7 : ZMod 652715343151)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 652715343151 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((13 : ℕ)^1 * ((31 : ℕ)^1 * ((101 : ℕ)^1 * ((106907 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 652715343151)^326357671575 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 652715343151)^217571781050 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 652715343151)^130543068630 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (7 : ZMod 652715343151)^50208872550 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
              subst q
              change (7 : ZMod 652715343151)^21055333650 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
                subst q
                change (7 : ZMod 652715343151)^6462528150 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 106907 := Nat.prime_eq_prime_of_dvd_pow hq prime_106907 hd
                subst q
                change (7 : ZMod 652715343151)^6105450 ≠ 1
                reduce_mod_char
                decide

theorem prime_653120293013 : Nat.Prime 653120293013 := by
  apply lucas_primality 653120293013 (2 : ZMod 653120293013)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 653120293013 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^2 * ((1349422093 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 653120293013)^326560146506 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 653120293013)^59374572092 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1349422093 := Nat.prime_eq_prime_of_dvd_pow hq prime_1349422093 hd
        subst q
        change (2 : ZMod 653120293013)^484 ≠ 1
        reduce_mod_char
        decide

theorem prime_660763734871 : Nat.Prime 660763734871 := by
  apply lucas_primality 660763734871 (3 : ZMod 660763734871)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 660763734871 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((125429 : ℕ)^1 * ((175601 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 660763734871)^330381867435 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 660763734871)^220254578290 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 660763734871)^132152746974 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 125429 := Nat.prime_eq_prime_of_dvd_pow hq prime_125429 hd
            subst q
            change (3 : ZMod 660763734871)^5268030 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 175601 := Nat.prime_eq_prime_of_dvd_pow hq prime_175601 hd
            subst q
            change (3 : ZMod 660763734871)^3762870 ≠ 1
            reduce_mod_char
            decide

theorem prime_681825548827 : Nat.Prime 681825548827 := by
  apply lucas_primality 681825548827 (2 : ZMod 681825548827)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 681825548827 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((37879197157 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 681825548827)^340912774413 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 681825548827)^227275182942 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 37879197157 := Nat.prime_eq_prime_of_dvd_pow hq prime_37879197157 hd
        subst q
        change (2 : ZMod 681825548827)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_683438665373 : Nat.Prime 683438665373 := by
  apply lucas_primality 683438665373 (2 : ZMod 683438665373)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 683438665373 - 1 = (2 : ℕ)^2 * ((170859666343 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 683438665373)^341719332686 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 170859666343 := Nat.prime_eq_prime_of_dvd_pow hq prime_170859666343 hd
      subst q
      change (2 : ZMod 683438665373)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_689869781071 : Nat.Prime 689869781071 := by
  apply lucas_primality 689869781071 (7 : ZMod 689869781071)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 689869781071 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((22995659369 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 689869781071)^344934890535 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 689869781071)^229956593690 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 689869781071)^137973956214 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 22995659369 := Nat.prime_eq_prime_of_dvd_pow hq prime_22995659369 hd
          subst q
          change (7 : ZMod 689869781071)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_720743948329 : Nat.Prime 720743948329 := by
  apply lucas_primality 720743948329 (7 : ZMod 720743948329)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 720743948329 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((47 : ℕ)^1 * ((3793 : ℕ)^1 * ((168457 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 720743948329)^360371974164 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 720743948329)^240247982776 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (7 : ZMod 720743948329)^15334977624 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3793 := Nat.prime_eq_prime_of_dvd_pow hq prime_3793 hd
            subst q
            change (7 : ZMod 720743948329)^190019496 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 168457 := Nat.prime_eq_prime_of_dvd_pow hq prime_168457 hd
            subst q
            change (7 : ZMod 720743948329)^4278504 ≠ 1
            reduce_mod_char
            decide

theorem prime_729416238121 : Nat.Prime 729416238121 := by
  apply lucas_primality 729416238121 (11 : ZMod 729416238121)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 729416238121 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((5821 : ℕ)^1 * ((348077 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 729416238121)^364708119060 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 729416238121)^243138746040 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 729416238121)^145883247624 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 5821 := Nat.prime_eq_prime_of_dvd_pow hq prime_5821 hd
            subst q
            change (11 : ZMod 729416238121)^125307720 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 348077 := Nat.prime_eq_prime_of_dvd_pow hq prime_348077 hd
            subst q
            change (11 : ZMod 729416238121)^2095560 ≠ 1
            reduce_mod_char
            decide

theorem prime_735091890679 : Nat.Prime 735091890679 := by
  apply lucas_primality 735091890679 (3 : ZMod 735091890679)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 735091890679 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((23 : ℕ)^1 * ((149 : ℕ)^1 * ((919 : ℕ)^1 * ((12967 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 735091890679)^367545945339 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 735091890679)^245030630226 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (3 : ZMod 735091890679)^31960516986 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
            subst q
            change (3 : ZMod 735091890679)^4933502622 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 919 := Nat.prime_eq_prime_of_dvd_pow hq prime_919 hd
              subst q
              change (3 : ZMod 735091890679)^799882362 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 12967 := Nat.prime_eq_prime_of_dvd_pow hq prime_12967 hd
              subst q
              change (3 : ZMod 735091890679)^56689434 ≠ 1
              reduce_mod_char
              decide

theorem prime_738676666333 : Nat.Prime 738676666333 := by
  apply lucas_primality 738676666333 (2 : ZMod 738676666333)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 738676666333 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((43 : ℕ)^1 * ((43380119 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 738676666333)^369338333166 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 738676666333)^246225555444 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 738676666333)^67152424212 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (2 : ZMod 738676666333)^17178527124 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 43380119 := Nat.prime_eq_prime_of_dvd_pow hq prime_43380119 hd
            subst q
            change (2 : ZMod 738676666333)^17028 ≠ 1
            reduce_mod_char
            decide

theorem prime_752642312801 : Nat.Prime 752642312801 := by
  apply lucas_primality 752642312801 (3 : ZMod 752642312801)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 752642312801 - 1 = (2 : ℕ)^5 * ((5 : ℕ)^2 * ((7 : ℕ)^2 * ((29 : ℕ)^1 * ((43 : ℕ)^1 * ((89 : ℕ)^1 * ((173 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 752642312801)^376321156400 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 752642312801)^150528462560 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 752642312801)^107520330400 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (3 : ZMod 752642312801)^25953183200 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
              subst q
              change (3 : ZMod 752642312801)^17503309600 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
                subst q
                change (3 : ZMod 752642312801)^8456655200 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
                subst q
                change (3 : ZMod 752642312801)^4350533600 ≠ 1
                reduce_mod_char
                decide

theorem prime_768506768191 : Nat.Prime 768506768191 := by
  apply lucas_primality 768506768191 (12 : ZMod 768506768191)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 768506768191 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((691 : ℕ)^1 * ((1765343 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (12 : ZMod 768506768191)^384253384095 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (12 : ZMod 768506768191)^256168922730 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (12 : ZMod 768506768191)^153701353638 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (12 : ZMod 768506768191)^109786681170 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 691 := Nat.prime_eq_prime_of_dvd_pow hq prime_691 hd
              subst q
              change (12 : ZMod 768506768191)^1112166090 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1765343 := Nat.prime_eq_prime_of_dvd_pow hq prime_1765343 hd
              subst q
              change (12 : ZMod 768506768191)^435330 ≠ 1
              reduce_mod_char
              decide

theorem prime_782757789703 : Nat.Prime 782757789703 := by
  apply lucas_primality 782757789703 (3 : ZMod 782757789703)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 782757789703 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((204437 : ℕ)^1 * ((91163 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 782757789703)^391378894851 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 782757789703)^260919263234 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 782757789703)^111822541386 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 204437 := Nat.prime_eq_prime_of_dvd_pow hq prime_204437 hd
            subst q
            change (3 : ZMod 782757789703)^3828846 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 91163 := Nat.prime_eq_prime_of_dvd_pow hq prime_91163 hd
            subst q
            change (3 : ZMod 782757789703)^8586354 ≠ 1
            reduce_mod_char
            decide

theorem prime_808705572811 : Nat.Prime 808705572811 := by
  apply lucas_primality 808705572811 (10 : ZMod 808705572811)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 808705572811 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((67 : ℕ)^1 * ((402341081 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 808705572811)^404352786405 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 808705572811)^269568524270 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 808705572811)^161741114562 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
            subst q
            change (10 : ZMod 808705572811)^12070232430 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 402341081 := Nat.prime_eq_prime_of_dvd_pow hq prime_402341081 hd
            subst q
            change (10 : ZMod 808705572811)^2010 ≠ 1
            reduce_mod_char
            decide

theorem prime_813736300033 : Nat.Prime 813736300033 := by
  apply lucas_primality 813736300033 (5 : ZMod 813736300033)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 813736300033 - 1 = (2 : ℕ)^9 * ((3 : ℕ)^2 * ((1471 : ℕ)^1 * ((120049 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 813736300033)^406868150016 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 813736300033)^271245433344 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1471 := Nat.prime_eq_prime_of_dvd_pow hq prime_1471 hd
          subst q
          change (5 : ZMod 813736300033)^553185792 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 120049 := Nat.prime_eq_prime_of_dvd_pow hq prime_120049 hd
          subst q
          change (5 : ZMod 813736300033)^6778368 ≠ 1
          reduce_mod_char
          decide

theorem prime_832972004971 : Nat.Prime 832972004971 := by
  apply lucas_primality 832972004971 (10 : ZMod 832972004971)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 832972004971 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((61 : ℕ)^1 * ((71 : ℕ)^1 * ((79 : ℕ)^1 * ((11593 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 832972004971)^416486002485 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 832972004971)^277657334990 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 832972004971)^166594400994 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (10 : ZMod 832972004971)^118996000710 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
              subst q
              change (10 : ZMod 832972004971)^13655278770 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
                subst q
                change (10 : ZMod 832972004971)^11732000070 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
                  subst q
                  change (10 : ZMod 832972004971)^10543949430 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 11593 := Nat.prime_eq_prime_of_dvd_pow hq prime_11593 hd
                  subst q
                  change (10 : ZMod 832972004971)^71851290 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_838572487013 : Nat.Prime 838572487013 := by
  apply lucas_primality 838572487013 (2 : ZMod 838572487013)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 838572487013 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((16126393981 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 838572487013)^419286243506 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 838572487013)^64505575924 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 16126393981 := Nat.prime_eq_prime_of_dvd_pow hq prime_16126393981 hd
        subst q
        change (2 : ZMod 838572487013)^52 ≠ 1
        reduce_mod_char
        decide

theorem prime_842268921113 : Nat.Prime 842268921113 := by
  apply lucas_primality 842268921113 (3 : ZMod 842268921113)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 842268921113 - 1 = (2 : ℕ)^3 * ((55411 : ℕ)^1 * ((1900049 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 842268921113)^421134460556 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 55411 := Nat.prime_eq_prime_of_dvd_pow hq prime_55411 hd
        subst q
        change (3 : ZMod 842268921113)^15200392 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1900049 := Nat.prime_eq_prime_of_dvd_pow hq prime_1900049 hd
        subst q
        change (3 : ZMod 842268921113)^443288 ≠ 1
        reduce_mod_char
        decide

theorem prime_846172739107 : Nat.Prime 846172739107 := by
  apply lucas_primality 846172739107 (2 : ZMod 846172739107)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 846172739107 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^5 * ((29 : ℕ)^1 * ((60037799 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 846172739107)^423086369553 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 846172739107)^282057579702 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (2 : ZMod 846172739107)^29178370314 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 60037799 := Nat.prime_eq_prime_of_dvd_pow hq prime_60037799 hd
          subst q
          change (2 : ZMod 846172739107)^14094 ≠ 1
          reduce_mod_char
          decide

theorem prime_851860373761 : Nat.Prime 851860373761 := by
  apply lucas_primality 851860373761 (7 : ZMod 851860373761)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 851860373761 - 1 = (2 : ℕ)^8 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((61 : ℕ)^1 * ((193 : ℕ)^1 * ((571 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 851860373761)^425930186880 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 851860373761)^283953457920 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 851860373761)^170372074752 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (7 : ZMod 851860373761)^77441852160 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
              subst q
              change (7 : ZMod 851860373761)^13964924160 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
                subst q
                change (7 : ZMod 851860373761)^4413784320 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 571 := Nat.prime_eq_prime_of_dvd_pow hq prime_571 hd
                subst q
                change (7 : ZMod 851860373761)^1491874560 ≠ 1
                reduce_mod_char
                decide

theorem prime_862553341651 : Nat.Prime 862553341651 := by
  apply lucas_primality 862553341651 (2 : ZMod 862553341651)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 862553341651 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((433 : ℕ)^1 * ((13267 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 862553341651)^431276670825 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 862553341651)^287517780550 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 862553341651)^172510668330 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (2 : ZMod 862553341651)^123221905950 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
              subst q
              change (2 : ZMod 862553341651)^78413940150 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
                subst q
                change (2 : ZMod 862553341651)^66350257050 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 433 := Nat.prime_eq_prime_of_dvd_pow hq prime_433 hd
                  subst q
                  change (2 : ZMod 862553341651)^1992040050 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 13267 := Nat.prime_eq_prime_of_dvd_pow hq prime_13267 hd
                  subst q
                  change (2 : ZMod 862553341651)^65014950 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_885675036119 : Nat.Prime 885675036119 := by
  apply lucas_primality 885675036119 (11 : ZMod 885675036119)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 885675036119 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((19253805133 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 885675036119)^442837518059 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (11 : ZMod 885675036119)^38507610266 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 19253805133 := Nat.prime_eq_prime_of_dvd_pow hq prime_19253805133 hd
        subst q
        change (11 : ZMod 885675036119)^46 ≠ 1
        reduce_mod_char
        decide

end LegendreK6.Pratt
