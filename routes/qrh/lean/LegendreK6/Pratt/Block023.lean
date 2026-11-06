import LegendreK6.Pratt.Block022

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LegendreK6.Pratt

theorem prime_28910698749983387 : Nat.Prime 28910698749983387 := by
  apply lucas_primality 28910698749983387 (2 : ZMod 28910698749983387)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 28910698749983387 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((2065049910713099 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 28910698749983387)^14455349374991693 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 28910698749983387)^4130099821426198 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2065049910713099 := Nat.prime_eq_prime_of_dvd_pow hq prime_2065049910713099 hd
        subst q
        change (2 : ZMod 28910698749983387)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_29225227377515669 : Nat.Prime 29225227377515669 := by
  apply lucas_primality 29225227377515669 (2 : ZMod 29225227377515669)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 29225227377515669 - 1 = (2 : ℕ)^2 * ((17 : ℕ)^1 * ((751813 : ℕ)^1 * ((571661777 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 29225227377515669)^14612613688757834 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 29225227377515669)^1719131022206804 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 751813 := Nat.prime_eq_prime_of_dvd_pow hq prime_751813 hd
          subst q
          change (2 : ZMod 29225227377515669)^38873000836 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 571661777 := Nat.prime_eq_prime_of_dvd_pow hq prime_571661777 hd
          subst q
          change (2 : ZMod 29225227377515669)^51123284 ≠ 1
          reduce_mod_char
          decide

theorem prime_29542602396307459 : Nat.Prime 29542602396307459 := by
  apply lucas_primality 29542602396307459 (2 : ZMod 29542602396307459)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 29542602396307459 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((43 : ℕ)^1 * ((27739 : ℕ)^1 * ((4127986259 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 29542602396307459)^14771301198153729 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 29542602396307459)^9847534132102486 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (2 : ZMod 29542602396307459)^687037265030406 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 27739 := Nat.prime_eq_prime_of_dvd_pow hq prime_27739 hd
            subst q
            change (2 : ZMod 29542602396307459)^1065020454822 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 4127986259 := Nat.prime_eq_prime_of_dvd_pow hq prime_4127986259 hd
            subst q
            change (2 : ZMod 29542602396307459)^7156662 ≠ 1
            reduce_mod_char
            decide

theorem prime_29692220205922093 : Nat.Prime 29692220205922093 := by
  apply lucas_primality 29692220205922093 (2 : ZMod 29692220205922093)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 29692220205922093 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((71 : ℕ)^1 * ((109 : ℕ)^1 * ((181 : ℕ)^1 * ((547 : ℕ)^1 * ((3943 : ℕ)^1)))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 29692220205922093)^14846110102961046 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 29692220205922093)^9897406735307364 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 29692220205922093)^4241745743703156 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (2 : ZMod 29692220205922093)^2284016938917084 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
              subst q
              change (2 : ZMod 29692220205922093)^418200284590452 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
                subst q
                change (2 : ZMod 29692220205922093)^272405689962588 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 181 := Nat.prime_eq_prime_of_dvd_pow hq prime_181 hd
                  subst q
                  change (2 : ZMod 29692220205922093)^164045415502332 ≠ 1
                  reduce_mod_char
                  decide
                · rcases hq.dvd_mul.mp hd with hd | hd
                  · have heq : q = 547 := Nat.prime_eq_prime_of_dvd_pow hq prime_547 hd
                    subst q
                    change (2 : ZMod 29692220205922093)^54281938219236 ≠ 1
                    reduce_mod_char
                    decide
                  · have heq : q = 3943 := Nat.prime_eq_prime_of_dvd_pow hq prime_3943 hd
                    subst q
                    change (2 : ZMod 29692220205922093)^7530362720244 ≠ 1
                    reduce_mod_char
                    decide

theorem prime_29862844376368253 : Nat.Prime 29862844376368253 := by
  apply lucas_primality 29862844376368253 (2 : ZMod 29862844376368253)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 29862844376368253 - 1 = (2 : ℕ)^2 * ((151 : ℕ)^1 * ((437809 : ℕ)^1 * ((112930057 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 29862844376368253)^14931422188184126 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
        subst q
        change (2 : ZMod 29862844376368253)^197767181300452 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 437809 := Nat.prime_eq_prime_of_dvd_pow hq prime_437809 hd
          subst q
          change (2 : ZMod 29862844376368253)^68209754428 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 112930057 := Nat.prime_eq_prime_of_dvd_pow hq prime_112930057 hd
          subst q
          change (2 : ZMod 29862844376368253)^264436636 ≠ 1
          reduce_mod_char
          decide

theorem prime_30185973998996567 : Nat.Prime 30185973998996567 := by
  apply lucas_primality 30185973998996567 (5 : ZMod 30185973998996567)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 30185973998996567 - 1 = (2 : ℕ)^1 * ((97 : ℕ)^2 * ((103 : ℕ)^1 * ((15573796829 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 30185973998996567)^15092986999498283 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
        subst q
        change (5 : ZMod 30185973998996567)^311195608237078 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
          subst q
          change (5 : ZMod 30185973998996567)^293067708728122 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 15573796829 := Nat.prime_eq_prime_of_dvd_pow hq prime_15573796829 hd
          subst q
          change (5 : ZMod 30185973998996567)^1938254 ≠ 1
          reduce_mod_char
          decide

theorem prime_30512012057180663 : Nat.Prime 30512012057180663 := by
  apply lucas_primality 30512012057180663 (7 : ZMod 30512012057180663)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 30512012057180663 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((6577 : ℕ)^1 * ((883627 : ℕ)^1 * ((154417 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 30512012057180663)^15256006028590331 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (7 : ZMod 30512012057180663)^1794824238657686 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 6577 := Nat.prime_eq_prime_of_dvd_pow hq prime_6577 hd
          subst q
          change (7 : ZMod 30512012057180663)^4639199035606 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 883627 := Nat.prime_eq_prime_of_dvd_pow hq prime_883627 hd
            subst q
            change (7 : ZMod 30512012057180663)^34530420706 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 154417 := Nat.prime_eq_prime_of_dvd_pow hq prime_154417 hd
            subst q
            change (7 : ZMod 30512012057180663)^197594902486 ≠ 1
            reduce_mod_char
            decide

theorem prime_30840979456000069 : Nat.Prime 30840979456000069 := by
  apply lucas_primality 30840979456000069 (2 : ZMod 30840979456000069)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 30840979456000069 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((137 : ℕ)^1 * ((379 : ℕ)^1 * ((1571 : ℕ)^1 * ((31507283 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 30840979456000069)^15420489728000034 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 30840979456000069)^10280326485333356 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
          subst q
          change (2 : ZMod 30840979456000069)^225116638364964 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 379 := Nat.prime_eq_prime_of_dvd_pow hq prime_379 hd
            subst q
            change (2 : ZMod 30840979456000069)^81374615978892 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1571 := Nat.prime_eq_prime_of_dvd_pow hq prime_1571 hd
              subst q
              change (2 : ZMod 30840979456000069)^19631431862508 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 31507283 := Nat.prime_eq_prime_of_dvd_pow hq prime_31507283 hd
              subst q
              change (2 : ZMod 30840979456000069)^978852396 ≠ 1
              reduce_mod_char
              decide

theorem prime_31172897213027371 : Nat.Prime 31172897213027371 := by
  apply lucas_primality 31172897213027371 (2 : ZMod 31172897213027371)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 31172897213027371 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((1553 : ℕ)^1 * ((20249 : ℕ)^1 * ((11014369 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 31172897213027371)^15586448606513685 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 31172897213027371)^10390965737675790 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 31172897213027371)^6234579442605474 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1553 := Nat.prime_eq_prime_of_dvd_pow hq prime_1553 hd
            subst q
            change (2 : ZMod 31172897213027371)^20072696209290 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 20249 := Nat.prime_eq_prime_of_dvd_pow hq prime_20249 hd
              subst q
              change (2 : ZMod 31172897213027371)^1539478355130 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 11014369 := Nat.prime_eq_prime_of_dvd_pow hq prime_11014369 hd
              subst q
              change (2 : ZMod 31172897213027371)^2830202730 ≠ 1
              reduce_mod_char
              decide

theorem prime_31507786458731587 : Nat.Prime 31507786458731587 := by
  apply lucas_primality 31507786458731587 (2 : ZMod 31507786458731587)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 31507786458731587 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((43 : ℕ)^1 * ((3347 : ℕ)^1 * ((36487362811 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 31507786458731587)^15753893229365793 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 31507786458731587)^10502595486243862 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (2 : ZMod 31507786458731587)^732739219970502 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3347 := Nat.prime_eq_prime_of_dvd_pow hq prime_3347 hd
            subst q
            change (2 : ZMod 31507786458731587)^9413739605238 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 36487362811 := Nat.prime_eq_prime_of_dvd_pow hq prime_36487362811 hd
            subst q
            change (2 : ZMod 31507786458731587)^863526 ≠ 1
            reduce_mod_char
            decide

theorem prime_31845668436881231 : Nat.Prime 31845668436881231 := by
  apply lucas_primality 31845668436881231 (7 : ZMod 31845668436881231)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 31845668436881231 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((17 : ℕ)^2 * ((11019262434907 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 31845668436881231)^15922834218440615 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 31845668436881231)^6369133687376246 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (7 : ZMod 31845668436881231)^1873274613934190 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11019262434907 := Nat.prime_eq_prime_of_dvd_pow hq prime_11019262434907 hd
          subst q
          change (7 : ZMod 31845668436881231)^2890 ≠ 1
          reduce_mod_char
          decide

theorem prime_32186564504948831 : Nat.Prime 32186564504948831 := by
  apply lucas_primality 32186564504948831 (19 : ZMod 32186564504948831)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32186564504948831 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((47 : ℕ)^1 * ((67 : ℕ)^1 * ((1022120181167 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 32186564504948831)^16093282252474415 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (19 : ZMod 32186564504948831)^6437312900989766 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (19 : ZMod 32186564504948831)^684820521381890 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
            subst q
            change (19 : ZMod 32186564504948831)^480396485148490 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1022120181167 := Nat.prime_eq_prime_of_dvd_pow hq prime_1022120181167 hd
            subst q
            change (19 : ZMod 32186564504948831)^31490 ≠ 1
            reduce_mod_char
            decide

theorem prime_32471739303365423 : Nat.Prime 32471739303365423 := by
  apply lucas_primality 32471739303365423 (5 : ZMod 32471739303365423)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32471739303365423 - 1 = (2 : ℕ)^1 * ((19961 : ℕ)^1 * ((892579 : ℕ)^1 * ((911269 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 32471739303365423)^16235869651682711 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19961 := Nat.prime_eq_prime_of_dvd_pow hq prime_19961 hd
        subst q
        change (5 : ZMod 32471739303365423)^1626759145502 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 892579 := Nat.prime_eq_prime_of_dvd_pow hq prime_892579 hd
          subst q
          change (5 : ZMod 32471739303365423)^36379681018 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 911269 := Nat.prime_eq_prime_of_dvd_pow hq prime_911269 hd
          subst q
          change (5 : ZMod 32471739303365423)^35633538838 ≠ 1
          reduce_mod_char
          decide

theorem prime_32530496134515703 : Nat.Prime 32530496134515703 := by
  apply lucas_primality 32530496134515703 (5 : ZMod 32530496134515703)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32530496134515703 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((59 : ℕ)^1 * ((885509 : ℕ)^1 * ((103775407 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 32530496134515703)^16265248067257851 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 32530496134515703)^10843498711505234 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (5 : ZMod 32530496134515703)^551364341262978 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 885509 := Nat.prime_eq_prime_of_dvd_pow hq prime_885509 hd
            subst q
            change (5 : ZMod 32530496134515703)^36736494078 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 103775407 := Nat.prime_eq_prime_of_dvd_pow hq prime_103775407 hd
            subst q
            change (5 : ZMod 32530496134515703)^313470186 ≠ 1
            reduce_mod_char
            decide

theorem prime_32877484911678061 : Nat.Prime 32877484911678061 := by
  apply lucas_primality 32877484911678061 (2 : ZMod 32877484911678061)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 32877484911678061 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((5273 : ℕ)^1 * ((34639236479 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 32877484911678061)^16438742455839030 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 32877484911678061)^10959161637226020 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 32877484911678061)^6575496982335612 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 5273 := Nat.prime_eq_prime_of_dvd_pow hq prime_5273 hd
            subst q
            change (2 : ZMod 32877484911678061)^6235062566220 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 34639236479 := Nat.prime_eq_prime_of_dvd_pow hq prime_34639236479 hd
            subst q
            change (2 : ZMod 32877484911678061)^949140 ≠ 1
            reduce_mod_char
            decide

theorem prime_33227552537453171 : Nat.Prime 33227552537453171 := by
  apply lucas_primality 33227552537453171 (2 : ZMod 33227552537453171)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 33227552537453171 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((2473 : ℕ)^1 * ((28573 : ℕ)^1 * ((3617221 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 33227552537453171)^16613776268726585 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 33227552537453171)^6645510507490634 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 33227552537453171)^2555965579804090 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2473 := Nat.prime_eq_prime_of_dvd_pow hq prime_2473 hd
            subst q
            change (2 : ZMod 33227552537453171)^13436131232290 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 28573 := Nat.prime_eq_prime_of_dvd_pow hq prime_28573 hd
              subst q
              change (2 : ZMod 33227552537453171)^1162900379290 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 3617221 := Nat.prime_eq_prime_of_dvd_pow hq prime_3617221 hd
              subst q
              change (2 : ZMod 33227552537453171)^9185933770 ≠ 1
              reduce_mod_char
              decide

theorem prime_33580720828186639 : Nat.Prime 33580720828186639 := by
  apply lucas_primality 33580720828186639 (3 : ZMod 33580720828186639)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 33580720828186639 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((139 : ℕ)^1 * ((1129 : ℕ)^1 * ((22091 : ℕ)^1 * ((1614413 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 33580720828186639)^16790360414093319 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 33580720828186639)^11193573609395546 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
          subst q
          change (3 : ZMod 33580720828186639)^241587919627242 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1129 := Nat.prime_eq_prime_of_dvd_pow hq prime_1129 hd
            subst q
            change (3 : ZMod 33580720828186639)^29743773984222 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 22091 := Nat.prime_eq_prime_of_dvd_pow hq prime_22091 hd
              subst q
              change (3 : ZMod 33580720828186639)^1520108679018 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1614413 := Nat.prime_eq_prime_of_dvd_pow hq prime_1614413 hd
              subst q
              change (3 : ZMod 33580720828186639)^20800576326 ≠ 1
              reduce_mod_char
              decide

theorem prime_33727061084259161 : Nat.Prime 33727061084259161 := by
  apply lucas_primality 33727061084259161 (3 : ZMod 33727061084259161)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 33727061084259161 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((61 : ℕ)^1 * ((373 : ℕ)^1 * ((37057817743 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 33727061084259161)^16863530542129580 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 33727061084259161)^6745412216851832 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (3 : ZMod 33727061084259161)^552902640725560 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 373 := Nat.prime_eq_prime_of_dvd_pow hq prime_373 hd
            subst q
            change (3 : ZMod 33727061084259161)^90421075292920 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 37057817743 := Nat.prime_eq_prime_of_dvd_pow hq prime_37057817743 hd
            subst q
            change (3 : ZMod 33727061084259161)^910120 ≠ 1
            reduce_mod_char
            decide

theorem prime_33937011715960163 : Nat.Prime 33937011715960163 := by
  apply lucas_primality 33937011715960163 (2 : ZMod 33937011715960163)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 33937011715960163 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((13109 : ℕ)^1 * ((22937 : ℕ)^1 * ((3319621 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 33937011715960163)^16968505857980081 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 33937011715960163)^1996294806821186 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13109 := Nat.prime_eq_prime_of_dvd_pow hq prime_13109 hd
          subst q
          change (2 : ZMod 33937011715960163)^2588832993818 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 22937 := Nat.prime_eq_prime_of_dvd_pow hq prime_22937 hd
            subst q
            change (2 : ZMod 33937011715960163)^1479574997426 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3319621 := Nat.prime_eq_prime_of_dvd_pow hq prime_3319621 hd
            subst q
            change (2 : ZMod 33937011715960163)^10223158522 ≠ 1
            reduce_mod_char
            decide

theorem prime_34296447249000011 : Nat.Prime 34296447249000011 := by
  apply lucas_primality 34296447249000011 (2 : ZMod 34296447249000011)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34296447249000011 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((37 : ℕ)^1 * ((1451 : ℕ)^1 * ((63882219623 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 34296447249000011)^17148223624500005 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 34296447249000011)^6859289449800002 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (2 : ZMod 34296447249000011)^926931006729730 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1451 := Nat.prime_eq_prime_of_dvd_pow hq prime_1451 hd
            subst q
            change (2 : ZMod 34296447249000011)^23636421260510 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 63882219623 := Nat.prime_eq_prime_of_dvd_pow hq prime_63882219623 hd
            subst q
            change (2 : ZMod 34296447249000011)^536870 ≠ 1
            reduce_mod_char
            decide

theorem prime_34659049592086937 : Nat.Prime 34659049592086937 := by
  apply lucas_primality 34659049592086937 (3 : ZMod 34659049592086937)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 34659049592086937 - 1 = (2 : ℕ)^3 * ((31 : ℕ)^1 * ((6792977 : ℕ)^1 * ((20573341 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 34659049592086937)^17329524796043468 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (3 : ZMod 34659049592086937)^1118033857809256 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 6792977 := Nat.prime_eq_prime_of_dvd_pow hq prime_6792977 hd
          subst q
          change (3 : ZMod 34659049592086937)^5102188568 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 20573341 := Nat.prime_eq_prime_of_dvd_pow hq prime_20573341 hd
          subst q
          change (3 : ZMod 34659049592086937)^1684658296 ≠ 1
          reduce_mod_char
          decide

theorem prime_35024841026965577 : Nat.Prime 35024841026965577 := by
  apply lucas_primality 35024841026965577 (3 : ZMod 35024841026965577)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 35024841026965577 - 1 = (2 : ℕ)^3 * ((43019 : ℕ)^1 * ((101771429563 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 35024841026965577)^17512420513482788 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 43019 := Nat.prime_eq_prime_of_dvd_pow hq prime_43019 hd
        subst q
        change (3 : ZMod 35024841026965577)^814171436504 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 101771429563 := Nat.prime_eq_prime_of_dvd_pow hq prime_101771429563 hd
        subst q
        change (3 : ZMod 35024841026965577)^344152 ≠ 1
        reduce_mod_char
        decide

theorem prime_35393843952755461 : Nat.Prime 35393843952755461 := by
  apply lucas_primality 35393843952755461 (6 : ZMod 35393843952755461)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 35393843952755461 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((163 : ℕ)^1 * ((1206334149719 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 35393843952755461)^17696921976377730 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 35393843952755461)^11797947984251820 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 35393843952755461)^7078768790551092 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
            subst q
            change (6 : ZMod 35393843952755461)^217140146949420 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1206334149719 := Nat.prime_eq_prime_of_dvd_pow hq prime_1206334149719 hd
            subst q
            change (6 : ZMod 35393843952755461)^29340 ≠ 1
            reduce_mod_char
            decide

theorem prime_35639951553184091 : Nat.Prime 35639951553184091 := by
  apply lucas_primality 35639951553184091 (2 : ZMod 35639951553184091)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 35639951553184091 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((21529 : ℕ)^1 * ((23649132103 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 35639951553184091)^17819975776592045 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 35639951553184091)^7127990310636818 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 35639951553184091)^5091421650454870 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 21529 := Nat.prime_eq_prime_of_dvd_pow hq prime_21529 hd
            subst q
            change (2 : ZMod 35639951553184091)^1655439247210 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 23649132103 := Nat.prime_eq_prime_of_dvd_pow hq prime_23649132103 hd
            subst q
            change (2 : ZMod 35639951553184091)^1507030 ≠ 1
            reduce_mod_char
            decide

theorem prime_35766080886362209 : Nat.Prime 35766080886362209 := by
  apply lucas_primality 35766080886362209 (14 : ZMod 35766080886362209)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 35766080886362209 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((43 : ℕ)^1 * ((8664263780611 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 35766080886362209)^17883040443181104 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 35766080886362209)^11922026962120736 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (14 : ZMod 35766080886362209)^831769322938656 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 8664263780611 := Nat.prime_eq_prime_of_dvd_pow hq prime_8664263780611 hd
          subst q
          change (14 : ZMod 35766080886362209)^4128 ≠ 1
          reduce_mod_char
          decide

theorem prime_35859952588834837 : Nat.Prime 35859952588834837 := by
  apply lucas_primality 35859952588834837 (2 : ZMod 35859952588834837)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 35859952588834837 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((593 : ℕ)^1 * ((36097 : ℕ)^1 * ((201451 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 35859952588834837)^17929976294417418 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 35859952588834837)^11953317529611612 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 35859952588834837)^5122850369833548 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (2 : ZMod 35859952588834837)^3259995689894076 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 593 := Nat.prime_eq_prime_of_dvd_pow hq prime_593 hd
              subst q
              change (2 : ZMod 35859952588834837)^60472095428052 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 36097 := Nat.prime_eq_prime_of_dvd_pow hq prime_36097 hd
                subst q
                change (2 : ZMod 35859952588834837)^993433043988 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 201451 := Nat.prime_eq_prime_of_dvd_pow hq prime_201451 hd
                subst q
                change (2 : ZMod 35859952588834837)^178008312636 ≠ 1
                reduce_mod_char
                decide

theorem prime_36141574462890641 : Nat.Prime 36141574462890641 := by
  apply lucas_primality 36141574462890641 (3 : ZMod 36141574462890641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 36141574462890641 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((1489 : ℕ)^1 * ((303404755397 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 36141574462890641)^18070787231445320 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 36141574462890641)^7228314892578128 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1489 := Nat.prime_eq_prime_of_dvd_pow hq prime_1489 hd
          subst q
          change (3 : ZMod 36141574462890641)^24272380431760 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 303404755397 := Nat.prime_eq_prime_of_dvd_pow hq prime_303404755397 hd
          subst q
          change (3 : ZMod 36141574462890641)^119120 ≠ 1
          reduce_mod_char
          decide

theorem prime_36520347436056593 : Nat.Prime 36520347436056593 := by
  apply lucas_primality 36520347436056593 (3 : ZMod 36520347436056593)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 36520347436056593 - 1 = (2 : ℕ)^4 * ((2529361 : ℕ)^1 * ((902410417 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 36520347436056593)^18260173718028296 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 2529361 := Nat.prime_eq_prime_of_dvd_pow hq prime_2529361 hd
        subst q
        change (3 : ZMod 36520347436056593)^14438566672 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 902410417 := Nat.prime_eq_prime_of_dvd_pow hq prime_902410417 hd
        subst q
        change (3 : ZMod 36520347436056593)^40469776 ≠ 1
        reduce_mod_char
        decide

theorem prime_36902422678601111 : Nat.Prime 36902422678601111 := by
  apply lucas_primality 36902422678601111 (11 : ZMod 36902422678601111)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 36902422678601111 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((3690242267860111 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 36902422678601111)^18451211339300555 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 36902422678601111)^7380484535720222 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3690242267860111 := Nat.prime_eq_prime_of_dvd_pow hq prime_3690242267860111 hd
        subst q
        change (11 : ZMod 36902422678601111)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_37018604205637643 : Nat.Prime 37018604205637643 := by
  apply lucas_primality 37018604205637643 (2 : ZMod 37018604205637643)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 37018604205637643 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((743 : ℕ)^1 * ((3558796789621 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 37018604205637643)^18509302102818821 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 37018604205637643)^5288372029376806 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 743 := Nat.prime_eq_prime_of_dvd_pow hq prime_743 hd
          subst q
          change (2 : ZMod 37018604205637643)^49823155054694 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3558796789621 := Nat.prime_eq_prime_of_dvd_pow hq prime_3558796789621 hd
          subst q
          change (2 : ZMod 37018604205637643)^10402 ≠ 1
          reduce_mod_char
          decide

theorem prime_37287823182704707 : Nat.Prime 37287823182704707 := by
  apply lucas_primality 37287823182704707 (2 : ZMod 37287823182704707)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 37287823182704707 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((921203 : ℕ)^1 * ((6746219017 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 37287823182704707)^18643911591352353 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 37287823182704707)^12429274394234902 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 921203 := Nat.prime_eq_prime_of_dvd_pow hq prime_921203 hd
          subst q
          change (2 : ZMod 37287823182704707)^40477314102 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 6746219017 := Nat.prime_eq_prime_of_dvd_pow hq prime_6746219017 hd
          subst q
          change (2 : ZMod 37287823182704707)^5527218 ≠ 1
          reduce_mod_char
          decide

theorem prime_37676572060402589 : Nat.Prime 37676572060402589 := by
  apply lucas_primality 37676572060402589 (2 : ZMod 37676572060402589)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 37676572060402589 - 1 = (2 : ℕ)^2 * ((17 : ℕ)^1 * ((23 : ℕ)^1 * ((100271 : ℕ)^1 * ((240247727 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 37676572060402589)^18838286030201294 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 37676572060402589)^2216268944729564 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 37676572060402589)^1638111828713156 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 100271 := Nat.prime_eq_prime_of_dvd_pow hq prime_100271 hd
            subst q
            change (2 : ZMod 37676572060402589)^375747445028 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 240247727 := Nat.prime_eq_prime_of_dvd_pow hq prime_240247727 hd
            subst q
            change (2 : ZMod 37676572060402589)^156823844 ≠ 1
            reduce_mod_char
            decide

theorem prime_38068692544000009 : Nat.Prime 38068692544000009 := by
  apply lucas_primality 38068692544000009 (14 : ZMod 38068692544000009)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 38068692544000009 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((11 : ℕ)^1 * ((19 : ℕ)^1 * ((67 : ℕ)^1 * ((1699 : ℕ)^1 * ((7407979 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 38068692544000009)^19034346272000004 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 38068692544000009)^12689564181333336 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (14 : ZMod 38068692544000009)^3460790231272728 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (14 : ZMod 38068692544000009)^2003615397052632 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
              subst q
              change (14 : ZMod 38068692544000009)^568189440955224 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 1699 := Nat.prime_eq_prime_of_dvd_pow hq prime_1699 hd
                subst q
                change (14 : ZMod 38068692544000009)^22406528866392 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 7407979 := Nat.prime_eq_prime_of_dvd_pow hq prime_7407979 hd
                subst q
                change (14 : ZMod 38068692544000009)^5138876952 ≠ 1
                reduce_mod_char
                decide

theorem prime_38464207986489497 : Nat.Prime 38464207986489497 := by
  apply lucas_primality 38464207986489497 (3 : ZMod 38464207986489497)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 38464207986489497 - 1 = (2 : ℕ)^3 * ((1031119 : ℕ)^1 * ((4662920573 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 38464207986489497)^19232103993244748 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1031119 := Nat.prime_eq_prime_of_dvd_pow hq prime_1031119 hd
        subst q
        change (3 : ZMod 38464207986489497)^37303364584 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4662920573 := Nat.prime_eq_prime_of_dvd_pow hq prime_4662920573 hd
        subst q
        change (3 : ZMod 38464207986489497)^8248952 ≠ 1
        reduce_mod_char
        decide

theorem prime_38863141861967429 : Nat.Prime 38863141861967429 := by
  apply lucas_primality 38863141861967429 (2 : ZMod 38863141861967429)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 38863141861967429 - 1 = (2 : ℕ)^2 * ((9715785465491857 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 38863141861967429)^19431570930983714 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 9715785465491857 := Nat.prime_eq_prime_of_dvd_pow hq prime_9715785465491857 hd
      subst q
      change (2 : ZMod 38863141861967429)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_39260200559076061 : Nat.Prime 39260200559076061 := by
  apply lucas_primality 39260200559076061 (6 : ZMod 39260200559076061)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 39260200559076061 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((181 : ℕ)^1 * ((233 : ℕ)^1 * ((23957 : ℕ)^1 * ((647641 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 39260200559076061)^19630100279538030 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 39260200559076061)^13086733519692020 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 39260200559076061)^7852040111815212 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 181 := Nat.prime_eq_prime_of_dvd_pow hq prime_181 hd
            subst q
            change (6 : ZMod 39260200559076061)^216907185409260 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
              subst q
              change (6 : ZMod 39260200559076061)^168498714845820 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 23957 := Nat.prime_eq_prime_of_dvd_pow hq prime_23957 hd
                subst q
                change (6 : ZMod 39260200559076061)^1638777833580 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 647641 := Nat.prime_eq_prime_of_dvd_pow hq prime_647641 hd
                subst q
                change (6 : ZMod 39260200559076061)^60620313660 ≠ 1
                reduce_mod_char
                decide

theorem prime_39265517766052421 : Nat.Prime 39265517766052421 := by
  apply lucas_primality 39265517766052421 (2 : ZMod 39265517766052421)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 39265517766052421 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((6451 : ℕ)^1 * ((7057 : ℕ)^1 * ((43125503 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 39265517766052421)^19632758883026210 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 39265517766052421)^7853103553210484 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 6451 := Nat.prime_eq_prime_of_dvd_pow hq prime_6451 hd
          subst q
          change (2 : ZMod 39265517766052421)^6086733493420 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7057 := Nat.prime_eq_prime_of_dvd_pow hq prime_7057 hd
            subst q
            change (2 : ZMod 39265517766052421)^5564052397060 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 43125503 := Nat.prime_eq_prime_of_dvd_pow hq prime_43125503 hd
            subst q
            change (2 : ZMod 39265517766052421)^910494140 ≠ 1
            reduce_mod_char
            decide

theorem prime_39671359416303697 : Nat.Prime 39671359416303697 := by
  apply lucas_primality 39671359416303697 (5 : ZMod 39671359416303697)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 39671359416303697 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^3 * ((29 : ℕ)^1 * ((174289 : ℕ)^1 * ((18168763 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 39671359416303697)^19835679708151848 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 39671359416303697)^13223786472101232 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (5 : ZMod 39671359416303697)^1367977910907024 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 174289 := Nat.prime_eq_prime_of_dvd_pow hq prime_174289 hd
            subst q
            change (5 : ZMod 39671359416303697)^227618262864 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 18168763 := Nat.prime_eq_prime_of_dvd_pow hq prime_18168763 hd
            subst q
            change (5 : ZMod 39671359416303697)^2183492592 ≠ 1
            reduce_mod_char
            decide

theorem prime_40080690652640629 : Nat.Prime 40080690652640629 := by
  apply lucas_primality 40080690652640629 (7 : ZMod 40080690652640629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 40080690652640629 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((103 : ℕ)^1 * ((32427743246473 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 40080690652640629)^20040345326320314 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 40080690652640629)^13360230217546876 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
          subst q
          change (7 : ZMod 40080690652640629)^389132918957676 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 32427743246473 := Nat.prime_eq_prime_of_dvd_pow hq prime_32427743246473 hd
          subst q
          change (7 : ZMod 40080690652640629)^1236 ≠ 1
          reduce_mod_char
          decide

theorem prime_40493535437763269 : Nat.Prime 40493535437763269 := by
  apply lucas_primality 40493535437763269 (2 : ZMod 40493535437763269)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 40493535437763269 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^2 * ((17 : ℕ)^1 * ((1481 : ℕ)^1 * ((4943 : ℕ)^1 * ((1660103 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 40493535437763269)^20246767718881634 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 40493535437763269)^5784790776823324 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 40493535437763269)^2381972672809604 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1481 := Nat.prime_eq_prime_of_dvd_pow hq prime_1481 hd
            subst q
            change (2 : ZMod 40493535437763269)^27342022577828 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 4943 := Nat.prime_eq_prime_of_dvd_pow hq prime_4943 hd
              subst q
              change (2 : ZMod 40493535437763269)^8192096993276 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1660103 := Nat.prime_eq_prime_of_dvd_pow hq prime_1660103 hd
              subst q
              change (2 : ZMod 40493535437763269)^24392182556 ≠ 1
              reduce_mod_char
              decide

theorem prime_40786687721081641 : Nat.Prime 40786687721081641 := by
  apply lucas_primality 40786687721081641 (14 : ZMod 40786687721081641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 40786687721081641 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((23 : ℕ)^1 * ((631 : ℕ)^1 * ((677 : ℕ)^1 * ((719 : ℕ)^1 * ((3701 : ℕ)^1)))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 40786687721081641)^20393343860540820 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 40786687721081641)^13595562573693880 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (14 : ZMod 40786687721081641)^8157337544216328 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (14 : ZMod 40786687721081641)^3137437517006280 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
              subst q
              change (14 : ZMod 40786687721081641)^1773334248742680 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 631 := Nat.prime_eq_prime_of_dvd_pow hq prime_631 hd
                subst q
                change (14 : ZMod 40786687721081641)^64638173884440 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 677 := Nat.prime_eq_prime_of_dvd_pow hq prime_677 hd
                  subst q
                  change (14 : ZMod 40786687721081641)^60246215245320 ≠ 1
                  reduce_mod_char
                  decide
                · rcases hq.dvd_mul.mp hd with hd | hd
                  · have heq : q = 719 := Nat.prime_eq_prime_of_dvd_pow hq prime_719 hd
                    subst q
                    change (14 : ZMod 40786687721081641)^56726964841560 ≠ 1
                    reduce_mod_char
                    decide
                  · have heq : q = 3701 := Nat.prime_eq_prime_of_dvd_pow hq prime_3701 hd
                    subst q
                    change (14 : ZMod 40786687721081641)^11020450613640 ≠ 1
                    reduce_mod_char
                    decide

theorem prime_40909917857572091 : Nat.Prime 40909917857572091 := by
  apply lucas_primality 40909917857572091 (2 : ZMod 40909917857572091)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 40909917857572091 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((509 : ℕ)^1 * ((472783056253 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 40909917857572091)^20454958928786045 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 40909917857572091)^8181983571514418 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 40909917857572091)^2406465756327770 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 509 := Nat.prime_eq_prime_of_dvd_pow hq prime_509 hd
            subst q
            change (2 : ZMod 40909917857572091)^80373119563010 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 472783056253 := Nat.prime_eq_prime_of_dvd_pow hq prime_472783056253 hd
            subst q
            change (2 : ZMod 40909917857572091)^86530 ≠ 1
            reduce_mod_char
            decide

theorem prime_41329862121590797 : Nat.Prime 41329862121590797 := by
  apply lucas_primality 41329862121590797 (2 : ZMod 41329862121590797)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 41329862121590797 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((673 : ℕ)^1 * ((393662724517 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 41329862121590797)^20664931060795398 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 41329862121590797)^13776620707196932 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 41329862121590797)^3179220163199292 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 673 := Nat.prime_eq_prime_of_dvd_pow hq prime_673 hd
            subst q
            change (2 : ZMod 41329862121590797)^61411385024652 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 393662724517 := Nat.prime_eq_prime_of_dvd_pow hq prime_393662724517 hd
            subst q
            change (2 : ZMod 41329862121590797)^104988 ≠ 1
            reduce_mod_char
            decide

theorem prime_41341833271014641 : Nat.Prime 41341833271014641 := by
  apply lucas_primality 41341833271014641 (3 : ZMod 41341833271014641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 41341833271014641 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((31 : ℕ)^1 * ((163 : ℕ)^1 * ((593 : ℕ)^1 * ((877 : ℕ)^1 * ((2161 : ℕ)^1)))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 41341833271014641)^20670916635507320 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 41341833271014641)^8268366654202928 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 41341833271014641)^5905976181573520 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (3 : ZMod 41341833271014641)^3180141020847280 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
              subst q
              change (3 : ZMod 41341833271014641)^1333607524871440 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
                subst q
                change (3 : ZMod 41341833271014641)^253630878963280 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 593 := Nat.prime_eq_prime_of_dvd_pow hq prime_593 hd
                  subst q
                  change (3 : ZMod 41341833271014641)^69716413610480 ≠ 1
                  reduce_mod_char
                  decide
                · rcases hq.dvd_mul.mp hd with hd | hd
                  · have heq : q = 877 := Nat.prime_eq_prime_of_dvd_pow hq prime_877 hd
                    subst q
                    change (3 : ZMod 41341833271014641)^47140060742320 ≠ 1
                    reduce_mod_char
                    decide
                  · have heq : q = 2161 := Nat.prime_eq_prime_of_dvd_pow hq prime_2161 hd
                    subst q
                    change (3 : ZMod 41341833271014641)^19130880736240 ≠ 1
                    reduce_mod_char
                    decide

theorem prime_41729113658021123 : Nat.Prime 41729113658021123 := by
  apply lucas_primality 41729113658021123 (2 : ZMod 41729113658021123)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 41729113658021123 - 1 = (2 : ℕ)^1 * ((53 : ℕ)^1 * ((5501 : ℕ)^1 * ((71563512737 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 41729113658021123)^20864556829010561 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
        subst q
        change (2 : ZMod 41729113658021123)^787341767132474 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5501 := Nat.prime_eq_prime_of_dvd_pow hq prime_5501 hd
          subst q
          change (2 : ZMod 41729113658021123)^7585732350122 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 71563512737 := Nat.prime_eq_prime_of_dvd_pow hq prime_71563512737 hd
          subst q
          change (2 : ZMod 41729113658021123)^583106 ≠ 1
          reduce_mod_char
          decide

theorem prime_41753392563388043 : Nat.Prime 41753392563388043 := by
  apply lucas_primality 41753392563388043 (2 : ZMod 41753392563388043)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 41753392563388043 - 1 = (2 : ℕ)^1 * ((1117 : ℕ)^1 * ((130261 : ℕ)^1 * ((143480933 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 41753392563388043)^20876696281694021 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1117 := Nat.prime_eq_prime_of_dvd_pow hq prime_1117 hd
        subst q
        change (2 : ZMod 41753392563388043)^37379939627026 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 130261 := Nat.prime_eq_prime_of_dvd_pow hq prime_130261 hd
          subst q
          change (2 : ZMod 41753392563388043)^320536404322 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 143480933 := Nat.prime_eq_prime_of_dvd_pow hq prime_143480933 hd
          subst q
          change (2 : ZMod 41753392563388043)^291003074 ≠ 1
          reduce_mod_char
          decide

theorem prime_42180533641000003 : Nat.Prime 42180533641000003 := by
  apply lucas_primality 42180533641000003 (2 : ZMod 42180533641000003)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 42180533641000003 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((34313 : ℕ)^1 * ((204881209459 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 42180533641000003)^21090266820500001 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 42180533641000003)^14060177880333334 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 34313 := Nat.prime_eq_prime_of_dvd_pow hq prime_34313 hd
          subst q
          change (2 : ZMod 42180533641000003)^1229287256754 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 204881209459 := Nat.prime_eq_prime_of_dvd_pow hq prime_204881209459 hd
          subst q
          change (2 : ZMod 42180533641000003)^205878 ≠ 1
          reduce_mod_char
          decide

theorem prime_42611309937355073 : Nat.Prime 42611309937355073 := by
  apply lucas_primality 42611309937355073 (3 : ZMod 42611309937355073)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 42611309937355073 - 1 = (2 : ℕ)^6 * ((19 : ℕ)^1 * ((35042195672167 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 42611309937355073)^21305654968677536 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (3 : ZMod 42611309937355073)^2242700523018688 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 35042195672167 := Nat.prime_eq_prime_of_dvd_pow hq prime_35042195672167 hd
        subst q
        change (3 : ZMod 42611309937355073)^1216 ≠ 1
        reduce_mod_char
        decide

theorem prime_43045746160697453 : Nat.Prime 43045746160697453 := by
  apply lucas_primality 43045746160697453 (2 : ZMod 43045746160697453)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 43045746160697453 - 1 = (2 : ℕ)^2 * ((31 : ℕ)^1 * ((307 : ℕ)^1 * ((1404937 : ℕ)^1 * ((804847 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 43045746160697453)^21522873080348726 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (2 : ZMod 43045746160697453)^1388572456796692 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 307 := Nat.prime_eq_prime_of_dvd_pow hq prime_307 hd
          subst q
          change (2 : ZMod 43045746160697453)^140214156875236 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1404937 := Nat.prime_eq_prime_of_dvd_pow hq prime_1404937 hd
            subst q
            change (2 : ZMod 43045746160697453)^30638915596 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 804847 := Nat.prime_eq_prime_of_dvd_pow hq prime_804847 hd
            subst q
            change (2 : ZMod 43045746160697453)^53483141716 ≠ 1
            reduce_mod_char
            decide

theorem prime_43483867145012509 : Nat.Prime 43483867145012509 := by
  apply lucas_primality 43483867145012509 (2 : ZMod 43483867145012509)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 43483867145012509 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((359 : ℕ)^1 * ((757 : ℕ)^1 * ((98429 : ℕ)^1 * ((135467 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 43483867145012509)^21741933572506254 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 43483867145012509)^14494622381670836 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 359 := Nat.prime_eq_prime_of_dvd_pow hq prime_359 hd
          subst q
          change (2 : ZMod 43483867145012509)^121124978119812 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 757 := Nat.prime_eq_prime_of_dvd_pow hq prime_757 hd
            subst q
            change (2 : ZMod 43483867145012509)^57442360825644 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 98429 := Nat.prime_eq_prime_of_dvd_pow hq prime_98429 hd
              subst q
              change (2 : ZMod 43483867145012509)^441779019852 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 135467 := Nat.prime_eq_prime_of_dvd_pow hq prime_135467 hd
              subst q
              change (2 : ZMod 43483867145012509)^320992323924 ≠ 1
              reduce_mod_char
              decide

theorem prime_43925697850453093 : Nat.Prime 43925697850453093 := by
  apply lucas_primality 43925697850453093 (2 : ZMod 43925697850453093)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 43925697850453093 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((941 : ℕ)^1 * ((1296661289717 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 43925697850453093)^21962848925226546 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 43925697850453093)^14641899283484364 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 941 := Nat.prime_eq_prime_of_dvd_pow hq prime_941 hd
          subst q
          change (2 : ZMod 43925697850453093)^46679806429812 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1296661289717 := Nat.prime_eq_prime_of_dvd_pow hq prime_1296661289717 hd
          subst q
          change (2 : ZMod 43925697850453093)^33876 ≠ 1
          reduce_mod_char
          decide

theorem prime_44371263363765631 : Nat.Prime 44371263363765631 := by
  apply lucas_primality 44371263363765631 (3 : ZMod 44371263363765631)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 44371263363765631 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((1479042112125521 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 44371263363765631)^22185631681882815 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 44371263363765631)^14790421121255210 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 44371263363765631)^8874252672753126 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1479042112125521 := Nat.prime_eq_prime_of_dvd_pow hq prime_1479042112125521 hd
          subst q
          change (3 : ZMod 44371263363765631)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_44820588898717741 : Nat.Prime 44820588898717741 := by
  apply lucas_primality 44820588898717741 (6 : ZMod 44820588898717741)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 44820588898717741 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((71 : ℕ)^1 * ((727 : ℕ)^1 * ((10781 : ℕ)^1 * ((149153 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 44820588898717741)^22410294449358870 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 44820588898717741)^14940196299572580 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 44820588898717741)^8964117779743548 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
            subst q
            change (6 : ZMod 44820588898717741)^631275899981940 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 727 := Nat.prime_eq_prime_of_dvd_pow hq prime_727 hd
              subst q
              change (6 : ZMod 44820588898717741)^61651429021620 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 10781 := Nat.prime_eq_prime_of_dvd_pow hq prime_10781 hd
                subst q
                change (6 : ZMod 44820588898717741)^4157368416540 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 149153 := Nat.prime_eq_prime_of_dvd_pow hq prime_149153 hd
                subst q
                change (6 : ZMod 44820588898717741)^300500753580 ≠ 1
                reduce_mod_char
                decide

theorem prime_45273699796525939 : Nat.Prime 45273699796525939 := by
  apply lucas_primality 45273699796525939 (2 : ZMod 45273699796525939)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 45273699796525939 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((91813 : ℕ)^1 * ((27394873757 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 45273699796525939)^22636849898262969 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 45273699796525939)^15091233265508646 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 91813 := Nat.prime_eq_prime_of_dvd_pow hq prime_91813 hd
          subst q
          change (2 : ZMod 45273699796525939)^493107727626 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 27394873757 := Nat.prime_eq_prime_of_dvd_pow hq prime_27394873757 hd
          subst q
          change (2 : ZMod 45273699796525939)^1652634 ≠ 1
          reduce_mod_char
          decide

theorem prime_45730621526284873 : Nat.Prime 45730621526284873 := by
  apply lucas_primality 45730621526284873 (5 : ZMod 45730621526284873)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 45730621526284873 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((19 : ℕ)^1 * ((2179 : ℕ)^1 * ((19867 : ℕ)^1 * ((257401 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 45730621526284873)^22865310763142436 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 45730621526284873)^15243540508761624 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (5 : ZMod 45730621526284873)^2406874817172888 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2179 := Nat.prime_eq_prime_of_dvd_pow hq prime_2179 hd
            subst q
            change (5 : ZMod 45730621526284873)^20986976377368 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 19867 := Nat.prime_eq_prime_of_dvd_pow hq prime_19867 hd
              subst q
              change (5 : ZMod 45730621526284873)^2301838301016 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 257401 := Nat.prime_eq_prime_of_dvd_pow hq prime_257401 hd
              subst q
              change (5 : ZMod 45730621526284873)^177662952072 ≠ 1
              reduce_mod_char
              decide

theorem prime_46191379685396497 : Nat.Prime 46191379685396497 := by
  apply lucas_primality 46191379685396497 (7 : ZMod 46191379685396497)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 46191379685396497 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((2879927 : ℕ)^1 * ((334147501 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 46191379685396497)^23095689842698248 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 46191379685396497)^15397126561798832 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2879927 := Nat.prime_eq_prime_of_dvd_pow hq prime_2879927 hd
          subst q
          change (7 : ZMod 46191379685396497)^16039080048 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 334147501 := Nat.prime_eq_prime_of_dvd_pow hq prime_334147501 hd
          subst q
          change (7 : ZMod 46191379685396497)^138236496 ≠ 1
          reduce_mod_char
          decide

theorem prime_46656000000000019 : Nat.Prime 46656000000000019 := by
  apply lucas_primality 46656000000000019 (2 : ZMod 46656000000000019)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 46656000000000019 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((19 : ℕ)^1 * ((136421052631579 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 46656000000000019)^23328000000000009 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 46656000000000019)^15552000000000006 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 46656000000000019)^2455578947368422 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 136421052631579 := Nat.prime_eq_prime_of_dvd_pow hq prime_136421052631579 hd
          subst q
          change (2 : ZMod 46656000000000019)^342 ≠ 1
          reduce_mod_char
          decide

theorem prime_47124508325403673 : Nat.Prime 47124508325403673 := by
  apply lucas_primality 47124508325403673 (7 : ZMod 47124508325403673)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 47124508325403673 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((218169020025017 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 47124508325403673)^23562254162701836 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 47124508325403673)^15708169441801224 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 218169020025017 := Nat.prime_eq_prime_of_dvd_pow hq prime_218169020025017 hd
        subst q
        change (7 : ZMod 47124508325403673)^216 ≠ 1
        reduce_mod_char
        decide

theorem prime_47596930646515399 : Nat.Prime 47596930646515399 := by
  apply lucas_primality 47596930646515399 (3 : ZMod 47596930646515399)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 47596930646515399 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((1327 : ℕ)^1 * ((12527 : ℕ)^1 * ((17674451 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 47596930646515399)^23798465323257699 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 47596930646515399)^15865643548838466 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1327 := Nat.prime_eq_prime_of_dvd_pow hq prime_1327 hd
          subst q
          change (3 : ZMod 47596930646515399)^35868071323674 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 12527 := Nat.prime_eq_prime_of_dvd_pow hq prime_12527 hd
            subst q
            change (3 : ZMod 47596930646515399)^3799547429274 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 17674451 := Nat.prime_eq_prime_of_dvd_pow hq prime_17674451 hd
            subst q
            change (3 : ZMod 47596930646515399)^2692979298 ≠ 1
            reduce_mod_char
            decide

theorem prime_48073293078275539 : Nat.Prime 48073293078275539 := by
  apply lucas_primality 48073293078275539 (3 : ZMod 48073293078275539)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 48073293078275539 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((757 : ℕ)^1 * ((3528056148413 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 48073293078275539)^24036646539137769 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 48073293078275539)^16024431026091846 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 757 := Nat.prime_eq_prime_of_dvd_pow hq prime_757 hd
          subst q
          change (3 : ZMod 48073293078275539)^63505010671434 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3528056148413 := Nat.prime_eq_prime_of_dvd_pow hq prime_3528056148413 hd
          subst q
          change (3 : ZMod 48073293078275539)^13626 ≠ 1
          reduce_mod_char
          decide

theorem prime_48553621866090527 : Nat.Prime 48553621866090527 := by
  apply lucas_primality 48553621866090527 (5 : ZMod 48553621866090527)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 48553621866090527 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((613 : ℕ)^1 * ((24749 : ℕ)^1 * ((94129247 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 48553621866090527)^24276810933045263 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (5 : ZMod 48553621866090527)^2856095403887678 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 613 := Nat.prime_eq_prime_of_dvd_pow hq prime_613 hd
          subst q
          change (5 : ZMod 48553621866090527)^79206560956102 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 24749 := Nat.prime_eq_prime_of_dvd_pow hq prime_24749 hd
            subst q
            change (5 : ZMod 48553621866090527)^1961841765974 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 94129247 := Nat.prime_eq_prime_of_dvd_pow hq prime_94129247 hd
            subst q
            change (5 : ZMod 48553621866090527)^515818658 ≠ 1
            reduce_mod_char
            decide

theorem prime_49037943386265629 : Nat.Prime 49037943386265629 := by
  apply lucas_primality 49037943386265629 (2 : ZMod 49037943386265629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 49037943386265629 - 1 = (2 : ℕ)^2 * ((67 : ℕ)^1 * ((182977400695021 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 49037943386265629)^24518971693132814 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
        subst q
        change (2 : ZMod 49037943386265629)^731909602780084 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 182977400695021 := Nat.prime_eq_prime_of_dvd_pow hq prime_182977400695021 hd
        subst q
        change (2 : ZMod 49037943386265629)^268 ≠ 1
        reduce_mod_char
        decide

theorem prime_49526284146440263 : Nat.Prime 49526284146440263 := by
  apply lucas_primality 49526284146440263 (3 : ZMod 49526284146440263)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 49526284146440263 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((121591 : ℕ)^1 * ((9698063521 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 49526284146440263)^24763142073220131 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 49526284146440263)^16508761382146754 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 49526284146440263)^7075183449491466 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 121591 := Nat.prime_eq_prime_of_dvd_pow hq prime_121591 hd
            subst q
            change (3 : ZMod 49526284146440263)^407318667882 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 9698063521 := Nat.prime_eq_prime_of_dvd_pow hq prime_9698063521 hd
            subst q
            change (3 : ZMod 49526284146440263)^5106822 ≠ 1
            reduce_mod_char
            decide

theorem prime_50018670786022853 : Nat.Prime 50018670786022853 := by
  apply lucas_primality 50018670786022853 (2 : ZMod 50018670786022853)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 50018670786022853 - 1 = (2 : ℕ)^2 * ((61 : ℕ)^1 * ((204994552401733 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 50018670786022853)^25009335393011426 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
        subst q
        change (2 : ZMod 50018670786022853)^819978209606932 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 204994552401733 := Nat.prime_eq_prime_of_dvd_pow hq prime_204994552401733 hd
        subst q
        change (2 : ZMod 50018670786022853)^244 ≠ 1
        reduce_mod_char
        decide

theorem prime_50515130076626977 : Nat.Prime 50515130076626977 := by
  apply lucas_primality 50515130076626977 (7 : ZMod 50515130076626977)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 50515130076626977 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((283 : ℕ)^1 * ((1859361383857 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 50515130076626977)^25257565038313488 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 50515130076626977)^16838376692208992 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 283 := Nat.prime_eq_prime_of_dvd_pow hq prime_283 hd
          subst q
          change (7 : ZMod 50515130076626977)^178498692850272 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1859361383857 := Nat.prime_eq_prime_of_dvd_pow hq prime_1859361383857 hd
          subst q
          change (7 : ZMod 50515130076626977)^27168 ≠ 1
          reduce_mod_char
          decide

theorem prime_51015688922507861 : Nat.Prime 51015688922507861 := by
  apply lucas_primality 51015688922507861 (2 : ZMod 51015688922507861)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 51015688922507861 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((1217 : ℕ)^1 * ((123291819137 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 51015688922507861)^25507844461253930 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 51015688922507861)^10203137784501572 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 51015688922507861)^3000922877794580 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1217 := Nat.prime_eq_prime_of_dvd_pow hq prime_1217 hd
            subst q
            change (2 : ZMod 51015688922507861)^41919218506580 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 123291819137 := Nat.prime_eq_prime_of_dvd_pow hq prime_123291819137 hd
            subst q
            change (2 : ZMod 51015688922507861)^413780 ≠ 1
            reduce_mod_char
            decide

theorem prime_51520374361000033 : Nat.Prime 51520374361000033 := by
  apply lucas_primality 51520374361000033 (5 : ZMod 51520374361000033)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 51520374361000033 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((2360459 : ℕ)^1 * ((227358563 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 51520374361000033)^25760187180500016 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 51520374361000033)^17173458120333344 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2360459 := Nat.prime_eq_prime_of_dvd_pow hq prime_2360459 hd
          subst q
          change (5 : ZMod 51520374361000033)^21826422048 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 227358563 := Nat.prime_eq_prime_of_dvd_pow hq prime_227358563 hd
          subst q
          change (5 : ZMod 51520374361000033)^226604064 ≠ 1
          reduce_mod_char
          decide

theorem prime_52029213562955171 : Nat.Prime 52029213562955171 := by
  apply lucas_primality 52029213562955171 (6 : ZMod 52029213562955171)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 52029213562955171 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((1249 : ℕ)^1 * ((4165669620733 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 52029213562955171)^26014606781477585 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 52029213562955171)^10405842712591034 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1249 := Nat.prime_eq_prime_of_dvd_pow hq prime_1249 hd
          subst q
          change (6 : ZMod 52029213562955171)^41656696207330 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4165669620733 := Nat.prime_eq_prime_of_dvd_pow hq prime_4165669620733 hd
          subst q
          change (6 : ZMod 52029213562955171)^12490 ≠ 1
          reduce_mod_char
          decide

theorem prime_52542233833181237 : Nat.Prime 52542233833181237 := by
  apply lucas_primality 52542233833181237 (2 : ZMod 52542233833181237)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 52542233833181237 - 1 = (2 : ℕ)^2 * ((167 : ℕ)^1 * ((5432971 : ℕ)^1 * ((14477537 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 52542233833181237)^26271116916590618 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
        subst q
        change (2 : ZMod 52542233833181237)^314624154689708 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5432971 := Nat.prime_eq_prime_of_dvd_pow hq prime_5432971 hd
          subst q
          change (2 : ZMod 52542233833181237)^9670994716 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 14477537 := Nat.prime_eq_prime_of_dvd_pow hq prime_14477537 hd
          subst q
          change (2 : ZMod 52542233833181237)^3629224628 ≠ 1
          reduce_mod_char
          decide

theorem prime_53059462610881679 : Nat.Prime 53059462610881679 := by
  apply lucas_primality 53059462610881679 (7 : ZMod 53059462610881679)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 53059462610881679 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((19 : ℕ)^1 * ((239 : ℕ)^1 * ((1381 : ℕ)^1 * ((604351537 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 53059462610881679)^26529731305440839 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 53059462610881679)^7579923230125954 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (7 : ZMod 53059462610881679)^2792603295309562 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 239 := Nat.prime_eq_prime_of_dvd_pow hq prime_239 hd
            subst q
            change (7 : ZMod 53059462610881679)^222006119710802 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1381 := Nat.prime_eq_prime_of_dvd_pow hq prime_1381 hd
              subst q
              change (7 : ZMod 53059462610881679)^38421044613238 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 604351537 := Nat.prime_eq_prime_of_dvd_pow hq prime_604351537 hd
              subst q
              change (7 : ZMod 53059462610881679)^87795694 ≠ 1
              reduce_mod_char
              decide

theorem prime_53580927470095939 : Nat.Prime 53580927470095939 := by
  apply lucas_primality 53580927470095939 (2 : ZMod 53580927470095939)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 53580927470095939 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((811832234395393 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 53580927470095939)^26790463735047969 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 53580927470095939)^17860309156698646 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 53580927470095939)^4870993406372358 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 811832234395393 := Nat.prime_eq_prime_of_dvd_pow hq prime_811832234395393 hd
          subst q
          change (2 : ZMod 53580927470095939)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_54106656120140653 : Nat.Prime 54106656120140653 := by
  apply lucas_primality 54106656120140653 (11 : ZMod 54106656120140653)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 54106656120140653 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((43 : ℕ)^1 * ((733 : ℕ)^1 * ((17923 : ℕ)^1 * ((126691 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 54106656120140653)^27053328060070326 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 54106656120140653)^18035552040046884 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (11 : ZMod 54106656120140653)^7729522302877236 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (11 : ZMod 54106656120140653)^1258294328375364 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 733 := Nat.prime_eq_prime_of_dvd_pow hq prime_733 hd
              subst q
              change (11 : ZMod 54106656120140653)^73815356234844 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 17923 := Nat.prime_eq_prime_of_dvd_pow hq prime_17923 hd
                subst q
                change (11 : ZMod 54106656120140653)^3018839263524 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 126691 := Nat.prime_eq_prime_of_dvd_pow hq prime_126691 hd
                subst q
                change (11 : ZMod 54106656120140653)^427075767972 ≠ 1
                reduce_mod_char
                decide

theorem prime_54636676406050901 : Nat.Prime 54636676406050901 := by
  apply lucas_primality 54636676406050901 (3 : ZMod 54636676406050901)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 54636676406050901 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((7 : ℕ)^1 * ((23 : ℕ)^1 * ((173 : ℕ)^1 * ((347 : ℕ)^1 * ((2861 : ℕ)^1 * ((19759 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 54636676406050901)^27318338203025450 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 54636676406050901)^10927335281210180 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 54636676406050901)^7805239486578700 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (3 : ZMod 54636676406050901)^2375507669828300 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
              subst q
              change (3 : ZMod 54636676406050901)^315818938763300 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 347 := Nat.prime_eq_prime_of_dvd_pow hq prime_347 hd
                subst q
                change (3 : ZMod 54636676406050901)^157454398864700 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 2861 := Nat.prime_eq_prime_of_dvd_pow hq prime_2861 hd
                  subst q
                  change (3 : ZMod 54636676406050901)^19097055716900 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 19759 := Nat.prime_eq_prime_of_dvd_pow hq prime_19759 hd
                  subst q
                  change (3 : ZMod 54636676406050901)^2765153925100 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_55171016309022791 : Nat.Prime 55171016309022791 := by
  apply lucas_primality 55171016309022791 (11 : ZMod 55171016309022791)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 55171016309022791 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((23 : ℕ)^1 * ((659 : ℕ)^1 * ((3797 : ℕ)^1 * ((8714941 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 55171016309022791)^27585508154511395 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 55171016309022791)^11034203261804558 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (11 : ZMod 55171016309022791)^5015546937183890 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (11 : ZMod 55171016309022791)^2398739839522730 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 659 := Nat.prime_eq_prime_of_dvd_pow hq prime_659 hd
              subst q
              change (11 : ZMod 55171016309022791)^83719296371810 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 3797 := Nat.prime_eq_prime_of_dvd_pow hq prime_3797 hd
                subst q
                change (11 : ZMod 55171016309022791)^14530159681070 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 8714941 := Nat.prime_eq_prime_of_dvd_pow hq prime_8714941 hd
                subst q
                change (11 : ZMod 55171016309022791)^6330624190 ≠ 1
                reduce_mod_char
                decide

theorem prime_55672884370302547 : Nat.Prime 55672884370302547 := by
  apply lucas_primality 55672884370302547 (5 : ZMod 55672884370302547)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 55672884370302547 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((269 : ℕ)^1 * ((1047751 : ℕ)^1 * ((32921689 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 55672884370302547)^27836442185151273 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 55672884370302547)^18557628123434182 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
          subst q
          change (5 : ZMod 55672884370302547)^206962395428634 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1047751 := Nat.prime_eq_prime_of_dvd_pow hq prime_1047751 hd
            subst q
            change (5 : ZMod 55672884370302547)^53135606046 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 32921689 := Nat.prime_eq_prime_of_dvd_pow hq prime_32921689 hd
            subst q
            change (5 : ZMod 55672884370302547)^1691070114 ≠ 1
            reduce_mod_char
            decide

theorem prime_55709703946857029 : Nat.Prime 55709703946857029 := by
  apply lucas_primality 55709703946857029 (2 : ZMod 55709703946857029)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 55709703946857029 - 1 = (2 : ℕ)^2 * ((8513 : ℕ)^1 * ((62213 : ℕ)^1 * ((26297053 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 55709703946857029)^27854851973428514 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 8513 := Nat.prime_eq_prime_of_dvd_pow hq prime_8513 hd
        subst q
        change (2 : ZMod 55709703946857029)^6544074233156 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 62213 := Nat.prime_eq_prime_of_dvd_pow hq prime_62213 hd
          subst q
          change (2 : ZMod 55709703946857029)^895467248756 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 26297053 := Nat.prime_eq_prime_of_dvd_pow hq prime_26297053 hd
          subst q
          change (2 : ZMod 55709703946857029)^2118477076 ≠ 1
          reduce_mod_char
          decide

theorem prime_56252767574402291 : Nat.Prime 56252767574402291 := by
  apply lucas_primality 56252767574402291 (2 : ZMod 56252767574402291)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 56252767574402291 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((53 : ℕ)^1 * ((106137297310193 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 56252767574402291)^28126383787201145 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 56252767574402291)^11250553514880458 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (2 : ZMod 56252767574402291)^1061372973101930 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 106137297310193 := Nat.prime_eq_prime_of_dvd_pow hq prime_106137297310193 hd
          subst q
          change (2 : ZMod 56252767574402291)^530 ≠ 1
          reduce_mod_char
          decide

theorem prime_56800235584000141 : Nat.Prime 56800235584000141 := by
  apply lucas_primality 56800235584000141 (6 : ZMod 56800235584000141)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 56800235584000141 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7237 : ℕ)^1 * ((130809809737 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 56800235584000141)^28400117792000070 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 56800235584000141)^18933411861333380 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 56800235584000141)^11360047116800028 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7237 := Nat.prime_eq_prime_of_dvd_pow hq prime_7237 hd
            subst q
            change (6 : ZMod 56800235584000141)^7848588584220 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 130809809737 := Nat.prime_eq_prime_of_dvd_pow hq prime_130809809737 hd
            subst q
            change (6 : ZMod 56800235584000141)^434220 ≠ 1
            reduce_mod_char
            decide

theorem prime_57352136505929773 : Nat.Prime 57352136505929773 := by
  apply lucas_primality 57352136505929773 (2 : ZMod 57352136505929773)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 57352136505929773 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((13669 : ℕ)^1 * ((285827 : ℕ)^1 * ((94099 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 57352136505929773)^28676068252964886 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 57352136505929773)^19117378835309924 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 57352136505929773)^4411702808148444 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13669 := Nat.prime_eq_prime_of_dvd_pow hq prime_13669 hd
            subst q
            change (2 : ZMod 57352136505929773)^4195781440188 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 285827 := Nat.prime_eq_prime_of_dvd_pow hq prime_285827 hd
              subst q
              change (2 : ZMod 57352136505929773)^200653320036 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 94099 := Nat.prime_eq_prime_of_dvd_pow hq prime_94099 hd
              subst q
              change (2 : ZMod 57352136505929773)^609487205028 ≠ 1
              reduce_mod_char
              decide

theorem prime_57908499008855153 : Nat.Prime 57908499008855153 := by
  apply lucas_primality 57908499008855153 (3 : ZMod 57908499008855153)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 57908499008855153 - 1 = (2 : ℕ)^4 * ((7 : ℕ)^1 * ((37 : ℕ)^1 * ((379 : ℕ)^1 * ((36870867127 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 57908499008855153)^28954249504427576 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 57908499008855153)^8272642715550736 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (3 : ZMod 57908499008855153)^1565094567806896 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 379 := Nat.prime_eq_prime_of_dvd_pow hq prime_379 hd
            subst q
            change (3 : ZMod 57908499008855153)^152792873374288 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 36870867127 := Nat.prime_eq_prime_of_dvd_pow hq prime_36870867127 hd
            subst q
            change (3 : ZMod 57908499008855153)^1570576 ≠ 1
            reduce_mod_char
            decide

theorem prime_58469351900270719 : Nat.Prime 58469351900270719 := by
  apply lucas_primality 58469351900270719 (6 : ZMod 58469351900270719)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 58469351900270719 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^2 * ((3413 : ℕ)^1 * ((71359 : ℕ)^1 * ((330679 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 58469351900270719)^29234675950135359 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 58469351900270719)^19489783966756906 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (6 : ZMod 58469351900270719)^5315395627297338 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3413 := Nat.prime_eq_prime_of_dvd_pow hq prime_3413 hd
            subst q
            change (6 : ZMod 58469351900270719)^17131365924486 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 71359 := Nat.prime_eq_prime_of_dvd_pow hq prime_71359 hd
              subst q
              change (6 : ZMod 58469351900270719)^819368992002 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 330679 := Nat.prime_eq_prime_of_dvd_pow hq prime_330679 hd
              subst q
              change (6 : ZMod 58469351900270719)^176816041842 ≠ 1
              reduce_mod_char
              decide

theorem prime_59034724126949387 : Nat.Prime 59034724126949387 := by
  apply lucas_primality 59034724126949387 (2 : ZMod 59034724126949387)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 59034724126949387 - 1 = (2 : ℕ)^1 * ((24001 : ℕ)^1 * ((1229838842693 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 59034724126949387)^29517362063474693 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 24001 := Nat.prime_eq_prime_of_dvd_pow hq prime_24001 hd
        subst q
        change (2 : ZMod 59034724126949387)^2459677685386 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1229838842693 := Nat.prime_eq_prime_of_dvd_pow hq prime_1229838842693 hd
        subst q
        change (2 : ZMod 59034724126949387)^48002 ≠ 1
        reduce_mod_char
        decide

theorem prime_59604644775390683 : Nat.Prime 59604644775390683 := by
  apply lucas_primality 59604644775390683 (2 : ZMod 59604644775390683)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 59604644775390683 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((2709302035245031 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 59604644775390683)^29802322387695341 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 59604644775390683)^5418604070490062 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2709302035245031 := Nat.prime_eq_prime_of_dvd_pow hq prime_2709302035245031 hd
        subst q
        change (2 : ZMod 59604644775390683)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_60179143072269563 : Nat.Prime 60179143072269563 := by
  apply lucas_primality 60179143072269563 (2 : ZMod 60179143072269563)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 60179143072269563 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((2735415594194071 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 60179143072269563)^30089571536134781 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 60179143072269563)^5470831188388142 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2735415594194071 := Nat.prime_eq_prime_of_dvd_pow hq prime_2735415594194071 hd
        subst q
        change (2 : ZMod 60179143072269563)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_60758248384885703 : Nat.Prime 60758248384885703 := by
  apply lucas_primality 60758248384885703 (7 : ZMod 60758248384885703)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 60758248384885703 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((54690529 : ℕ)^1 * ((79353317 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 60758248384885703)^30379124192442851 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 60758248384885703)^8679749769269386 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 54690529 := Nat.prime_eq_prime_of_dvd_pow hq prime_54690529 hd
          subst q
          change (7 : ZMod 60758248384885703)^1110946438 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 79353317 := Nat.prime_eq_prime_of_dvd_pow hq prime_79353317 hd
          subst q
          change (7 : ZMod 60758248384885703)^765667406 ≠ 1
          reduce_mod_char
          decide

theorem prime_61032025196406163 : Nat.Prime 61032025196406163 := by
  apply lucas_primality 61032025196406163 (3 : ZMod 61032025196406163)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 61032025196406163 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((1865329 : ℕ)^1 * ((1817731921 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 61032025196406163)^30516012598203081 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 61032025196406163)^20344008398802054 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1865329 := Nat.prime_eq_prime_of_dvd_pow hq prime_1865329 hd
          subst q
          change (3 : ZMod 61032025196406163)^32719174578 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1817731921 := Nat.prime_eq_prime_of_dvd_pow hq prime_1817731921 hd
          subst q
          change (3 : ZMod 61032025196406163)^33575922 ≠ 1
          reduce_mod_char
          decide

theorem prime_61341990221615183 : Nat.Prime 61341990221615183 := by
  apply lucas_primality 61341990221615183 (5 : ZMod 61341990221615183)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 61341990221615183 - 1 = (2 : ℕ)^1 * ((143573 : ℕ)^1 * ((213626483467 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 61341990221615183)^30670995110807591 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 143573 := Nat.prime_eq_prime_of_dvd_pow hq prime_143573 hd
        subst q
        change (5 : ZMod 61341990221615183)^427252966934 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 213626483467 := Nat.prime_eq_prime_of_dvd_pow hq prime_213626483467 hd
        subst q
        change (5 : ZMod 61341990221615183)^287146 ≠ 1
        reduce_mod_char
        decide

theorem prime_61930398232359739 : Nat.Prime 61930398232359739 := by
  apply lucas_primality 61930398232359739 (2 : ZMod 61930398232359739)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 61930398232359739 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((17 : ℕ)^1 * ((202386922327973 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 61930398232359739)^30965199116179869 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 61930398232359739)^20643466077453246 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 61930398232359739)^3642964601903514 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 202386922327973 := Nat.prime_eq_prime_of_dvd_pow hq prime_202386922327973 hd
          subst q
          change (2 : ZMod 61930398232359739)^306 ≠ 1
          reduce_mod_char
          decide

theorem prime_62523502209000013 : Nat.Prime 62523502209000013 := by
  apply lucas_primality 62523502209000013 (2 : ZMod 62523502209000013)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 62523502209000013 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((274225886881579 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 62523502209000013)^31261751104500006 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 62523502209000013)^20841167403000004 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 62523502209000013)^3290710642578948 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 274225886881579 := Nat.prime_eq_prime_of_dvd_pow hq prime_274225886881579 hd
          subst q
          change (2 : ZMod 62523502209000013)^228 ≠ 1
          reduce_mod_char
          decide

theorem prime_63121332085847309 : Nat.Prime 63121332085847309 := by
  apply lucas_primality 63121332085847309 (2 : ZMod 63121332085847309)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 63121332085847309 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((13 : ℕ)^2 * ((19 : ℕ)^1 * ((31 : ℕ)^1 * ((67 : ℕ)^1 * ((223 : ℕ)^1 * ((853 : ℕ)^1 * ((1777 : ℕ)^1)))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 63121332085847309)^31560666042923654 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 63121332085847309)^9017333155121044 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 63121332085847309)^4855487083526716 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (2 : ZMod 63121332085847309)^3322175372939332 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
              subst q
              change (2 : ZMod 63121332085847309)^2036172002769268 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
                subst q
                change (2 : ZMod 63121332085847309)^942109434117124 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 223 := Nat.prime_eq_prime_of_dvd_pow hq prime_223 hd
                  subst q
                  change (2 : ZMod 63121332085847309)^283055300833396 ≠ 1
                  reduce_mod_char
                  decide
                · rcases hq.dvd_mul.mp hd with hd | hd
                  · have heq : q = 853 := Nat.prime_eq_prime_of_dvd_pow hq prime_853 hd
                    subst q
                    change (2 : ZMod 63121332085847309)^73999216982236 ≠ 1
                    reduce_mod_char
                    decide
                  · have heq : q = 1777 := Nat.prime_eq_prime_of_dvd_pow hq prime_1777 hd
                    subst q
                    change (2 : ZMod 63121332085847309)^35521289862604 ≠ 1
                    reduce_mod_char
                    decide

theorem prime_63723917940097189 : Nat.Prime 63723917940097189 := by
  apply lucas_primality 63723917940097189 (7 : ZMod 63723917940097189)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 63723917940097189 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((27673 : ℕ)^1 * ((10099767577 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 63723917940097189)^31861958970048594 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 63723917940097189)^21241305980032396 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (7 : ZMod 63723917940097189)^3353890417899852 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 27673 := Nat.prime_eq_prime_of_dvd_pow hq prime_27673 hd
            subst q
            change (7 : ZMod 63723917940097189)^2302747007556 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 10099767577 := Nat.prime_eq_prime_of_dvd_pow hq prime_10099767577 hd
            subst q
            change (7 : ZMod 63723917940097189)^6309444 ≠ 1
            reduce_mod_char
            decide

theorem prime_64331289992282801 : Nat.Prime 64331289992282801 := by
  apply lucas_primality 64331289992282801 (3 : ZMod 64331289992282801)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 64331289992282801 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^2 * ((2673211 : ℕ)^1 * ((60162937 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 64331289992282801)^32165644996141400 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 64331289992282801)^12866257998456560 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2673211 := Nat.prime_eq_prime_of_dvd_pow hq prime_2673211 hd
          subst q
          change (3 : ZMod 64331289992282801)^24065174800 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 60162937 := Nat.prime_eq_prime_of_dvd_pow hq prime_60162937 hd
          subst q
          change (3 : ZMod 64331289992282801)^1069284400 ≠ 1
          reduce_mod_char
          decide

theorem prime_64943478606730847 : Nat.Prime 64943478606730847 := by
  apply lucas_primality 64943478606730847 (5 : ZMod 64943478606730847)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 64943478606730847 - 1 = (2 : ℕ)^1 * ((32471739303365423 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 64943478606730847)^32471739303365423 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 32471739303365423 := Nat.prime_eq_prime_of_dvd_pow hq prime_32471739303365423 hd
      subst q
      change (5 : ZMod 64943478606730847)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_65560514292015709 : Nat.Prime 65560514292015709 := by
  apply lucas_primality 65560514292015709 (2 : ZMod 65560514292015709)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 65560514292015709 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((29 : ℕ)^1 * ((86689 : ℕ)^1 * ((44350961 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 65560514292015709)^32780257146007854 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 65560514292015709)^21853504764005236 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 65560514292015709)^9365787756002244 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (2 : ZMod 65560514292015709)^2260707389379852 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 86689 := Nat.prime_eq_prime_of_dvd_pow hq prime_86689 hd
              subst q
              change (2 : ZMod 65560514292015709)^756272586972 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 44350961 := Nat.prime_eq_prime_of_dvd_pow hq prime_44350961 hd
              subst q
              change (2 : ZMod 65560514292015709)^1478220828 ≠ 1
              reduce_mod_char
              decide

theorem prime_66182427701415983 : Nat.Prime 66182427701415983 := by
  apply lucas_primality 66182427701415983 (5 : ZMod 66182427701415983)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 66182427701415983 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((19 : ℕ)^2 * ((31 : ℕ)^2 * ((73 : ℕ)^1 * ((157 : ℕ)^1 * ((756601 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 66182427701415983)^33091213850707991 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 66182427701415983)^6016584336492362 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (5 : ZMod 66182427701415983)^3483285668495578 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (5 : ZMod 66182427701415983)^2134917022626322 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
              subst q
              change (5 : ZMod 66182427701415983)^906608598649534 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
                subst q
                change (5 : ZMod 66182427701415983)^421544125486726 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 756601 := Nat.prime_eq_prime_of_dvd_pow hq prime_756601 hd
                subst q
                change (5 : ZMod 66182427701415983)^87473354782 ≠ 1
                reduce_mod_char
                decide

theorem prime_66809249633371621 : Nat.Prime 66809249633371621 := by
  apply lucas_primality 66809249633371621 (2 : ZMod 66809249633371621)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 66809249633371621 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((599 : ℕ)^1 * ((175783 : ℕ)^1 * ((10575031 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 66809249633371621)^33404624816685810 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 66809249633371621)^22269749877790540 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 66809249633371621)^13361849926674324 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 599 := Nat.prime_eq_prime_of_dvd_pow hq prime_599 hd
            subst q
            change (2 : ZMod 66809249633371621)^111534640456380 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 175783 := Nat.prime_eq_prime_of_dvd_pow hq prime_175783 hd
              subst q
              change (2 : ZMod 66809249633371621)^380066614140 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 10575031 := Nat.prime_eq_prime_of_dvd_pow hq prime_10575031 hd
              subst q
              change (2 : ZMod 66809249633371621)^6317641020 ≠ 1
              reduce_mod_char
              decide

theorem prime_67441011031941223 : Nat.Prime 67441011031941223 := by
  apply lucas_primality 67441011031941223 (5 : ZMod 67441011031941223)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 67441011031941223 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((864628346563349 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 67441011031941223)^33720505515970611 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 67441011031941223)^22480337010647074 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (5 : ZMod 67441011031941223)^5187770079380094 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 864628346563349 := Nat.prime_eq_prime_of_dvd_pow hq prime_864628346563349 hd
          subst q
          change (5 : ZMod 67441011031941223)^78 ≠ 1
          reduce_mod_char
          decide

theorem prime_68077742987260187 : Nat.Prime 68077742987260187 := by
  apply lucas_primality 68077742987260187 (2 : ZMod 68077742987260187)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 68077742987260187 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((694609 : ℕ)^1 * ((2882609581 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 68077742987260187)^34038871493630093 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 68077742987260187)^4004573116897658 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 694609 := Nat.prime_eq_prime_of_dvd_pow hq prime_694609 hd
          subst q
          change (2 : ZMod 68077742987260187)^98008725754 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2882609581 := Nat.prime_eq_prime_of_dvd_pow hq prime_2882609581 hd
          subst q
          change (2 : ZMod 68077742987260187)^23616706 ≠ 1
          reduce_mod_char
          decide

theorem prime_68719476736000039 : Nat.Prime 68719476736000039 := by
  apply lucas_primality 68719476736000039 (3 : ZMod 68719476736000039)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 68719476736000039 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((53 : ℕ)^1 * ((359 : ℕ)^1 * ((46303617623 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 68719476736000039)^34359738368000019 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 68719476736000039)^22906492245333346 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 68719476736000039)^5286113595076926 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
            subst q
            change (3 : ZMod 68719476736000039)^1296593900679246 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 359 := Nat.prime_eq_prime_of_dvd_pow hq prime_359 hd
              subst q
              change (3 : ZMod 68719476736000039)^191419155253482 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 46303617623 := Nat.prime_eq_prime_of_dvd_pow hq prime_46303617623 hd
              subst q
              change (3 : ZMod 68719476736000039)^1484106 ≠ 1
              reduce_mod_char
              decide

theorem prime_69366243661827859 : Nat.Prime 69366243661827859 := by
  apply lucas_primality 69366243661827859 (2 : ZMod 69366243661827859)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 69366243661827859 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((918149 : ℕ)^1 * ((1399075823 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 69366243661827859)^34683121830913929 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 69366243661827859)^23122081220609286 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 918149 := Nat.prime_eq_prime_of_dvd_pow hq prime_918149 hd
          subst q
          change (2 : ZMod 69366243661827859)^75550094442 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1399075823 := Nat.prime_eq_prime_of_dvd_pow hq prime_1399075823 hd
          subst q
          change (2 : ZMod 69366243661827859)^49580046 ≠ 1
          reduce_mod_char
          decide

theorem prime_70018075295866963 : Nat.Prime 70018075295866963 := by
  apply lucas_primality 70018075295866963 (2 : ZMod 70018075295866963)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 70018075295866963 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((62401 : ℕ)^1 * ((333353107 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 70018075295866963)^35009037647933481 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 70018075295866963)^23339358431955654 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 70018075295866963)^6365279572351542 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (2 : ZMod 70018075295866963)^4118710311521586 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 62401 := Nat.prime_eq_prime_of_dvd_pow hq prime_62401 hd
              subst q
              change (2 : ZMod 70018075295866963)^1122066558162 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 333353107 := Nat.prime_eq_prime_of_dvd_pow hq prime_333353107 hd
              subst q
              change (2 : ZMod 70018075295866963)^210041766 ≠ 1
              reduce_mod_char
              decide

theorem prime_70675003317157859 : Nat.Prime 70675003317157859 := by
  apply lucas_primality 70675003317157859 (2 : ZMod 70675003317157859)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 70675003317157859 - 1 = (2 : ℕ)^1 * ((193 : ℕ)^1 * ((1093 : ℕ)^1 * ((208121 : ℕ)^1 * ((804901 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 70675003317157859)^35337501658578929 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
        subst q
        change (2 : ZMod 70675003317157859)^366191727031906 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1093 := Nat.prime_eq_prime_of_dvd_pow hq prime_1093 hd
          subst q
          change (2 : ZMod 70675003317157859)^64661485194106 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 208121 := Nat.prime_eq_prime_of_dvd_pow hq prime_208121 hd
            subst q
            change (2 : ZMod 70675003317157859)^339586122098 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 804901 := Nat.prime_eq_prime_of_dvd_pow hq prime_804901 hd
            subst q
            change (2 : ZMod 70675003317157859)^87805833658 ≠ 1
            reduce_mod_char
            decide

theorem prime_71337059553120281 : Nat.Prime 71337059553120281 := by
  apply lucas_primality 71337059553120281 (3 : ZMod 71337059553120281)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 71337059553120281 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((73 : ℕ)^1 * ((24430499846959 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 71337059553120281)^35668529776560140 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 71337059553120281)^14267411910624056 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
          subst q
          change (3 : ZMod 71337059553120281)^977219993878360 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 24430499846959 := Nat.prime_eq_prime_of_dvd_pow hq prime_24430499846959 hd
          subst q
          change (3 : ZMod 71337059553120281)^2920 ≠ 1
          reduce_mod_char
          decide

theorem prime_72004275980015657 : Nat.Prime 72004275980015657 := by
  apply lucas_primality 72004275980015657 (3 : ZMod 72004275980015657)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 72004275980015657 - 1 = (2 : ℕ)^3 * ((1493 : ℕ)^1 * ((482773 : ℕ)^1 * ((12487213 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 72004275980015657)^36002137990007828 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1493 := Nat.prime_eq_prime_of_dvd_pow hq prime_1493 hd
        subst q
        change (3 : ZMod 72004275980015657)^48227914253192 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 482773 := Nat.prime_eq_prime_of_dvd_pow hq prime_482773 hd
          subst q
          change (3 : ZMod 72004275980015657)^149147272072 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 12487213 := Nat.prime_eq_prime_of_dvd_pow hq prime_12487213 hd
          subst q
          change (3 : ZMod 72004275980015657)^5766240712 ≠ 1
          reduce_mod_char
          decide

theorem prime_72191037313158319 : Nat.Prime 72191037313158319 := by
  apply lucas_primality 72191037313158319 (3 : ZMod 72191037313158319)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 72191037313158319 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((4010613184064351 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 72191037313158319)^36095518656579159 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 72191037313158319)^24063679104386106 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4010613184064351 := Nat.prime_eq_prime_of_dvd_pow hq prime_4010613184064351 hd
        subst q
        change (3 : ZMod 72191037313158319)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_72676684723410511 : Nat.Prime 72676684723410511 := by
  apply lucas_primality 72676684723410511 (6 : ZMod 72676684723410511)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 72676684723410511 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((83 : ℕ)^1 * ((29187423583699 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 72676684723410511)^36338342361705255 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 72676684723410511)^24225561574470170 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 72676684723410511)^14535336944682102 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
            subst q
            change (6 : ZMod 72676684723410511)^875622707510970 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 29187423583699 := Nat.prime_eq_prime_of_dvd_pow hq prime_29187423583699 hd
            subst q
            change (6 : ZMod 72676684723410511)^2490 ≠ 1
            reduce_mod_char
            decide

theorem prime_73354318058640767 : Nat.Prime 73354318058640767 := by
  apply lucas_primality 73354318058640767 (5 : ZMod 73354318058640767)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 73354318058640767 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^2 * ((17 : ℕ)^1 * ((23 : ℕ)^1 * ((43 : ℕ)^1 * ((103 : ℕ)^1 * ((432232253 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 73354318058640767)^36677159029320383 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 73354318058640767)^10479188294091538 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (5 : ZMod 73354318058640767)^4314959885802398 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (5 : ZMod 73354318058640767)^3189318176462642 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
              subst q
              change (5 : ZMod 73354318058640767)^1705914373456762 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
                subst q
                change (5 : ZMod 73354318058640767)^712177845229522 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 432232253 := Nat.prime_eq_prime_of_dvd_pow hq prime_432232253 hd
                subst q
                change (5 : ZMod 73354318058640767)^169710422 ≠ 1
                reduce_mod_char
                decide

theorem prime_74037208411275287 : Nat.Prime 74037208411275287 := by
  apply lucas_primality 74037208411275287 (5 : ZMod 74037208411275287)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 74037208411275287 - 1 = (2 : ℕ)^1 * ((37018604205637643 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 74037208411275287)^37018604205637643 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 37018604205637643 := Nat.prime_eq_prime_of_dvd_pow hq prime_37018604205637643 hd
      subst q
      change (5 : ZMod 74037208411275287)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_74725388357583617 : Nat.Prime 74725388357583617 := by
  apply lucas_primality 74725388357583617 (3 : ZMod 74725388357583617)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 74725388357583617 - 1 = (2 : ℕ)^8 * ((23 : ℕ)^1 * ((1613 : ℕ)^1 * ((7868030089 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 74725388357583617)^37362694178791808 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (3 : ZMod 74725388357583617)^3248929928590592 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1613 := Nat.prime_eq_prime_of_dvd_pow hq prime_1613 hd
          subst q
          change (3 : ZMod 74725388357583617)^46326961164032 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7868030089 := Nat.prime_eq_prime_of_dvd_pow hq prime_7868030089 hd
          subst q
          change (3 : ZMod 74725388357583617)^9497344 ≠ 1
          reduce_mod_char
          decide

theorem prime_75418890625000033 : Nat.Prime 75418890625000033 := by
  apply lucas_primality 75418890625000033 (5 : ZMod 75418890625000033)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 75418890625000033 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((71419404000947 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 75418890625000033)^37709445312500016 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 75418890625000033)^25139630208333344 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 75418890625000033)^6856262784090912 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 71419404000947 := Nat.prime_eq_prime_of_dvd_pow hq prime_71419404000947 hd
          subst q
          change (5 : ZMod 75418890625000033)^1056 ≠ 1
          reduce_mod_char
          decide

theorem prime_76117748092591493 : Nat.Prime 76117748092591493 := by
  apply lucas_primality 76117748092591493 (3 : ZMod 76117748092591493)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 76117748092591493 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((16476223 : ℕ)^1 * ((164994793 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 76117748092591493)^38058874046295746 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 76117748092591493)^10873964013227356 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 16476223 := Nat.prime_eq_prime_of_dvd_pow hq prime_16476223 hd
          subst q
          change (3 : ZMod 76117748092591493)^4619854204 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 164994793 := Nat.prime_eq_prime_of_dvd_pow hq prime_164994793 hd
          subst q
          change (3 : ZMod 76117748092591493)^461334244 ≠ 1
          reduce_mod_char
          decide

theorem prime_76351196109027857 : Nat.Prime 76351196109027857 := by
  apply lucas_primality 76351196109027857 (3 : ZMod 76351196109027857)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 76351196109027857 - 1 = (2 : ℕ)^4 * ((83 : ℕ)^1 * ((1459 : ℕ)^1 * ((39406011353 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 76351196109027857)^38175598054513928 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
        subst q
        change (3 : ZMod 76351196109027857)^919893929024432 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1459 := Nat.prime_eq_prime_of_dvd_pow hq prime_1459 hd
          subst q
          change (3 : ZMod 76351196109027857)^52331183076784 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 39406011353 := Nat.prime_eq_prime_of_dvd_pow hq prime_39406011353 hd
          subst q
          change (3 : ZMod 76351196109027857)^1937552 ≠ 1
          reduce_mod_char
          decide

theorem prime_76821993791524901 : Nat.Prime 76821993791524901 := by
  apply lucas_primality 76821993791524901 (3 : ZMod 76821993791524901)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 76821993791524901 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((409 : ℕ)^1 * ((1878288356761 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 76821993791524901)^38410996895762450 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 76821993791524901)^15364398758304980 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 409 := Nat.prime_eq_prime_of_dvd_pow hq prime_409 hd
          subst q
          change (3 : ZMod 76821993791524901)^187828835676100 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1878288356761 := Nat.prime_eq_prime_of_dvd_pow hq prime_1878288356761 hd
          subst q
          change (3 : ZMod 76821993791524901)^40900 ≠ 1
          reduce_mod_char
          decide

theorem prime_76919506757978141 : Nat.Prime 76919506757978141 := by
  apply lucas_primality 76919506757978141 (2 : ZMod 76919506757978141)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 76919506757978141 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((5023 : ℕ)^1 * ((275447 : ℕ)^1 * ((2779747 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 76919506757978141)^38459753378989070 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 76919506757978141)^15383901351595628 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5023 := Nat.prime_eq_prime_of_dvd_pow hq prime_5023 hd
          subst q
          change (2 : ZMod 76919506757978141)^15313459438180 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 275447 := Nat.prime_eq_prime_of_dvd_pow hq prime_275447 hd
            subst q
            change (2 : ZMod 76919506757978141)^279253383620 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2779747 := Nat.prime_eq_prime_of_dvd_pow hq prime_2779747 hd
            subst q
            change (2 : ZMod 76919506757978141)^27671405620 ≠ 1
            reduce_mod_char
            decide

theorem prime_77531660905535983 : Nat.Prime 77531660905535983 := by
  apply lucas_primality 77531660905535983 (5 : ZMod 77531660905535983)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 77531660905535983 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((29 : ℕ)^1 * ((151 : ℕ)^1 * ((983629708781 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 77531660905535983)^38765830452767991 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 77531660905535983)^25843886968511994 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (5 : ZMod 77531660905535983)^2673505548466758 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
            subst q
            change (5 : ZMod 77531660905535983)^513454707983682 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 983629708781 := Nat.prime_eq_prime_of_dvd_pow hq prime_983629708781 hd
            subst q
            change (5 : ZMod 77531660905535983)^78822 ≠ 1
            reduce_mod_char
            decide

theorem prime_77793236523459077 : Nat.Prime 77793236523459077 := by
  apply lucas_primality 77793236523459077 (2 : ZMod 77793236523459077)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 77793236523459077 - 1 = (2 : ℕ)^2 * ((104107 : ℕ)^1 * ((186810772867 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 77793236523459077)^38896618261729538 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 104107 := Nat.prime_eq_prime_of_dvd_pow hq prime_104107 hd
        subst q
        change (2 : ZMod 77793236523459077)^747243091468 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 186810772867 := Nat.prime_eq_prime_of_dvd_pow hq prime_186810772867 hd
        subst q
        change (2 : ZMod 77793236523459077)^416428 ≠ 1
        reduce_mod_char
        decide

theorem prime_78246782771397701 : Nat.Prime 78246782771397701 := by
  apply lucas_primality 78246782771397701 (3 : ZMod 78246782771397701)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 78246782771397701 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((929 : ℕ)^1 * ((842268921113 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 78246782771397701)^39123391385698850 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 78246782771397701)^15649356554279540 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 929 := Nat.prime_eq_prime_of_dvd_pow hq prime_929 hd
          subst q
          change (3 : ZMod 78246782771397701)^84226892111300 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 842268921113 := Nat.prime_eq_prime_of_dvd_pow hq prime_842268921113 hd
          subst q
          change (3 : ZMod 78246782771397701)^92900 ≠ 1
          reduce_mod_char
          decide

theorem prime_78967392879390629 : Nat.Prime 78967392879390629 := by
  apply lucas_primality 78967392879390629 (2 : ZMod 78967392879390629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 78967392879390629 - 1 = (2 : ℕ)^2 * ((3499 : ℕ)^1 * ((5642140102843 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 78967392879390629)^39483696439695314 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3499 := Nat.prime_eq_prime_of_dvd_pow hq prime_3499 hd
        subst q
        change (2 : ZMod 78967392879390629)^22568560411372 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5642140102843 := Nat.prime_eq_prime_of_dvd_pow hq prime_5642140102843 hd
        subst q
        change (2 : ZMod 78967392879390629)^13996 ≠ 1
        reduce_mod_char
        decide

theorem prime_79693524873773077 : Nat.Prime 79693524873773077 := by
  apply lucas_primality 79693524873773077 (2 : ZMod 79693524873773077)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 79693524873773077 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((29 : ℕ)^1 * ((32714911688741 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 79693524873773077)^39846762436886538 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 79693524873773077)^26564508291257692 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 79693524873773077)^11384789267681868 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (2 : ZMod 79693524873773077)^2748052581854244 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 32714911688741 := Nat.prime_eq_prime_of_dvd_pow hq prime_32714911688741 hd
            subst q
            change (2 : ZMod 79693524873773077)^2436 ≠ 1
            reduce_mod_char
            decide

theorem prime_80425212553252451 : Nat.Prime 80425212553252451 := by
  apply lucas_primality 80425212553252451 (2 : ZMod 80425212553252451)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 80425212553252451 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((13 : ℕ)^3 * ((89 : ℕ)^1 * ((97 : ℕ)^1 * ((673 : ℕ)^1 * ((126013 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 80425212553252451)^40212606276626225 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 80425212553252451)^16085042510650490 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 80425212553252451)^6186554811788650 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
            subst q
            change (2 : ZMod 80425212553252451)^903654073632050 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
              subst q
              change (2 : ZMod 80425212553252451)^829125902610850 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 673 := Nat.prime_eq_prime_of_dvd_pow hq prime_673 hd
                subst q
                change (2 : ZMod 80425212553252451)^119502544655650 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 126013 := Nat.prime_eq_prime_of_dvd_pow hq prime_126013 hd
                subst q
                change (2 : ZMod 80425212553252451)^638229488650 ≠ 1
                reduce_mod_char
                decide

theorem prime_81162489871457377 : Nat.Prime 81162489871457377 := by
  apply lucas_primality 81162489871457377 (5 : ZMod 81162489871457377)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 81162489871457377 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((49731917813393 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 81162489871457377)^40581244935728688 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 81162489871457377)^27054163290485792 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (5 : ZMod 81162489871457377)^4774264110085728 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 49731917813393 := Nat.prime_eq_prime_of_dvd_pow hq prime_49731917813393 hd
          subst q
          change (5 : ZMod 81162489871457377)^1632 ≠ 1
          reduce_mod_char
          decide

theorem prime_81905390937410071 : Nat.Prime 81905390937410071 := by
  apply lucas_primality 81905390937410071 (3 : ZMod 81905390937410071)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 81905390937410071 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((990023 : ℕ)^1 * ((2757693203 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 81905390937410071)^40952695468705035 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 81905390937410071)^27301796979136690 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 81905390937410071)^16381078187482014 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 990023 := Nat.prime_eq_prime_of_dvd_pow hq prime_990023 hd
            subst q
            change (3 : ZMod 81905390937410071)^82730796090 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2757693203 := Nat.prime_eq_prime_of_dvd_pow hq prime_2757693203 hd
            subst q
            change (3 : ZMod 81905390937410071)^29700690 ≠ 1
            reduce_mod_char
            decide

theorem prime_82653950016000007 : Nat.Prime 82653950016000007 := by
  apply lucas_primality 82653950016000007 (3 : ZMod 82653950016000007)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 82653950016000007 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((243031 : ℕ)^1 * ((8097531553 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 82653950016000007)^41326975008000003 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 82653950016000007)^27551316672000002 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 82653950016000007)^11807707145142858 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 243031 := Nat.prime_eq_prime_of_dvd_pow hq prime_243031 hd
            subst q
            change (3 : ZMod 82653950016000007)^340096325226 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 8097531553 := Nat.prime_eq_prime_of_dvd_pow hq prime_8097531553 hd
            subst q
            change (3 : ZMod 82653950016000007)^10207302 ≠ 1
            reduce_mod_char
            decide

theorem prime_83408201528457977 : Nat.Prime 83408201528457977 := by
  apply lucas_primality 83408201528457977 (3 : ZMod 83408201528457977)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 83408201528457977 - 1 = (2 : ℕ)^3 * ((17929 : ℕ)^1 * ((581517384743 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 83408201528457977)^41704100764228988 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17929 := Nat.prime_eq_prime_of_dvd_pow hq prime_17929 hd
        subst q
        change (3 : ZMod 83408201528457977)^4652139077944 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 581517384743 := Nat.prime_eq_prime_of_dvd_pow hq prime_581517384743 hd
        subst q
        change (3 : ZMod 83408201528457977)^143432 ≠ 1
        reduce_mod_char
        decide

theorem prime_83443677518903099 : Nat.Prime 83443677518903099 := by
  apply lucas_primality 83443677518903099 (2 : ZMod 83443677518903099)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 83443677518903099 - 1 = (2 : ℕ)^1 * ((7652401 : ℕ)^1 * ((5452123949 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 83443677518903099)^41721838759451549 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7652401 := Nat.prime_eq_prime_of_dvd_pow hq prime_7652401 hd
        subst q
        change (2 : ZMod 83443677518903099)^10904247898 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5452123949 := Nat.prime_eq_prime_of_dvd_pow hq prime_5452123949 hd
        subst q
        change (2 : ZMod 83443677518903099)^15304802 ≠ 1
        reduce_mod_char
        decide

theorem prime_84168180052830787 : Nat.Prime 84168180052830787 := by
  apply lucas_primality 84168180052830787 (2 : ZMod 84168180052830787)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 84168180052830787 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((41 : ℕ)^1 * ((4049 : ℕ)^1 * ((7681965769 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 84168180052830787)^42084090026415393 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 84168180052830787)^28056060017610262 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 84168180052830787)^7651652732075526 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (2 : ZMod 84168180052830787)^2052882440312946 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 4049 := Nat.prime_eq_prime_of_dvd_pow hq prime_4049 hd
              subst q
              change (2 : ZMod 84168180052830787)^20787399370914 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 7681965769 := Nat.prime_eq_prime_of_dvd_pow hq prime_7681965769 hd
              subst q
              change (2 : ZMod 84168180052830787)^10956594 ≠ 1
              reduce_mod_char
              decide

theorem prime_84933920324457013 : Nat.Prime 84933920324457013 := by
  apply lucas_primality 84933920324457013 (6 : ZMod 84933920324457013)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 84933920324457013 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((67 : ℕ)^1 * ((3071317 : ℕ)^1 * ((34395409 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 84933920324457013)^42466960162228506 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 84933920324457013)^28311306774819004 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (6 : ZMod 84933920324457013)^1267670452603836 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3071317 := Nat.prime_eq_prime_of_dvd_pow hq prime_3071317 hd
            subst q
            change (6 : ZMod 84933920324457013)^27653908836 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 34395409 := Nat.prime_eq_prime_of_dvd_pow hq prime_34395409 hd
            subst q
            change (6 : ZMod 84933920324457013)^2469338868 ≠ 1
            reduce_mod_char
            decide

theorem prime_85705457236443181 : Nat.Prime 85705457236443181 := by
  apply lucas_primality 85705457236443181 (6 : ZMod 85705457236443181)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 85705457236443181 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((60611 : ℕ)^1 * ((2618564447 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 85705457236443181)^42852728618221590 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 85705457236443181)^28568485745481060 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 85705457236443181)^17141091447288636 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 60611 := Nat.prime_eq_prime_of_dvd_pow hq prime_60611 hd
            subst q
            change (6 : ZMod 85705457236443181)^1414024801380 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2618564447 := Nat.prime_eq_prime_of_dvd_pow hq prime_2618564447 hd
            subst q
            change (6 : ZMod 85705457236443181)^32729940 ≠ 1
            reduce_mod_char
            decide

theorem prime_86482825840140643 : Nat.Prime 86482825840140643 := by
  apply lucas_primality 86482825840140643 (2 : ZMod 86482825840140643)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 86482825840140643 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((11 : ℕ)^2 * ((353 : ℕ)^1 * ((701 : ℕ)^1 * ((160464613 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 86482825840140643)^43241412920070321 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 86482825840140643)^28827608613380214 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 86482825840140643)^7862075076376422 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 353 := Nat.prime_eq_prime_of_dvd_pow hq prime_353 hd
            subst q
            change (2 : ZMod 86482825840140643)^244993840906914 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 701 := Nat.prime_eq_prime_of_dvd_pow hq prime_701 hd
              subst q
              change (2 : ZMod 86482825840140643)^123370650271242 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 160464613 := Nat.prime_eq_prime_of_dvd_pow hq prime_160464613 hd
              subst q
              change (2 : ZMod 86482825840140643)^538952634 ≠ 1
              reduce_mod_char
              decide

theorem prime_87266061345623681 : Nat.Prime 87266061345623681 := by
  apply lucas_primality 87266061345623681 (7 : ZMod 87266061345623681)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 87266061345623681 - 1 = (2 : ℕ)^7 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((853 : ℕ)^1 * ((937 : ℕ)^1 * ((13123009 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 87266061345623681)^43633030672811840 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 87266061345623681)^17453212269124736 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (7 : ZMod 87266061345623681)^6712773949663360 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 853 := Nat.prime_eq_prime_of_dvd_pow hq prime_853 hd
            subst q
            change (7 : ZMod 87266061345623681)^102304878482560 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 937 := Nat.prime_eq_prime_of_dvd_pow hq prime_937 hd
              subst q
              change (7 : ZMod 87266061345623681)^93133469952640 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 13123009 := Nat.prime_eq_prime_of_dvd_pow hq prime_13123009 hd
              subst q
              change (7 : ZMod 87266061345623681)^6649851520 ≠ 1
              reduce_mod_char
              decide

theorem prime_88055199122167411 : Nat.Prime 88055199122167411 := by
  apply lucas_primality 88055199122167411 (3 : ZMod 88055199122167411)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 88055199122167411 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((1097 : ℕ)^1 * ((382233793993 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 88055199122167411)^44027599561083705 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 88055199122167411)^29351733040722470 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 88055199122167411)^17611039824433482 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (3 : ZMod 88055199122167411)^12579314160309630 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1097 := Nat.prime_eq_prime_of_dvd_pow hq prime_1097 hd
              subst q
              change (3 : ZMod 88055199122167411)^80269096738530 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 382233793993 := Nat.prime_eq_prime_of_dvd_pow hq prime_382233793993 hd
              subst q
              change (3 : ZMod 88055199122167411)^230370 ≠ 1
              reduce_mod_char
              decide

theorem prime_88850274698727449 : Nat.Prime 88850274698727449 := by
  apply lucas_primality 88850274698727449 (3 : ZMod 88850274698727449)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 88850274698727449 - 1 = (2 : ℕ)^3 * ((1249 : ℕ)^1 * ((37379 : ℕ)^1 * ((237891361 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 88850274698727449)^44425137349363724 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1249 := Nat.prime_eq_prime_of_dvd_pow hq prime_1249 hd
        subst q
        change (3 : ZMod 88850274698727449)^71137129462552 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37379 := Nat.prime_eq_prime_of_dvd_pow hq prime_37379 hd
          subst q
          change (3 : ZMod 88850274698727449)^2377010479112 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 237891361 := Nat.prime_eq_prime_of_dvd_pow hq prime_237891361 hd
          subst q
          change (3 : ZMod 88850274698727449)^373490968 ≠ 1
          reduce_mod_char
          decide

theorem prime_89651323764419503 : Nat.Prime 89651323764419503 := by
  apply lucas_primality 89651323764419503 (3 : ZMod 89651323764419503)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 89651323764419503 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((14941887294069917 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 89651323764419503)^44825661882209751 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 89651323764419503)^29883774588139834 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 14941887294069917 := Nat.prime_eq_prime_of_dvd_pow hq prime_14941887294069917 hd
        subst q
        change (3 : ZMod 89651323764419503)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_90200925735953761 : Nat.Prime 90200925735953761 := by
  apply lucas_primality 90200925735953761 (29 : ZMod 90200925735953761)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 90200925735953761 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((17 : ℕ)^1 * ((31 : ℕ)^1 * ((37 : ℕ)^1 * ((3121 : ℕ)^1 * ((11311 : ℕ)^1))))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (29 : ZMod 90200925735953761)^45100462867976880 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (29 : ZMod 90200925735953761)^30066975245317920 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (29 : ZMod 90200925735953761)^18040185147190752 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (29 : ZMod 90200925735953761)^12885846533707680 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
              subst q
              change (29 : ZMod 90200925735953761)^6938532748919520 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
                subst q
                change (29 : ZMod 90200925735953761)^5305936807997280 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
                  subst q
                  change (29 : ZMod 90200925735953761)^2909707281804960 ≠ 1
                  reduce_mod_char
                  decide
                · rcases hq.dvd_mul.mp hd with hd | hd
                  · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
                    subst q
                    change (29 : ZMod 90200925735953761)^2437862857728480 ≠ 1
                    reduce_mod_char
                    decide
                  · rcases hq.dvd_mul.mp hd with hd | hd
                    · have heq : q = 3121 := Nat.prime_eq_prime_of_dvd_pow hq prime_3121 hd
                      subst q
                      change (29 : ZMod 90200925735953761)^28901289886560 ≠ 1
                      reduce_mod_char
                      decide
                    · have heq : q = 11311 := Nat.prime_eq_prime_of_dvd_pow hq prime_11311 hd
                      subst q
                      change (29 : ZMod 90200925735953761)^7974619904160 ≠ 1
                      reduce_mod_char
                      decide

theorem prime_90458382169000033 : Nat.Prime 90458382169000033 := by
  apply lucas_primality 90458382169000033 (5 : ZMod 90458382169000033)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 90458382169000033 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((11 : ℕ)^2 * ((41 : ℕ)^1 * ((107 : ℕ)^1 * ((499 : ℕ)^1 * ((1019 : ℕ)^1 * ((3491 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 90458382169000033)^45229191084500016 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 90458382169000033)^30152794056333344 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 90458382169000033)^8223489288090912 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (5 : ZMod 90458382169000033)^2206302004121952 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
              subst q
              change (5 : ZMod 90458382169000033)^845405440831776 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 499 := Nat.prime_eq_prime_of_dvd_pow hq prime_499 hd
                subst q
                change (5 : ZMod 90458382169000033)^181279322983968 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 1019 := Nat.prime_eq_prime_of_dvd_pow hq prime_1019 hd
                  subst q
                  change (5 : ZMod 90458382169000033)^88771719498528 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 3491 := Nat.prime_eq_prime_of_dvd_pow hq prime_3491 hd
                  subst q
                  change (5 : ZMod 90458382169000033)^25911882603552 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_91271485923347533 : Nat.Prime 91271485923347533 := by
  apply lucas_primality 91271485923347533 (2 : ZMod 91271485923347533)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 91271485923347533 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((229 : ℕ)^1 * ((91193 : ℕ)^1 * ((33110383 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 91271485923347533)^45635742961673766 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 91271485923347533)^30423828641115844 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 91271485923347533)^8297407811213412 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 229 := Nat.prime_eq_prime_of_dvd_pow hq prime_229 hd
            subst q
            change (2 : ZMod 91271485923347533)^398565440713308 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 91193 := Nat.prime_eq_prime_of_dvd_pow hq prime_91193 hd
              subst q
              change (2 : ZMod 91271485923347533)^1000860657324 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 33110383 := Nat.prime_eq_prime_of_dvd_pow hq prime_33110383 hd
              subst q
              change (2 : ZMod 91271485923347533)^2756582004 ≠ 1
              reduce_mod_char
              decide

theorem prime_92090671199944787 : Nat.Prime 92090671199944787 := by
  apply lucas_primality 92090671199944787 (2 : ZMod 92090671199944787)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 92090671199944787 - 1 = (2 : ℕ)^1 * ((703349 : ℕ)^1 * ((65465843557 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 92090671199944787)^46045335599972393 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 703349 := Nat.prime_eq_prime_of_dvd_pow hq prime_703349 hd
        subst q
        change (2 : ZMod 92090671199944787)^130931687114 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 65465843557 := Nat.prime_eq_prime_of_dvd_pow hq prime_65465843557 hd
        subst q
        change (2 : ZMod 92090671199944787)^1406698 ≠ 1
        reduce_mod_char
        decide

theorem prime_92308240023212233 : Nat.Prime 92308240023212233 := by
  apply lucas_primality 92308240023212233 (5 : ZMod 92308240023212233)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 92308240023212233 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((19 : ℕ)^1 * ((47 : ℕ)^1 * ((53 : ℕ)^1 * ((12601 : ℕ)^1 * ((716563 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 92308240023212233)^46154120011606116 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 92308240023212233)^30769413341070744 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (5 : ZMod 92308240023212233)^4858328422274328 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
            subst q
            change (5 : ZMod 92308240023212233)^1964005106876856 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
              subst q
              change (5 : ZMod 92308240023212233)^1741664906098344 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 12601 := Nat.prime_eq_prime_of_dvd_pow hq prime_12601 hd
                subst q
                change (5 : ZMod 92308240023212233)^7325469409032 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 716563 := Nat.prime_eq_prime_of_dvd_pow hq prime_716563 hd
                subst q
                change (5 : ZMod 92308240023212233)^128820829464 ≠ 1
                reduce_mod_char
                decide

theorem prime_92915974333361161 : Nat.Prime 92915974333361161 := by
  apply lucas_primality 92915974333361161 (13 : ZMod 92915974333361161)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 92915974333361161 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((93083 : ℕ)^1 * ((924264469 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 92915974333361161)^46457987166680580 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 92915974333361161)^30971991444453720 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 92915974333361161)^18583194866672232 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 93083 := Nat.prime_eq_prime_of_dvd_pow hq prime_93083 hd
            subst q
            change (13 : ZMod 92915974333361161)^998205626520 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 924264469 := Nat.prime_eq_prime_of_dvd_pow hq prime_924264469 hd
            subst q
            change (13 : ZMod 92915974333361161)^100529640 ≠ 1
            reduce_mod_char
            decide

theorem prime_93747431820736627 : Nat.Prime 93747431820736627 := by
  apply lucas_primality 93747431820736627 (2 : ZMod 93747431820736627)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 93747431820736627 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1269643 : ℕ)^1 * ((12306271897 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 93747431820736627)^46873715910368313 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 93747431820736627)^31249143940245542 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1269643 := Nat.prime_eq_prime_of_dvd_pow hq prime_1269643 hd
          subst q
          change (2 : ZMod 93747431820736627)^73837631382 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 12306271897 := Nat.prime_eq_prime_of_dvd_pow hq prime_12306271897 hd
          subst q
          change (2 : ZMod 93747431820736627)^7617858 ≠ 1
          reduce_mod_char
          decide

theorem prime_94152792067807717 : Nat.Prime 94152792067807717 := by
  apply lucas_primality 94152792067807717 (5 : ZMod 94152792067807717)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 94152792067807717 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((43 : ℕ)^1 * ((3217 : ℕ)^1 * ((14449 : ℕ)^1 * ((1308499 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 94152792067807717)^47076396033903858 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 94152792067807717)^31384264022602572 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (5 : ZMod 94152792067807717)^2189599815530412 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3217 := Nat.prime_eq_prime_of_dvd_pow hq prime_3217 hd
            subst q
            change (5 : ZMod 94152792067807717)^29267265174948 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 14449 := Nat.prime_eq_prime_of_dvd_pow hq prime_14449 hd
              subst q
              change (5 : ZMod 94152792067807717)^6516215106084 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1308499 := Nat.prime_eq_prime_of_dvd_pow hq prime_1308499 hd
              subst q
              change (5 : ZMod 94152792067807717)^71954806284 ≠ 1
              reduce_mod_char
              decide

theorem prime_94585080322265629 : Nat.Prime 94585080322265629 := by
  apply lucas_primality 94585080322265629 (7 : ZMod 94585080322265629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 94585080322265629 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((193 : ℕ)^1 * ((654421 : ℕ)^1 * ((62406073 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 94585080322265629)^47292540161132814 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 94585080322265629)^31528360107421876 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
          subst q
          change (7 : ZMod 94585080322265629)^490078136384796 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 654421 := Nat.prime_eq_prime_of_dvd_pow hq prime_654421 hd
            subst q
            change (7 : ZMod 94585080322265629)^144532465068 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 62406073 := Nat.prime_eq_prime_of_dvd_pow hq prime_62406073 hd
            subst q
            change (7 : ZMod 94585080322265629)^1515639036 ≠ 1
            reduce_mod_char
            decide

theorem prime_94644875340166667 : Nat.Prime 94644875340166667 := by
  apply lucas_primality 94644875340166667 (2 : ZMod 94644875340166667)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 94644875340166667 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((31 : ℕ)^1 * ((238321 : ℕ)^1 * ((376785499 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 94644875340166667)^47322437670083333 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 94644875340166667)^5567345608245098 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (2 : ZMod 94644875340166667)^3053060494844086 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 238321 := Nat.prime_eq_prime_of_dvd_pow hq prime_238321 hd
            subst q
            change (2 : ZMod 94644875340166667)^397131915946 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 376785499 := Nat.prime_eq_prime_of_dvd_pow hq prime_376785499 hd
            subst q
            change (2 : ZMod 94644875340166667)^251190334 ≠ 1
            reduce_mod_char
            decide

theorem prime_95428956661682197 : Nat.Prime 95428956661682197 := by
  apply lucas_primality 95428956661682197 (2 : ZMod 95428956661682197)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 95428956661682197 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((23 : ℕ)^1 * ((1129 : ℕ)^1 * ((8363 : ℕ)^1 * ((5231389 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 95428956661682197)^47714478330841098 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 95428956661682197)^31809652220560732 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 95428956661682197)^13632708094526028 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (2 : ZMod 95428956661682197)^4149085072247052 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1129 := Nat.prime_eq_prime_of_dvd_pow hq prime_1129 hd
              subst q
              change (2 : ZMod 95428956661682197)^84525205191924 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 8363 := Nat.prime_eq_prime_of_dvd_pow hq prime_8363 hd
                subst q
                change (2 : ZMod 95428956661682197)^11410852165692 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 5231389 := Nat.prime_eq_prime_of_dvd_pow hq prime_5231389 hd
                subst q
                change (2 : ZMod 95428956661682197)^18241609764 ≠ 1
                reduce_mod_char
                decide

theorem prime_96279097826745331 : Nat.Prime 96279097826745331 := by
  apply lucas_primality 96279097826745331 (2 : ZMod 96279097826745331)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 96279097826745331 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((173 : ℕ)^1 * ((503 : ℕ)^1 * ((4483 : ℕ)^1 * ((1175249 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 96279097826745331)^48139548913372665 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 96279097826745331)^32093032608915110 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 96279097826745331)^19255819565349066 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (2 : ZMod 96279097826745331)^13754156832392190 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
              subst q
              change (2 : ZMod 96279097826745331)^556526577033210 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 503 := Nat.prime_eq_prime_of_dvd_pow hq prime_503 hd
                subst q
                change (2 : ZMod 96279097826745331)^191409737230110 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 4483 := Nat.prime_eq_prime_of_dvd_pow hq prime_4483 hd
                  subst q
                  change (2 : ZMod 96279097826745331)^21476488473510 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 1175249 := Nat.prime_eq_prime_of_dvd_pow hq prime_1175249 hd
                  subst q
                  change (2 : ZMod 96279097826745331)^81922297170 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_97135540969725527 : Nat.Prime 97135540969725527 := by
  apply lucas_primality 97135540969725527 (5 : ZMod 97135540969725527)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 97135540969725527 - 1 = (2 : ℕ)^1 * ((103 : ℕ)^1 * ((1049 : ℕ)^1 * ((449505960229 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 97135540969725527)^48567770484862763 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
        subst q
        change (5 : ZMod 97135540969725527)^943063504560442 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1049 := Nat.prime_eq_prime_of_dvd_pow hq prime_1049 hd
          subst q
          change (5 : ZMod 97135540969725527)^92598227807174 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 449505960229 := Nat.prime_eq_prime_of_dvd_pow hq prime_449505960229 hd
          subst q
          change (5 : ZMod 97135540969725527)^216094 ≠ 1
          reduce_mod_char
          decide

theorem prime_97998323407891927 : Nat.Prime 97998323407891927 := by
  apply lucas_primality 97998323407891927 (3 : ZMod 97998323407891927)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 97998323407891927 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((9103 : ℕ)^1 * ((938129 : ℕ)^1 * ((1912583 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 97998323407891927)^48999161703945963 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 97998323407891927)^32666107802630642 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 9103 := Nat.prime_eq_prime_of_dvd_pow hq prime_9103 hd
          subst q
          change (3 : ZMod 97998323407891927)^10765497463242 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 938129 := Nat.prime_eq_prime_of_dvd_pow hq prime_938129 hd
            subst q
            change (3 : ZMod 97998323407891927)^104461458294 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1912583 := Nat.prime_eq_prime_of_dvd_pow hq prime_1912583 hd
            subst q
            change (3 : ZMod 97998323407891927)^51238729722 ≠ 1
            reduce_mod_char
            decide

theorem prime_98867482624000007 : Nat.Prime 98867482624000007 := by
  apply lucas_primality 98867482624000007 (5 : ZMod 98867482624000007)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 98867482624000007 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((7061963044571429 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 98867482624000007)^49433741312000003 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 98867482624000007)^14123926089142858 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7061963044571429 := Nat.prime_eq_prime_of_dvd_pow hq prime_7061963044571429 hd
        subst q
        change (5 : ZMod 98867482624000007)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_99743056266780107 : Nat.Prime 99743056266780107 := by
  apply lucas_primality 99743056266780107 (2 : ZMod 99743056266780107)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 99743056266780107 - 1 = (2 : ℕ)^1 * ((41 : ℕ)^1 * ((3881 : ℕ)^1 * ((313418895893 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 99743056266780107)^49871528133390053 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
        subst q
        change (2 : ZMod 99743056266780107)^2432757469921466 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 3881 := Nat.prime_eq_prime_of_dvd_pow hq prime_3881 hd
          subst q
          change (2 : ZMod 99743056266780107)^25700349463226 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 313418895893 := Nat.prime_eq_prime_of_dvd_pow hq prime_313418895893 hd
          subst q
          change (2 : ZMod 99743056266780107)^318242 ≠ 1
          reduce_mod_char
          decide

theorem prime_100625082151426627 : Nat.Prime 100625082151426627 := by
  apply lucas_primality 100625082151426627 (2 : ZMod 100625082151426627)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 100625082151426627 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((8681 : ℕ)^1 * ((1931902663891 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 100625082151426627)^50312541075713313 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 100625082151426627)^33541694050475542 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 8681 := Nat.prime_eq_prime_of_dvd_pow hq prime_8681 hd
          subst q
          change (2 : ZMod 100625082151426627)^11591415983346 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1931902663891 := Nat.prime_eq_prime_of_dvd_pow hq prime_1931902663891 hd
          subst q
          change (2 : ZMod 100625082151426627)^52086 ≠ 1
          reduce_mod_char
          decide

theorem prime_101513598260088191 : Nat.Prime 101513598260088191 := by
  apply lucas_primality 101513598260088191 (7 : ZMod 101513598260088191)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 101513598260088191 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^2 * ((23537 : ℕ)^1 * ((31333 : ℕ)^1 * ((113759 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 101513598260088191)^50756799130044095 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 101513598260088191)^20302719652017638 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (7 : ZMod 101513598260088191)^9228508932735290 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23537 := Nat.prime_eq_prime_of_dvd_pow hq prime_23537 hd
            subst q
            change (7 : ZMod 101513598260088191)^4312937003870 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 31333 := Nat.prime_eq_prime_of_dvd_pow hq prime_31333 hd
              subst q
              change (7 : ZMod 101513598260088191)^3239830155430 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 113759 := Nat.prime_eq_prime_of_dvd_pow hq prime_113759 hd
              subst q
              change (7 : ZMod 101513598260088191)^892356633410 ≠ 1
              reduce_mod_char
              decide

theorem prime_102238205991621881 : Nat.Prime 102238205991621881 := by
  apply lucas_primality 102238205991621881 (3 : ZMod 102238205991621881)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 102238205991621881 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((61 : ℕ)^1 * ((1163 : ℕ)^1 * ((3001 : ℕ)^1 * ((3187 : ℕ)^1 * ((3767 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 102238205991621881)^51119102995810940 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 102238205991621881)^20447641198324376 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (3 : ZMod 102238205991621881)^1676036163797080 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1163 := Nat.prime_eq_prime_of_dvd_pow hq prime_1163 hd
            subst q
            change (3 : ZMod 102238205991621881)^87909033526760 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 3001 := Nat.prime_eq_prime_of_dvd_pow hq prime_3001 hd
              subst q
              change (3 : ZMod 102238205991621881)^34068045981880 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 3187 := Nat.prime_eq_prime_of_dvd_pow hq prime_3187 hd
                subst q
                change (3 : ZMod 102238205991621881)^32079763411240 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 3767 := Nat.prime_eq_prime_of_dvd_pow hq prime_3767 hd
                subst q
                change (3 : ZMod 102238205991621881)^27140484733640 ≠ 1
                reduce_mod_char
                decide

theorem prime_102408642742358041 : Nat.Prime 102408642742358041 := by
  apply lucas_primality 102408642742358041 (13 : ZMod 102408642742358041)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 102408642742358041 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((269 : ℕ)^1 * ((3889 : ℕ)^1 * ((74160467 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 102408642742358041)^51204321371179020 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 102408642742358041)^34136214247452680 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (13 : ZMod 102408642742358041)^20481728548471608 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (13 : ZMod 102408642742358041)^9309876612941640 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
              subst q
              change (13 : ZMod 102408642742358041)^380701274135160 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 3889 := Nat.prime_eq_prime_of_dvd_pow hq prime_3889 hd
                subst q
                change (13 : ZMod 102408642742358041)^26332898622360 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 74160467 := Nat.prime_eq_prime_of_dvd_pow hq prime_74160467 hd
                subst q
                change (13 : ZMod 102408642742358041)^1380906120 ≠ 1
                reduce_mod_char
                decide

theorem prime_103310253915765647 : Nat.Prime 103310253915765647 := by
  apply lucas_primality 103310253915765647 (5 : ZMod 103310253915765647)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 103310253915765647 - 1 = (2 : ℕ)^1 * ((1032506597 : ℕ)^1 * ((50028859 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 103310253915765647)^51655126957882823 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1032506597 := Nat.prime_eq_prime_of_dvd_pow hq prime_1032506597 hd
        subst q
        change (5 : ZMod 103310253915765647)^100057718 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 50028859 := Nat.prime_eq_prime_of_dvd_pow hq prime_50028859 hd
        subst q
        change (5 : ZMod 103310253915765647)^2065013194 ≠ 1
        reduce_mod_char
        decide

theorem prime_104218470266268769 : Nat.Prime 104218470266268769 := by
  apply lucas_primality 104218470266268769 (7 : ZMod 104218470266268769)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 104218470266268769 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((1627 : ℕ)^1 * ((120091 : ℕ)^1 * ((5556169 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 104218470266268769)^52109235133134384 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 104218470266268769)^34739490088756256 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1627 := Nat.prime_eq_prime_of_dvd_pow hq prime_1627 hd
          subst q
          change (7 : ZMod 104218470266268769)^64055605572384 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 120091 := Nat.prime_eq_prime_of_dvd_pow hq prime_120091 hd
            subst q
            change (7 : ZMod 104218470266268769)^867829148448 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 5556169 := Nat.prime_eq_prime_of_dvd_pow hq prime_5556169 hd
            subst q
            change (7 : ZMod 104218470266268769)^18757253472 ≠ 1
            reduce_mod_char
            decide

theorem prime_105133330448746231 : Nat.Prime 105133330448746231 := by
  apply lucas_primality 105133330448746231 (6 : ZMod 105133330448746231)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 105133330448746231 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((3504444348291541 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 105133330448746231)^52566665224373115 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 105133330448746231)^35044443482915410 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 105133330448746231)^21026666089749246 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3504444348291541 := Nat.prime_eq_prime_of_dvd_pow hq prime_3504444348291541 hd
          subst q
          change (6 : ZMod 105133330448746231)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_106054873287491603 : Nat.Prime 106054873287491603 := by
  apply lucas_primality 106054873287491603 (2 : ZMod 106054873287491603)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 106054873287491603 - 1 = (2 : ℕ)^1 * ((499 : ℕ)^1 * ((106267408103699 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 106054873287491603)^53027436643745801 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 499 := Nat.prime_eq_prime_of_dvd_pow hq prime_499 hd
        subst q
        change (2 : ZMod 106054873287491603)^212534816207398 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 106267408103699 := Nat.prime_eq_prime_of_dvd_pow hq prime_106267408103699 hd
        subst q
        change (2 : ZMod 106054873287491603)^998 ≠ 1
        reduce_mod_char
        decide

theorem prime_106983137776707377 : Nat.Prime 106983137776707377 := by
  apply lucas_primality 106983137776707377 (3 : ZMod 106983137776707377)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 106983137776707377 - 1 = (2 : ℕ)^4 * ((2539 : ℕ)^1 * ((2633495908249 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 106983137776707377)^53491568888353688 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 2539 := Nat.prime_eq_prime_of_dvd_pow hq prime_2539 hd
        subst q
        change (3 : ZMod 106983137776707377)^42135934531984 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2633495908249 := Nat.prime_eq_prime_of_dvd_pow hq prime_2633495908249 hd
        subst q
        change (3 : ZMod 106983137776707377)^40624 ≠ 1
        reduce_mod_char
        decide

theorem prime_107918163081000029 : Nat.Prime 107918163081000029 := by
  apply lucas_primality 107918163081000029 (2 : ZMod 107918163081000029)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 107918163081000029 - 1 = (2 : ℕ)^2 * ((191 : ℕ)^1 * ((26101037 : ℕ)^1 * ((5411821 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 107918163081000029)^53959081540500014 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
        subst q
        change (2 : ZMod 107918163081000029)^565016560633508 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 26101037 := Nat.prime_eq_prime_of_dvd_pow hq prime_26101037 hd
          subst q
          change (2 : ZMod 107918163081000029)^4134631244 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 5411821 := Nat.prime_eq_prime_of_dvd_pow hq prime_5411821 hd
          subst q
          change (2 : ZMod 107918163081000029)^19941192268 ≠ 1
          reduce_mod_char
          decide

theorem prime_108859988535875713 : Nat.Prime 108859988535875713 := by
  apply lucas_primality 108859988535875713 (7 : ZMod 108859988535875713)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 108859988535875713 - 1 = (2 : ℕ)^7 * ((3 : ℕ)^5 * ((873293 : ℕ)^1 * ((4007671 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 108859988535875713)^54429994267937856 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 108859988535875713)^36286662845291904 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 873293 := Nat.prime_eq_prime_of_dvd_pow hq prime_873293 hd
          subst q
          change (7 : ZMod 108859988535875713)^124654598784 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4007671 := Nat.prime_eq_prime_of_dvd_pow hq prime_4007671 hd
          subst q
          change (7 : ZMod 108859988535875713)^27162905472 ≠ 1
          reduce_mod_char
          decide

theorem prime_109808653648236589 : Nat.Prime 109808653648236589 := by
  apply lucas_primality 109808653648236589 (2 : ZMod 109808653648236589)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 109808653648236589 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((47 : ℕ)^1 * ((64898731470589 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 109808653648236589)^54904326824118294 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 109808653648236589)^36602884549412196 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (2 : ZMod 109808653648236589)^2336354332941204 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 64898731470589 := Nat.prime_eq_prime_of_dvd_pow hq prime_64898731470589 hd
          subst q
          change (2 : ZMod 109808653648236589)^1692 ≠ 1
          reduce_mod_char
          decide

theorem prime_110764198096878289 : Nat.Prime 110764198096878289 := by
  apply lucas_primality 110764198096878289 (7 : ZMod 110764198096878289)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 110764198096878289 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((313 : ℕ)^1 * ((7372483898887 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 110764198096878289)^55382099048439144 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 110764198096878289)^36921399365626096 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 313 := Nat.prime_eq_prime_of_dvd_pow hq prime_313 hd
          subst q
          change (7 : ZMod 110764198096878289)^353879227146576 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7372483898887 := Nat.prime_eq_prime_of_dvd_pow hq prime_7372483898887 hd
          subst q
          change (7 : ZMod 110764198096878289)^15024 ≠ 1
          reduce_mod_char
          decide

theorem prime_111726661732987529 : Nat.Prime 111726661732987529 := by
  apply lucas_primality 111726661732987529 (3 : ZMod 111726661732987529)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 111726661732987529 - 1 = (2 : ℕ)^3 * ((20483 : ℕ)^1 * ((681825548827 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 111726661732987529)^55863330866493764 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 20483 := Nat.prime_eq_prime_of_dvd_pow hq prime_20483 hd
        subst q
        change (3 : ZMod 111726661732987529)^5454604390616 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 681825548827 := Nat.prime_eq_prime_of_dvd_pow hq prime_681825548827 hd
        subst q
        change (3 : ZMod 111726661732987529)^163864 ≠ 1
        reduce_mod_char
        decide

theorem prime_112696084580640637 : Nat.Prime 112696084580640637 := by
  apply lucas_primality 112696084580640637 (2 : ZMod 112696084580640637)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 112696084580640637 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((467 : ℕ)^1 * ((1122157 : ℕ)^1 * ((17920787 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 112696084580640637)^56348042290320318 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 112696084580640637)^37565361526880212 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 467 := Nat.prime_eq_prime_of_dvd_pow hq prime_467 hd
          subst q
          change (2 : ZMod 112696084580640637)^241319238930708 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1122157 := Nat.prime_eq_prime_of_dvd_pow hq prime_1122157 hd
            subst q
            change (2 : ZMod 112696084580640637)^100428090348 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 17920787 := Nat.prime_eq_prime_of_dvd_pow hq prime_17920787 hd
            subst q
            change (2 : ZMod 112696084580640637)^6288567828 ≠ 1
            reduce_mod_char
            decide

theorem prime_113672506837303313 : Nat.Prime 113672506837303313 := by
  apply lucas_primality 113672506837303313 (3 : ZMod 113672506837303313)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 113672506837303313 - 1 = (2 : ℕ)^4 * ((17 : ℕ)^1 * ((417913628078321 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 113672506837303313)^56836253418651656 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (3 : ZMod 113672506837303313)^6686618049253136 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 417913628078321 := Nat.prime_eq_prime_of_dvd_pow hq prime_417913628078321 hd
        subst q
        change (3 : ZMod 113672506837303313)^272 ≠ 1
        reduce_mod_char
        decide

theorem prime_114655968874330133 : Nat.Prime 114655968874330133 := by
  apply lucas_primality 114655968874330133 (2 : ZMod 114655968874330133)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 114655968874330133 - 1 = (2 : ℕ)^2 * ((967 : ℕ)^1 * ((13669 : ℕ)^1 * ((2168570071 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 114655968874330133)^57327984437165066 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 967 := Nat.prime_eq_prime_of_dvd_pow hq prime_967 hd
        subst q
        change (2 : ZMod 114655968874330133)^118568737201996 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13669 := Nat.prime_eq_prime_of_dvd_pow hq prime_13669 hd
          subst q
          change (2 : ZMod 114655968874330133)^8388029034628 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2168570071 := Nat.prime_eq_prime_of_dvd_pow hq prime_2168570071 hd
          subst q
          change (2 : ZMod 114655968874330133)^52871692 ≠ 1
          reduce_mod_char
          decide

theorem prime_115646511237465667 : Nat.Prime 115646511237465667 := by
  apply lucas_primality 115646511237465667 (2 : ZMod 115646511237465667)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 115646511237465667 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((641891 : ℕ)^1 * ((30027556921 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 115646511237465667)^57823255618732833 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 115646511237465667)^38548837079155222 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 641891 := Nat.prime_eq_prime_of_dvd_pow hq prime_641891 hd
          subst q
          change (2 : ZMod 115646511237465667)^180165341526 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 30027556921 := Nat.prime_eq_prime_of_dvd_pow hq prime_30027556921 hd
          subst q
          change (2 : ZMod 115646511237465667)^3851346 ≠ 1
          reduce_mod_char
          decide

theorem prime_116644174647345811 : Nat.Prime 116644174647345811 := by
  apply lucas_primality 116644174647345811 (7 : ZMod 116644174647345811)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 116644174647345811 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((5113 : ℕ)^1 * ((22073 : ℕ)^1 * ((11483741 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 116644174647345811)^58322087323672905 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 116644174647345811)^38881391549115270 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 116644174647345811)^23328834929469162 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 5113 := Nat.prime_eq_prime_of_dvd_pow hq prime_5113 hd
            subst q
            change (7 : ZMod 116644174647345811)^22813255358370 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 22073 := Nat.prime_eq_prime_of_dvd_pow hq prime_22073 hd
              subst q
              change (7 : ZMod 116644174647345811)^5284473095970 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 11483741 := Nat.prime_eq_prime_of_dvd_pow hq prime_11483741 hd
              subst q
              change (7 : ZMod 116644174647345811)^10157332410 ≠ 1
              reduce_mod_char
              decide

theorem prime_117649000000000013 : Nat.Prime 117649000000000013 := by
  apply lucas_primality 117649000000000013 (2 : ZMod 117649000000000013)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 117649000000000013 - 1 = (2 : ℕ)^2 * ((19 : ℕ)^1 * ((883 : ℕ)^1 * ((1753129284139 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 117649000000000013)^58824500000000006 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 117649000000000013)^6192052631578948 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 883 := Nat.prime_eq_prime_of_dvd_pow hq prime_883 hd
          subst q
          change (2 : ZMod 117649000000000013)^133237825594564 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1753129284139 := Nat.prime_eq_prime_of_dvd_pow hq prime_1753129284139 hd
          subst q
          change (2 : ZMod 117649000000000013)^67108 ≠ 1
          reduce_mod_char
          decide

theorem prime_118661028367354243 : Nat.Prime 118661028367354243 := by
  apply lucas_primality 118661028367354243 (5 : ZMod 118661028367354243)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 118661028367354243 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((256842052743191 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 118661028367354243)^59330514183677121 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 118661028367354243)^39553676122451414 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 118661028367354243)^16951575481050606 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (5 : ZMod 118661028367354243)^10787366215214022 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 256842052743191 := Nat.prime_eq_prime_of_dvd_pow hq prime_256842052743191 hd
            subst q
            change (5 : ZMod 118661028367354243)^462 ≠ 1
            reduce_mod_char
            decide

theorem prime_118800535564110233 : Nat.Prime 118800535564110233 := by
  apply lucas_primality 118800535564110233 (3 : ZMod 118800535564110233)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 118800535564110233 - 1 = (2 : ℕ)^3 * ((7 : ℕ)^2 * ((15031 : ℕ)^1 * ((20162503541 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 118800535564110233)^59400267782055116 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 118800535564110233)^16971505080587176 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 15031 := Nat.prime_eq_prime_of_dvd_pow hq prime_15031 hd
          subst q
          change (3 : ZMod 118800535564110233)^7903701388072 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 20162503541 := Nat.prime_eq_prime_of_dvd_pow hq prime_20162503541 hd
          subst q
          change (3 : ZMod 118800535564110233)^5892152 ≠ 1
          reduce_mod_char
          decide

theorem prime_119680300997734483 : Nat.Prime 119680300997734483 := by
  apply lucas_primality 119680300997734483 (2 : ZMod 119680300997734483)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 119680300997734483 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((19 : ℕ)^1 * ((107273 : ℕ)^1 * ((3262166627 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 119680300997734483)^59840150498867241 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 119680300997734483)^39893433665911494 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 119680300997734483)^6298963210407078 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 107273 := Nat.prime_eq_prime_of_dvd_pow hq prime_107273 hd
            subst q
            change (2 : ZMod 119680300997734483)^1115660986434 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3262166627 := Nat.prime_eq_prime_of_dvd_pow hq prime_3262166627 hd
            subst q
            change (2 : ZMod 119680300997734483)^36687366 ≠ 1
            reduce_mod_char
            decide

theorem prime_120030131812110701 : Nat.Prime 120030131812110701 := by
  apply lucas_primality 120030131812110701 (2 : ZMod 120030131812110701)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 120030131812110701 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((193 : ℕ)^1 * ((50773 : ℕ)^1 * ((122489863 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 120030131812110701)^60015065906055350 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 120030131812110701)^24006026362422140 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
          subst q
          change (2 : ZMod 120030131812110701)^621917781409900 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 50773 := Nat.prime_eq_prime_of_dvd_pow hq prime_50773 hd
            subst q
            change (2 : ZMod 120030131812110701)^2364054355900 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 122489863 := Nat.prime_eq_prime_of_dvd_pow hq prime_122489863 hd
            subst q
            change (2 : ZMod 120030131812110701)^979918900 ≠ 1
            reduce_mod_char
            decide

theorem prime_120706859316371347 : Nat.Prime 120706859316371347 := by
  apply lucas_primality 120706859316371347 (2 : ZMod 120706859316371347)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 120706859316371347 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((23 : ℕ)^1 * ((163 : ℕ)^1 * ((1685473 : ℕ)^1 * ((1061261 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 120706859316371347)^60353429658185673 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 120706859316371347)^40235619772123782 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 120706859316371347)^5248124318103102 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
            subst q
            change (2 : ZMod 120706859316371347)^740532879241542 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1685473 := Nat.prime_eq_prime_of_dvd_pow hq prime_1685473 hd
              subst q
              change (2 : ZMod 120706859316371347)^71616014802 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1061261 := Nat.prime_eq_prime_of_dvd_pow hq prime_1061261 hd
              subst q
              change (2 : ZMod 120706859316371347)^113739088986 ≠ 1
              reduce_mod_char
              decide

theorem prime_121740744925904953 : Nat.Prime 121740744925904953 := by
  apply lucas_primality 121740744925904953 (10 : ZMod 121740744925904953)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 121740744925904953 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((137 : ℕ)^1 * ((1459 : ℕ)^1 * ((1335657949 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 121740744925904953)^60870372462952476 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 121740744925904953)^40580248308634984 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (10 : ZMod 121740744925904953)^6407407627679208 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
            subst q
            change (10 : ZMod 121740744925904953)^888618576101496 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1459 := Nat.prime_eq_prime_of_dvd_pow hq prime_1459 hd
              subst q
              change (10 : ZMod 121740744925904953)^83441223389928 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1335657949 := Nat.prime_eq_prime_of_dvd_pow hq prime_1335657949 hd
              subst q
              change (10 : ZMod 121740744925904953)^91146648 ≠ 1
              reduce_mod_char
              decide

theorem prime_122781999606890653 : Nat.Prime 122781999606890653 := by
  apply lucas_primality 122781999606890653 (2 : ZMod 122781999606890653)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 122781999606890653 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((61 : ℕ)^1 * ((97 : ℕ)^1 * ((199 : ℕ)^1 * ((379 : ℕ)^1 * ((439 : ℕ)^1 * ((829 : ℕ)^1)))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 122781999606890653)^61390999803445326 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 122781999606890653)^40927333202296884 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 122781999606890653)^17540285658127236 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
            subst q
            change (2 : ZMod 122781999606890653)^2012819665686732 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
              subst q
              change (2 : ZMod 122781999606890653)^1265793810380316 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 199 := Nat.prime_eq_prime_of_dvd_pow hq prime_199 hd
                subst q
                change (2 : ZMod 122781999606890653)^616994972898948 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 379 := Nat.prime_eq_prime_of_dvd_pow hq prime_379 hd
                  subst q
                  change (2 : ZMod 122781999606890653)^323963059648788 ≠ 1
                  reduce_mod_char
                  decide
                · rcases hq.dvd_mul.mp hd with hd | hd
                  · have heq : q = 439 := Nat.prime_eq_prime_of_dvd_pow hq prime_439 hd
                    subst q
                    change (2 : ZMod 122781999606890653)^279685648307268 ≠ 1
                    reduce_mod_char
                    decide
                  · have heq : q = 829 := Nat.prime_eq_prime_of_dvd_pow hq prime_829 hd
                    subst q
                    change (2 : ZMod 122781999606890653)^148108564061388 ≠ 1
                    reduce_mod_char
                    decide

theorem prime_123830665318305859 : Nat.Prime 123830665318305859 := by
  apply lucas_primality 123830665318305859 (2 : ZMod 123830665318305859)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 123830665318305859 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((43 : ℕ)^1 * ((251 : ℕ)^1 * ((1627 : ℕ)^1 * ((106845083 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 123830665318305859)^61915332659152929 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 123830665318305859)^41276888439435286 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 123830665318305859)^11257333210755078 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (2 : ZMod 123830665318305859)^2879782914379206 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 251 := Nat.prime_eq_prime_of_dvd_pow hq prime_251 hd
              subst q
              change (2 : ZMod 123830665318305859)^493349264216358 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 1627 := Nat.prime_eq_prime_of_dvd_pow hq prime_1627 hd
                subst q
                change (2 : ZMod 123830665318305859)^76109812734054 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 106845083 := Nat.prime_eq_prime_of_dvd_pow hq prime_106845083 hd
                subst q
                change (2 : ZMod 123830665318305859)^1158973926 ≠ 1
                reduce_mod_char
                decide

theorem prime_124357659104446843 : Nat.Prime 124357659104446843 := by
  apply lucas_primality 124357659104446843 (3 : ZMod 124357659104446843)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 124357659104446843 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((3089 : ℕ)^1 * ((6709704278863 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 124357659104446843)^62178829552223421 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 124357659104446843)^41452553034815614 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 3089 := Nat.prime_eq_prime_of_dvd_pow hq prime_3089 hd
          subst q
          change (3 : ZMod 124357659104446843)^40258225673178 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 6709704278863 := Nat.prime_eq_prime_of_dvd_pow hq prime_6709704278863 hd
          subst q
          change (3 : ZMod 124357659104446843)^18534 ≠ 1
          reduce_mod_char
          decide

theorem prime_124886784198057109 : Nat.Prime 124886784198057109 := by
  apply lucas_primality 124886784198057109 (11 : ZMod 124886784198057109)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 124886784198057109 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((757 : ℕ)^1 * ((808705572811 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 124886784198057109)^62443392099028554 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 124886784198057109)^41628928066019036 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (11 : ZMod 124886784198057109)^7346281423415124 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 757 := Nat.prime_eq_prime_of_dvd_pow hq prime_757 hd
            subst q
            change (11 : ZMod 124886784198057109)^164975936853444 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 808705572811 := Nat.prime_eq_prime_of_dvd_pow hq prime_808705572811 hd
            subst q
            change (11 : ZMod 124886784198057109)^154428 ≠ 1
            reduce_mod_char
            decide

theorem prime_125950398563487811 : Nat.Prime 125950398563487811 := by
  apply lucas_primality 125950398563487811 (11 : ZMod 125950398563487811)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 125950398563487811 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((67 : ℕ)^1 * ((4820145371737 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 125950398563487811)^62975199281743905 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 125950398563487811)^41983466187829270 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 125950398563487811)^25190079712697562 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (11 : ZMod 125950398563487811)^9688492197191370 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
              subst q
              change (11 : ZMod 125950398563487811)^1879856694977430 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 4820145371737 := Nat.prime_eq_prime_of_dvd_pow hq prime_4820145371737 hd
              subst q
              change (11 : ZMod 125950398563487811)^26130 ≠ 1
              reduce_mod_char
              decide

theorem prime_127021550911887257 : Nat.Prime 127021550911887257 := by
  apply lucas_primality 127021550911887257 (3 : ZMod 127021550911887257)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 127021550911887257 - 1 = (2 : ℕ)^3 * ((17 : ℕ)^1 * ((79 : ℕ)^1 * ((1193 : ℕ)^1 * ((9909938693 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 127021550911887257)^63510775455943628 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (3 : ZMod 127021550911887257)^7471855935993368 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (3 : ZMod 127021550911887257)^1607867733061864 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1193 := Nat.prime_eq_prime_of_dvd_pow hq prime_1193 hd
            subst q
            change (3 : ZMod 127021550911887257)^106472381317592 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 9909938693 := Nat.prime_eq_prime_of_dvd_pow hq prime_9909938693 hd
            subst q
            change (3 : ZMod 127021550911887257)^12817592 ≠ 1
            reduce_mod_char
            decide

theorem prime_128100283921000009 : Nat.Prime 128100283921000009 := by
  apply lucas_primality 128100283921000009 (7 : ZMod 128100283921000009)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 128100283921000009 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((139 : ℕ)^1 * ((84017 : ℕ)^1 * ((152347603 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 128100283921000009)^64050141960500004 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 128100283921000009)^42700094640333336 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
          subst q
          change (7 : ZMod 128100283921000009)^921584776410072 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 84017 := Nat.prime_eq_prime_of_dvd_pow hq prime_84017 hd
            subst q
            change (7 : ZMod 128100283921000009)^1524694810824 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 152347603 := Nat.prime_eq_prime_of_dvd_pow hq prime_152347603 hd
            subst q
            change (7 : ZMod 128100283921000009)^840842136 ≠ 1
            reduce_mod_char
            decide

theorem prime_129186640449535811 : Nat.Prime 129186640449535811 := by
  apply lucas_primality 129186640449535811 (2 : ZMod 129186640449535811)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 129186640449535811 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((12918664044953581 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 129186640449535811)^64593320224767905 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 129186640449535811)^25837328089907162 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 12918664044953581 := Nat.prime_eq_prime_of_dvd_pow hq prime_12918664044953581 hd
        subst q
        change (2 : ZMod 129186640449535811)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_130280663537680387 : Nat.Prime 130280663537680387 := by
  apply lucas_primality 130280663537680387 (2 : ZMod 130280663537680387)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 130280663537680387 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((12659 : ℕ)^1 * ((1715257439209 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 130280663537680387)^65140331768840193 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 130280663537680387)^43426887845893462 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 12659 := Nat.prime_eq_prime_of_dvd_pow hq prime_12659 hd
          subst q
          change (2 : ZMod 130280663537680387)^10291544635254 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1715257439209 := Nat.prime_eq_prime_of_dvd_pow hq prime_1715257439209 hd
          subst q
          change (2 : ZMod 130280663537680387)^75954 ≠ 1
          reduce_mod_char
          decide

theorem prime_131382396407607421 : Nat.Prime 131382396407607421 := by
  apply lucas_primality 131382396407607421 (2 : ZMod 131382396407607421)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 131382396407607421 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((1571 : ℕ)^1 * ((1393829794267 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 131382396407607421)^65691198203803710 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 131382396407607421)^43794132135869140 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 131382396407607421)^26276479281521484 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1571 := Nat.prime_eq_prime_of_dvd_pow hq prime_1571 hd
            subst q
            change (2 : ZMod 131382396407607421)^83629787656020 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1393829794267 := Nat.prime_eq_prime_of_dvd_pow hq prime_1393829794267 hd
            subst q
            change (2 : ZMod 131382396407607421)^94260 ≠ 1
            reduce_mod_char
            decide

theorem prime_132491882463990359 : Nat.Prime 132491882463990359 := by
  apply lucas_primality 132491882463990359 (7 : ZMod 132491882463990359)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 132491882463990359 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((71 : ℕ)^1 * ((40567018513163 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 132491882463990359)^66245941231995179 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (7 : ZMod 132491882463990359)^5760516628869146 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
          subst q
          change (7 : ZMod 132491882463990359)^1866082851605498 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 40567018513163 := Nat.prime_eq_prime_of_dvd_pow hq prime_40567018513163 hd
          subst q
          change (7 : ZMod 132491882463990359)^3266 ≠ 1
          reduce_mod_char
          decide

theorem prime_133609165294515727 : Nat.Prime 133609165294515727 := by
  apply lucas_primality 133609165294515727 (5 : ZMod 133609165294515727)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 133609165294515727 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((37 : ℕ)^1 * ((3295723 : ℕ)^1 * ((10741963 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 133609165294515727)^66804582647257863 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 133609165294515727)^44536388431505242 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (5 : ZMod 133609165294515727)^7859362664383278 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
            subst q
            change (5 : ZMod 133609165294515727)^3611058521473398 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 3295723 := Nat.prime_eq_prime_of_dvd_pow hq prime_3295723 hd
              subst q
              change (5 : ZMod 133609165294515727)^40540168362 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 10741963 := Nat.prime_eq_prime_of_dvd_pow hq prime_10741963 hd
              subst q
              change (5 : ZMod 133609165294515727)^12438058602 ≠ 1
              reduce_mod_char
              decide

theorem prime_134048906629383569 : Nat.Prime 134048906629383569 := by
  apply lucas_primality 134048906629383569 (3 : ZMod 134048906629383569)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 134048906629383569 - 1 = (2 : ℕ)^4 * ((317 : ℕ)^1 * ((331 : ℕ)^1 * ((79846528199 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 134048906629383569)^67024453314691784 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 317 := Nat.prime_eq_prime_of_dvd_pow hq prime_317 hd
        subst q
        change (3 : ZMod 134048906629383569)^422867213341904 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 331 := Nat.prime_eq_prime_of_dvd_pow hq prime_331 hd
          subst q
          change (3 : ZMod 134048906629383569)^404981591025328 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 79846528199 := Nat.prime_eq_prime_of_dvd_pow hq prime_79846528199 hd
          subst q
          change (3 : ZMod 134048906629383569)^1678832 ≠ 1
          reduce_mod_char
          decide

theorem prime_134734288670396489 : Nat.Prime 134734288670396489 := by
  apply lucas_primality 134734288670396489 (3 : ZMod 134734288670396489)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 134734288670396489 - 1 = (2 : ℕ)^3 * ((17 : ℕ)^1 * ((281 : ℕ)^1 * ((1609 : ℕ)^1 * ((35267 : ℕ)^1 * ((62131 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 134734288670396489)^67367144335198244 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (3 : ZMod 134734288670396489)^7925546392376264 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 281 := Nat.prime_eq_prime_of_dvd_pow hq prime_281 hd
          subst q
          change (3 : ZMod 134734288670396489)^479481454343048 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1609 := Nat.prime_eq_prime_of_dvd_pow hq prime_1609 hd
            subst q
            change (3 : ZMod 134734288670396489)^83737904705032 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 35267 := Nat.prime_eq_prime_of_dvd_pow hq prime_35267 hd
              subst q
              change (3 : ZMod 134734288670396489)^3820406858264 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 62131 := Nat.prime_eq_prime_of_dvd_pow hq prime_62131 hd
              subst q
              change (3 : ZMod 134734288670396489)^2168551748248 ≠ 1
              reduce_mod_char
              decide

theorem prime_135867296546886997 : Nat.Prime 135867296546886997 := by
  apply lucas_primality 135867296546886997 (2 : ZMod 135867296546886997)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 135867296546886997 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((31 : ℕ)^1 * ((61 : ℕ)^1 * ((42841 : ℕ)^1 * ((170647 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 135867296546886997)^67933648273443498 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 135867296546886997)^45289098848962332 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 135867296546886997)^19409613792412428 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (2 : ZMod 135867296546886997)^10451330503606692 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
              subst q
              change (2 : ZMod 135867296546886997)^4382816017641516 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
                subst q
                change (2 : ZMod 135867296546886997)^2227332730276836 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 42841 := Nat.prime_eq_prime_of_dvd_pow hq prime_42841 hd
                  subst q
                  change (2 : ZMod 135867296546886997)^3171431491956 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 170647 := Nat.prime_eq_prime_of_dvd_pow hq prime_170647 hd
                  subst q
                  change (2 : ZMod 135867296546886997)^796189189068 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_137008233063797861 : Nat.Prime 137008233063797861 := by
  apply lucas_primality 137008233063797861 (2 : ZMod 137008233063797861)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 137008233063797861 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((797 : ℕ)^1 * ((7229 : ℕ)^1 * ((1188995261 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 137008233063797861)^68504116531898930 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 137008233063797861)^27401646612759572 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 797 := Nat.prime_eq_prime_of_dvd_pow hq prime_797 hd
          subst q
          change (2 : ZMod 137008233063797861)^171904934835380 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7229 := Nat.prime_eq_prime_of_dvd_pow hq prime_7229 hd
            subst q
            change (2 : ZMod 137008233063797861)^18952584460340 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1188995261 := Nat.prime_eq_prime_of_dvd_pow hq prime_1188995261 hd
            subst q
            change (2 : ZMod 137008233063797861)^115230260 ≠ 1
            reduce_mod_char
            decide

theorem prime_138157142546011697 : Nat.Prime 138157142546011697 := by
  apply lucas_primality 138157142546011697 (3 : ZMod 138157142546011697)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 138157142546011697 - 1 = (2 : ℕ)^4 * ((17 : ℕ)^1 * ((227 : ℕ)^1 * ((2237580049009 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 138157142546011697)^69078571273005848 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (3 : ZMod 138157142546011697)^8126890738000688 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 227 := Nat.prime_eq_prime_of_dvd_pow hq prime_227 hd
          subst q
          change (3 : ZMod 138157142546011697)^608621773330448 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2237580049009 := Nat.prime_eq_prime_of_dvd_pow hq prime_2237580049009 hd
          subst q
          change (3 : ZMod 138157142546011697)^61744 ≠ 1
          reduce_mod_char
          decide

theorem prime_139314069504000029 : Nat.Prime 139314069504000029 := by
  apply lucas_primality 139314069504000029 (2 : ZMod 139314069504000029)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 139314069504000029 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((53 : ℕ)^1 * ((631 : ℕ)^1 * ((94675383559 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 139314069504000029)^69657034752000014 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 139314069504000029)^12664915409454548 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (2 : ZMod 139314069504000029)^2628567349132076 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 631 := Nat.prime_eq_prime_of_dvd_pow hq prime_631 hd
            subst q
            change (2 : ZMod 139314069504000029)^220782994459588 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 94675383559 := Nat.prime_eq_prime_of_dvd_pow hq prime_94675383559 hd
            subst q
            change (2 : ZMod 139314069504000029)^1471492 ≠ 1
            reduce_mod_char
            decide

theorem prime_140479058634340367 : Nat.Prime 140479058634340367 := by
  apply lucas_primality 140479058634340367 (7 : ZMod 140479058634340367)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 140479058634340367 - 1 = (2 : ℕ)^1 * ((47 : ℕ)^1 * ((24203 : ℕ)^1 * ((61746811163 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 140479058634340367)^70239529317170183 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (7 : ZMod 140479058634340367)^2988916141156178 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 24203 := Nat.prime_eq_prime_of_dvd_pow hq prime_24203 hd
          subst q
          change (7 : ZMod 140479058634340367)^5804200249322 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 61746811163 := Nat.prime_eq_prime_of_dvd_pow hq prime_61746811163 hd
          subst q
          change (7 : ZMod 140479058634340367)^2275082 ≠ 1
          reduce_mod_char
          decide

theorem prime_141652154820234353 : Nat.Prime 141652154820234353 := by
  apply lucas_primality 141652154820234353 (3 : ZMod 141652154820234353)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 141652154820234353 - 1 = (2 : ℕ)^4 * ((7 : ℕ)^1 * ((859 : ℕ)^1 * ((1399 : ℕ)^1 * ((2203 : ℕ)^1 * ((477727 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 141652154820234353)^70826077410117176 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 141652154820234353)^20236022117176336 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 859 := Nat.prime_eq_prime_of_dvd_pow hq prime_859 hd
          subst q
          change (3 : ZMod 141652154820234353)^164903556251728 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1399 := Nat.prime_eq_prime_of_dvd_pow hq prime_1399 hd
            subst q
            change (3 : ZMod 141652154820234353)^101252433752848 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 2203 := Nat.prime_eq_prime_of_dvd_pow hq prime_2203 hd
              subst q
              change (3 : ZMod 141652154820234353)^64299661743184 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 477727 := Nat.prime_eq_prime_of_dvd_pow hq prime_477727 hd
              subst q
              change (3 : ZMod 141652154820234353)^296512767376 ≠ 1
              reduce_mod_char
              decide

theorem prime_142833403132026517 : Nat.Prime 142833403132026517 := by
  apply lucas_primality 142833403132026517 (6 : ZMod 142833403132026517)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 142833403132026517 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((7 : ℕ)^3 * ((13 : ℕ)^1 * ((43 : ℕ)^1 * ((73 : ℕ)^1 * ((127 : ℕ)^1 * ((313 : ℕ)^1 * ((2377 : ℕ)^1)))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 142833403132026517)^71416701566013258 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 142833403132026517)^47611134377342172 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 142833403132026517)^20404771876003788 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (6 : ZMod 142833403132026517)^10987184856309732 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
              subst q
              change (6 : ZMod 142833403132026517)^3321707049582012 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
                subst q
                change (6 : ZMod 142833403132026517)^1956621960712692 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
                  subst q
                  change (6 : ZMod 142833403132026517)^1124672465606508 ≠ 1
                  reduce_mod_char
                  decide
                · rcases hq.dvd_mul.mp hd with hd | hd
                  · have heq : q = 313 := Nat.prime_eq_prime_of_dvd_pow hq prime_313 hd
                    subst q
                    change (6 : ZMod 142833403132026517)^456336751220532 ≠ 1
                    reduce_mod_char
                    decide
                  · have heq : q = 2377 := Nat.prime_eq_prime_of_dvd_pow hq prime_2377 hd
                    subst q
                    change (6 : ZMod 142833403132026517)^60089778347508 ≠ 1
                    reduce_mod_char
                    decide

theorem prime_144022848827723779 : Nat.Prime 144022848827723779 := by
  apply lucas_primality 144022848827723779 (2 : ZMod 144022848827723779)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 144022848827723779 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((2182164376177633 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 144022848827723779)^72011424413861889 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 144022848827723779)^48007616275907926 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 144022848827723779)^13092986257065798 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2182164376177633 := Nat.prime_eq_prime_of_dvd_pow hq prime_2182164376177633 hd
          subst q
          change (2 : ZMod 144022848827723779)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_145220537353515653 : Nat.Prime 145220537353515653 := by
  apply lucas_primality 145220537353515653 (2 : ZMod 145220537353515653)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 145220537353515653 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((331 : ℕ)^1 * ((397 : ℕ)^1 * ((527803 : ℕ)^1 * ((74779 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 145220537353515653)^72610268676757826 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 145220537353515653)^20745791050502236 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 331 := Nat.prime_eq_prime_of_dvd_pow hq prime_331 hd
          subst q
          change (2 : ZMod 145220537353515653)^438732741249292 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 397 := Nat.prime_eq_prime_of_dvd_pow hq prime_397 hd
            subst q
            change (2 : ZMod 145220537353515653)^365794804416916 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 527803 := Nat.prime_eq_prime_of_dvd_pow hq prime_527803 hd
              subst q
              change (2 : ZMod 145220537353515653)^275141553484 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 74779 := Nat.prime_eq_prime_of_dvd_pow hq prime_74779 hd
              subst q
              change (2 : ZMod 145220537353515653)^1941996246988 ≠ 1
              reduce_mod_char
              decide

theorem prime_146426514344295037 : Nat.Prime 146426514344295037 := by
  apply lucas_primality 146426514344295037 (5 : ZMod 146426514344295037)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 146426514344295037 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((139 : ℕ)^1 * ((87785680062527 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 146426514344295037)^73213257172147518 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 146426514344295037)^48808838114765012 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
          subst q
          change (5 : ZMod 146426514344295037)^1053428160750324 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 87785680062527 := Nat.prime_eq_prime_of_dvd_pow hq prime_87785680062527 hd
          subst q
          change (5 : ZMod 146426514344295037)^1668 ≠ 1
          reduce_mod_char
          decide

theorem prime_146738778799360037 : Nat.Prime 146738778799360037 := by
  apply lucas_primality 146738778799360037 (2 : ZMod 146738778799360037)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 146738778799360037 - 1 = (2 : ℕ)^2 * ((223087 : ℕ)^1 * ((164441203207 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 146738778799360037)^73369389399680018 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 223087 := Nat.prime_eq_prime_of_dvd_pow hq prime_223087 hd
        subst q
        change (2 : ZMod 146738778799360037)^657764812828 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 164441203207 := Nat.prime_eq_prime_of_dvd_pow hq prime_164441203207 hd
        subst q
        change (2 : ZMod 146738778799360037)^892348 ≠ 1
        reduce_mod_char
        decide

end LegendreK6.Pratt
