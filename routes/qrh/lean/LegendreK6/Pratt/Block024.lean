import LegendreK6.Pratt.Block023

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LegendreK6.Pratt

theorem prime_147640825624179961 : Nat.Prime 147640825624179961 := by
  apply lucas_primality 147640825624179961 (7 : ZMod 147640825624179961)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 147640825624179961 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((27017 : ℕ)^1 * ((5059942561 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 147640825624179961)^73820412812089980 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 147640825624179961)^49213608541393320 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 147640825624179961)^29528165124835992 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 27017 := Nat.prime_eq_prime_of_dvd_pow hq prime_27017 hd
            subst q
            change (7 : ZMod 147640825624179961)^5464737965880 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 5059942561 := Nat.prime_eq_prime_of_dvd_pow hq prime_5059942561 hd
            subst q
            change (7 : ZMod 147640825624179961)^29178360 ≠ 1
            reduce_mod_char
            decide

theorem prime_148863517207035947 : Nat.Prime 148863517207035947 := by
  apply lucas_primality 148863517207035947 (2 : ZMod 148863517207035947)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 148863517207035947 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((71 : ℕ)^1 * ((653899 : ℕ)^1 * ((229029391 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 148863517207035947)^74431758603517973 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 148863517207035947)^21266216743862278 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
          subst q
          change (2 : ZMod 148863517207035947)^2096669256437126 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 653899 := Nat.prime_eq_prime_of_dvd_pow hq prime_653899 hd
            subst q
            change (2 : ZMod 148863517207035947)^227655214654 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 229029391 := Nat.prime_eq_prime_of_dvd_pow hq prime_229029391 hd
            subst q
            change (2 : ZMod 148863517207035947)^649975606 ≠ 1
            reduce_mod_char
            decide

theorem prime_150094635296999123 : Nat.Prime 150094635296999123 := by
  apply lucas_primality 150094635296999123 (2 : ZMod 150094635296999123)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 150094635296999123 - 1 = (2 : ℕ)^1 * ((41 : ℕ)^1 * ((6481 : ℕ)^1 * ((282429005041 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 150094635296999123)^75047317648499561 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
        subst q
        change (2 : ZMod 150094635296999123)^3660844763341442 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 6481 := Nat.prime_eq_prime_of_dvd_pow hq prime_6481 hd
          subst q
          change (2 : ZMod 150094635296999123)^23159178413362 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 282429005041 := Nat.prime_eq_prime_of_dvd_pow hq prime_282429005041 hd
          subst q
          change (2 : ZMod 150094635296999123)^531442 ≠ 1
          reduce_mod_char
          decide

theorem prime_151334226289000009 : Nat.Prime 151334226289000009 := by
  apply lucas_primality 151334226289000009 (7 : ZMod 151334226289000009)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 151334226289000009 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((88817 : ℕ)^1 * ((23665112017 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 151334226289000009)^75667113144500004 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 151334226289000009)^50444742096333336 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 88817 := Nat.prime_eq_prime_of_dvd_pow hq prime_88817 hd
          subst q
          change (7 : ZMod 151334226289000009)^1703888065224 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 23665112017 := Nat.prime_eq_prime_of_dvd_pow hq prime_23665112017 hd
          subst q
          change (7 : ZMod 151334226289000009)^6394824 ≠ 1
          reduce_mod_char
          decide

theorem prime_152582336769287903 : Nat.Prime 152582336769287903 := by
  apply lucas_primality 152582336769287903 (5 : ZMod 152582336769287903)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 152582336769287903 - 1 = (2 : ℕ)^1 * ((41 : ℕ)^1 * ((457 : ℕ)^1 * ((1987 : ℕ)^1 * ((2049162229 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 152582336769287903)^76291168384643951 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
        subst q
        change (5 : ZMod 152582336769287903)^3721520409007022 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 457 := Nat.prime_eq_prime_of_dvd_pow hq prime_457 hd
          subst q
          change (5 : ZMod 152582336769287903)^333878198619886 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1987 := Nat.prime_eq_prime_of_dvd_pow hq prime_1987 hd
            subst q
            change (5 : ZMod 152582336769287903)^76790305369546 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2049162229 := Nat.prime_eq_prime_of_dvd_pow hq prime_2049162229 hd
            subst q
            change (5 : ZMod 152582336769287903)^74460838 ≠ 1
            reduce_mod_char
            decide

theorem prime_153839013515956283 : Nat.Prime 153839013515956283 := by
  apply lucas_primality 153839013515956283 (2 : ZMod 153839013515956283)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 153839013515956283 - 1 = (2 : ℕ)^1 * ((76919506757978141 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 153839013515956283)^76919506757978141 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 76919506757978141 := Nat.prime_eq_prime_of_dvd_pow hq prime_76919506757978141 hd
      subst q
      change (2 : ZMod 153839013515956283)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_155104303499468621 : Nat.Prime 155104303499468621 := by
  apply lucas_primality 155104303499468621 (2 : ZMod 155104303499468621)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 155104303499468621 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((705019561361221 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 155104303499468621)^77552151749734310 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 155104303499468621)^31020860699893724 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 155104303499468621)^14100391227224420 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 705019561361221 := Nat.prime_eq_prime_of_dvd_pow hq prime_705019561361221 hd
          subst q
          change (2 : ZMod 155104303499468621)^220 ≠ 1
          reduce_mod_char
          decide

theorem prime_156378253883185223 : Nat.Prime 156378253883185223 := by
  apply lucas_primality 156378253883185223 (5 : ZMod 156378253883185223)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 156378253883185223 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((1277 : ℕ)^1 * ((437959 : ℕ)^1 * ((19972111 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 156378253883185223)^78189126941592611 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 156378253883185223)^22339750554740746 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1277 := Nat.prime_eq_prime_of_dvd_pow hq prime_1277 hd
          subst q
          change (5 : ZMod 156378253883185223)^122457520660286 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 437959 := Nat.prime_eq_prime_of_dvd_pow hq prime_437959 hd
            subst q
            change (5 : ZMod 156378253883185223)^357061400458 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 19972111 := Nat.prime_eq_prime_of_dvd_pow hq prime_19972111 hd
            subst q
            change (5 : ZMod 156378253883185223)^7829831002 ≠ 1
            reduce_mod_char
            decide

theorem prime_157660912023890641 : Nat.Prime 157660912023890641 := by
  apply lucas_primality 157660912023890641 (23 : ZMod 157660912023890641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 157660912023890641 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((137 : ℕ)^1 * ((4795039903403 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (23 : ZMod 157660912023890641)^78830456011945320 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (23 : ZMod 157660912023890641)^52553637341296880 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (23 : ZMod 157660912023890641)^31532182404778128 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
            subst q
            change (23 : ZMod 157660912023890641)^1150809576816720 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 4795039903403 := Nat.prime_eq_prime_of_dvd_pow hq prime_4795039903403 hd
            subst q
            change (23 : ZMod 157660912023890641)^32880 ≠ 1
            reduce_mod_char
            decide

theorem prime_158412606539792551 : Nat.Prime 158412606539792551 := by
  apply lucas_primality 158412606539792551 (6 : ZMod 158412606539792551)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 158412606539792551 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((11 : ℕ)^1 * ((29 : ℕ)^1 * ((151 : ℕ)^1 * ((307 : ℕ)^1 * ((4957 : ℕ)^1 * ((14407 : ℕ)^1)))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 158412606539792551)^79206303269896275 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 158412606539792551)^52804202179930850 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 158412606539792551)^31682521307958510 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (6 : ZMod 158412606539792551)^14401146049072050 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
              subst q
              change (6 : ZMod 158412606539792551)^5462503673785950 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
                subst q
                change (6 : ZMod 158412606539792551)^1049090109535050 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 307 := Nat.prime_eq_prime_of_dvd_pow hq prime_307 hd
                  subst q
                  change (6 : ZMod 158412606539792551)^516001975699650 ≠ 1
                  reduce_mod_char
                  decide
                · rcases hq.dvd_mul.mp hd with hd | hd
                  · have heq : q = 4957 := Nat.prime_eq_prime_of_dvd_pow hq prime_4957 hd
                    subst q
                    change (6 : ZMod 158412606539792551)^31957354557150 ≠ 1
                    reduce_mod_char
                    decide
                  · have heq : q = 14407 := Nat.prime_eq_prime_of_dvd_pow hq prime_14407 hd
                    subst q
                    change (6 : ZMod 158412606539792551)^10995530404650 ≠ 1
                    reduce_mod_char
                    decide

theorem prime_158952325472321539 : Nat.Prime 158952325472321539 := by
  apply lucas_primality 158952325472321539 (2 : ZMod 158952325472321539)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 158952325472321539 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((26492054245386923 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 158952325472321539)^79476162736160769 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 158952325472321539)^52984108490773846 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 26492054245386923 := Nat.prime_eq_prime_of_dvd_pow hq prime_26492054245386923 hd
        subst q
        change (2 : ZMod 158952325472321539)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_160252541973695827 : Nat.Prime 160252541973695827 := by
  apply lucas_primality 160252541973695827 (2 : ZMod 160252541973695827)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 160252541973695827 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((701 : ℕ)^1 * ((41513 : ℕ)^1 * ((305935789 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 160252541973695827)^80126270986847913 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 160252541973695827)^53417513991231942 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 701 := Nat.prime_eq_prime_of_dvd_pow hq prime_701 hd
          subst q
          change (2 : ZMod 160252541973695827)^228605623357626 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 41513 := Nat.prime_eq_prime_of_dvd_pow hq prime_41513 hd
            subst q
            change (2 : ZMod 160252541973695827)^3860297785602 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 305935789 := Nat.prime_eq_prime_of_dvd_pow hq prime_305935789 hd
            subst q
            change (2 : ZMod 160252541973695827)^523811034 ≠ 1
            reduce_mod_char
            decide

theorem prime_161561609468242033 : Nat.Prime 161561609468242033 := by
  apply lucas_primality 161561609468242033 (17 : ZMod 161561609468242033)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 161561609468242033 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((3511 : ℕ)^1 * ((136951900717 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 161561609468242033)^80780804734121016 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 161561609468242033)^53853869822747344 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (17 : ZMod 161561609468242033)^23080229924034576 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3511 := Nat.prime_eq_prime_of_dvd_pow hq prime_3511 hd
            subst q
            change (17 : ZMod 161561609468242033)^46015838640912 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 136951900717 := Nat.prime_eq_prime_of_dvd_pow hq prime_136951900717 hd
            subst q
            change (17 : ZMod 161561609468242033)^1179696 ≠ 1
            reduce_mod_char
            decide

theorem prime_162879576091729589 : Nat.Prime 162879576091729589 := by
  apply lucas_primality 162879576091729589 (2 : ZMod 162879576091729589)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 162879576091729589 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((43 : ℕ)^1 * ((97 : ℕ)^1 * ((139 : ℕ)^1 * ((5653 : ℕ)^1 * ((136531 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 162879576091729589)^81439788045864794 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 162879576091729589)^23268510870247084 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 162879576091729589)^12529198160902276 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (2 : ZMod 162879576091729589)^3787897118412316 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
              subst q
              change (2 : ZMod 162879576091729589)^1679170887543604 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
                subst q
                change (2 : ZMod 162879576091729589)^1171795511451292 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 5653 := Nat.prime_eq_prime_of_dvd_pow hq prime_5653 hd
                  subst q
                  change (2 : ZMod 162879576091729589)^28812944647396 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 136531 := Nat.prime_eq_prime_of_dvd_pow hq prime_136531 hd
                  subst q
                  change (2 : ZMod 162879576091729589)^1192986033148 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_164206490176000031 : Nat.Prime 164206490176000031 := by
  apply lucas_primality 164206490176000031 (7 : ZMod 164206490176000031)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 164206490176000031 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((461 : ℕ)^1 * ((190479300029 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 164206490176000031)^82103245088000015 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 164206490176000031)^32841298035200006 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (7 : ZMod 164206490176000031)^14927862743272730 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (7 : ZMod 164206490176000031)^9659205304470590 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 461 := Nat.prime_eq_prime_of_dvd_pow hq prime_461 hd
              subst q
              change (7 : ZMod 164206490176000031)^356196291054230 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 190479300029 := Nat.prime_eq_prime_of_dvd_pow hq prime_190479300029 hd
              subst q
              change (7 : ZMod 164206490176000031)^862070 ≠ 1
              reduce_mod_char
              decide

theorem prime_165542400249498527 : Nat.Prime 165542400249498527 := by
  apply lucas_primality 165542400249498527 (5 : ZMod 165542400249498527)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 165542400249498527 - 1 = (2 : ℕ)^1 * ((2903 : ℕ)^1 * ((1127101 : ℕ)^1 * ((25297021 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 165542400249498527)^82771200124749263 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 2903 := Nat.prime_eq_prime_of_dvd_pow hq prime_2903 hd
        subst q
        change (5 : ZMod 165542400249498527)^57024595332242 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1127101 := Nat.prime_eq_prime_of_dvd_pow hq prime_1127101 hd
          subst q
          change (5 : ZMod 165542400249498527)^146874503926 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 25297021 := Nat.prime_eq_prime_of_dvd_pow hq prime_25297021 hd
          subst q
          change (5 : ZMod 165542400249498527)^6543948406 ≠ 1
          reduce_mod_char
          decide

theorem prime_166887355037806199 : Nat.Prime 166887355037806199 := by
  apply lucas_primality 166887355037806199 (11 : ZMod 166887355037806199)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 166887355037806199 - 1 = (2 : ℕ)^1 * ((83443677518903099 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 166887355037806199)^83443677518903099 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 83443677518903099 := Nat.prime_eq_prime_of_dvd_pow hq prime_83443677518903099 hd
      subst q
      change (11 : ZMod 166887355037806199)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_168241403464173709 : Nat.Prime 168241403464173709 := by
  apply lucas_primality 168241403464173709 (2 : ZMod 168241403464173709)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 168241403464173709 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((75539 : ℕ)^1 * ((185601039931 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 168241403464173709)^84120701732086854 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 168241403464173709)^56080467821391236 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 75539 := Nat.prime_eq_prime_of_dvd_pow hq prime_75539 hd
          subst q
          change (2 : ZMod 168241403464173709)^2227212479172 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 185601039931 := Nat.prime_eq_prime_of_dvd_pow hq prime_185601039931 hd
          subst q
          change (2 : ZMod 168241403464173709)^906468 ≠ 1
          reduce_mod_char
          decide

theorem prime_169604594650054799 : Nat.Prime 169604594650054799 := by
  apply lucas_primality 169604594650054799 (7 : ZMod 169604594650054799)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 169604594650054799 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((8831 : ℕ)^1 * ((738676666333 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 169604594650054799)^84802297325027399 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (7 : ZMod 169604594650054799)^13046507280773446 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 8831 := Nat.prime_eq_prime_of_dvd_pow hq prime_8831 hd
          subst q
          change (7 : ZMod 169604594650054799)^19205593324658 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 738676666333 := Nat.prime_eq_prime_of_dvd_pow hq prime_738676666333 hd
          subst q
          change (7 : ZMod 169604594650054799)^229606 ≠ 1
          reduce_mod_char
          decide

theorem prime_170976977915640641 : Nat.Prime 170976977915640641 := by
  apply lucas_primality 170976977915640641 (3 : ZMod 170976977915640641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 170976977915640641 - 1 = (2 : ℕ)^6 * ((5 : ℕ)^1 * ((47807 : ℕ)^1 * ((11176251511 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 170976977915640641)^85488488957820320 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 170976977915640641)^34195395583128128 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47807 := Nat.prime_eq_prime_of_dvd_pow hq prime_47807 hd
          subst q
          change (3 : ZMod 170976977915640641)^3576400483520 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11176251511 := Nat.prime_eq_prime_of_dvd_pow hq prime_11176251511 hd
          subst q
          change (3 : ZMod 170976977915640641)^15298240 ≠ 1
          reduce_mod_char
          decide

theorem prime_172358602780396121 : Nat.Prime 172358602780396121 := by
  apply lucas_primality 172358602780396121 (3 : ZMod 172358602780396121)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 172358602780396121 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((193 : ℕ)^1 * ((2029658534861 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 172358602780396121)^86179301390198060 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 172358602780396121)^34471720556079224 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 172358602780396121)^15668963889126920 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
            subst q
            change (3 : ZMod 172358602780396121)^893049755338840 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2029658534861 := Nat.prime_eq_prime_of_dvd_pow hq prime_2029658534861 hd
            subst q
            change (3 : ZMod 172358602780396121)^84920 ≠ 1
            reduce_mod_char
            decide

theorem prime_173749518963594731 : Nat.Prime 173749518963594731 := by
  apply lucas_primality 173749518963594731 (2 : ZMod 173749518963594731)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 173749518963594731 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((41 : ℕ)^1 * ((1361 : ℕ)^1 * ((23951806621 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 173749518963594731)^86874759481797365 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 173749518963594731)^34749903792718946 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 173749518963594731)^13365347612584210 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (2 : ZMod 173749518963594731)^4237793145453530 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1361 := Nat.prime_eq_prime_of_dvd_pow hq prime_1361 hd
              subst q
              change (2 : ZMod 173749518963594731)^127663129289930 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 23951806621 := Nat.prime_eq_prime_of_dvd_pow hq prime_23951806621 hd
              subst q
              change (2 : ZMod 173749518963594731)^7254130 ≠ 1
              reduce_mod_char
              decide

theorem prime_175149776384856089 : Nat.Prime 175149776384856089 := by
  apply lucas_primality 175149776384856089 (3 : ZMod 175149776384856089)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 175149776384856089 - 1 = (2 : ℕ)^3 * ((273291947 : ℕ)^1 * ((80111113 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 175149776384856089)^87574888192428044 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 273291947 := Nat.prime_eq_prime_of_dvd_pow hq prime_273291947 hd
        subst q
        change (3 : ZMod 175149776384856089)^640888904 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 80111113 := Nat.prime_eq_prime_of_dvd_pow hq prime_80111113 hd
        subst q
        change (3 : ZMod 175149776384856089)^2186335576 ≠ 1
        reduce_mod_char
        decide

theorem prime_176559425164683049 : Nat.Prime 176559425164683049 := by
  apply lucas_primality 176559425164683049 (7 : ZMod 176559425164683049)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 176559425164683049 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((140683 : ℕ)^1 * ((52292336069 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 176559425164683049)^88279712582341524 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 176559425164683049)^58853141721561016 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 140683 := Nat.prime_eq_prime_of_dvd_pow hq prime_140683 hd
          subst q
          change (7 : ZMod 176559425164683049)^1255016065656 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 52292336069 := Nat.prime_eq_prime_of_dvd_pow hq prime_52292336069 hd
          subst q
          change (7 : ZMod 176559425164683049)^3376392 ≠ 1
          reduce_mod_char
          decide

theorem prime_177978515625000023 : Nat.Prime 177978515625000023 := by
  apply lucas_primality 177978515625000023 (5 : ZMod 177978515625000023)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 177978515625000023 - 1 = (2 : ℕ)^1 * ((29 : ℕ)^1 * ((14867 : ℕ)^1 * ((206403114077 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 177978515625000023)^88989257812500011 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (5 : ZMod 177978515625000023)^6137190193965518 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 14867 := Nat.prime_eq_prime_of_dvd_pow hq prime_14867 hd
          subst q
          change (5 : ZMod 177978515625000023)^11971380616466 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 206403114077 := Nat.prime_eq_prime_of_dvd_pow hq prime_206403114077 hd
          subst q
          change (5 : ZMod 177978515625000023)^862286 ≠ 1
          reduce_mod_char
          decide

theorem prime_179407098289692089 : Nat.Prime 179407098289692089 := by
  apply lucas_primality 179407098289692089 (3 : ZMod 179407098289692089)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 179407098289692089 - 1 = (2 : ℕ)^3 * ((17 : ℕ)^1 * ((1319169840365383 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 179407098289692089)^89703549144846044 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (3 : ZMod 179407098289692089)^10553358722923064 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1319169840365383 := Nat.prime_eq_prime_of_dvd_pow hq prime_1319169840365383 hd
        subst q
        change (3 : ZMod 179407098289692089)^136 ≠ 1
        reduce_mod_char
        decide

theorem prime_179499509787667973 : Nat.Prime 179499509787667973 := by
  apply lucas_primality 179499509787667973 (2 : ZMod 179499509787667973)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 179499509787667973 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((4591 : ℕ)^1 * ((13873 : ℕ)^1 * ((100653193 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 179499509787667973)^89749754893833986 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 179499509787667973)^25642787112523996 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 4591 := Nat.prime_eq_prime_of_dvd_pow hq prime_4591 hd
          subst q
          change (2 : ZMod 179499509787667973)^39098128901692 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13873 := Nat.prime_eq_prime_of_dvd_pow hq prime_13873 hd
            subst q
            change (2 : ZMod 179499509787667973)^12938766653764 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 100653193 := Nat.prime_eq_prime_of_dvd_pow hq prime_100653193 hd
            subst q
            change (2 : ZMod 179499509787667973)^1783346404 ≠ 1
            reduce_mod_char
            decide

theorem prime_180845223885144079 : Nat.Prime 180845223885144079 := by
  apply lucas_primality 180845223885144079 (3 : ZMod 180845223885144079)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 180845223885144079 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((2990513 : ℕ)^1 * ((775294577 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 180845223885144079)^90422611942572039 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 180845223885144079)^60281741295048026 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 180845223885144079)^13911171068088006 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2990513 := Nat.prime_eq_prime_of_dvd_pow hq prime_2990513 hd
            subst q
            change (3 : ZMod 180845223885144079)^60472977006 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 775294577 := Nat.prime_eq_prime_of_dvd_pow hq prime_775294577 hd
            subst q
            change (3 : ZMod 180845223885144079)^233260014 ≠ 1
            reduce_mod_char
            decide

theorem prime_182292943340781733 : Nat.Prime 182292943340781733 := by
  apply lucas_primality 182292943340781733 (5 : ZMod 182292943340781733)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 182292943340781733 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((15191078611731811 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 182292943340781733)^91146471670390866 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 182292943340781733)^60764314446927244 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 15191078611731811 := Nat.prime_eq_prime_of_dvd_pow hq prime_15191078611731811 hd
        subst q
        change (5 : ZMod 182292943340781733)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_183750307789612129 : Nat.Prime 183750307789612129 := by
  apply lucas_primality 183750307789612129 (7 : ZMod 183750307789612129)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 183750307789612129 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((433 : ℕ)^1 * ((3259 : ℕ)^1 * ((1356390019 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 183750307789612129)^91875153894806064 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 183750307789612129)^61250102596537376 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 433 := Nat.prime_eq_prime_of_dvd_pow hq prime_433 hd
          subst q
          change (7 : ZMod 183750307789612129)^424365606904416 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3259 := Nat.prime_eq_prime_of_dvd_pow hq prime_3259 hd
            subst q
            change (7 : ZMod 183750307789612129)^56382420309792 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1356390019 := Nat.prime_eq_prime_of_dvd_pow hq prime_1356390019 hd
            subst q
            change (7 : ZMod 183750307789612129)^135470112 ≠ 1
            reduce_mod_char
            decide

theorem prime_185217368568765641 : Nat.Prime 185217368568765641 := by
  apply lucas_primality 185217368568765641 (6 : ZMod 185217368568765641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 185217368568765641 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((4630434214219141 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 185217368568765641)^92608684284382820 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 185217368568765641)^37043473713753128 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4630434214219141 := Nat.prime_eq_prime_of_dvd_pow hq prime_4630434214219141 hd
        subst q
        change (6 : ZMod 185217368568765641)^40 ≠ 1
        reduce_mod_char
        decide

theorem prime_186694177220038687 : Nat.Prime 186694177220038687 := by
  apply lucas_primality 186694177220038687 (3 : ZMod 186694177220038687)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 186694177220038687 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((23 : ℕ)^1 * ((5449 : ℕ)^1 * ((16231 : ℕ)^1 * ((81799 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 186694177220038687)^93347088610019343 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 186694177220038687)^62231392406679562 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 186694177220038687)^16972197929094426 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (3 : ZMod 186694177220038687)^10982010424708158 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
              subst q
              change (3 : ZMod 186694177220038687)^8117138140001682 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 5449 := Nat.prime_eq_prime_of_dvd_pow hq prime_5449 hd
                subst q
                change (3 : ZMod 186694177220038687)^34262098957614 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 16231 := Nat.prime_eq_prime_of_dvd_pow hq prime_16231 hd
                  subst q
                  change (3 : ZMod 186694177220038687)^11502321312306 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 81799 := Nat.prime_eq_prime_of_dvd_pow hq prime_81799 hd
                  subst q
                  change (3 : ZMod 186694177220038687)^2282352806514 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_188180785490436707 : Nat.Prime 188180785490436707 := by
  apply lucas_primality 188180785490436707 (5 : ZMod 188180785490436707)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 188180785490436707 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((89 : ℕ)^1 * ((331 : ℕ)^1 * ((290358534497 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 188180785490436707)^94090392745218353 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 188180785490436707)^17107344135494246 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (5 : ZMod 188180785490436707)^2114390848207154 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 331 := Nat.prime_eq_prime_of_dvd_pow hq prime_331 hd
            subst q
            change (5 : ZMod 188180785490436707)^568522010545126 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 290358534497 := Nat.prime_eq_prime_of_dvd_pow hq prime_290358534497 hd
            subst q
            change (5 : ZMod 188180785490436707)^648098 ≠ 1
            reduce_mod_char
            decide

theorem prime_189677245332718177 : Nat.Prime 189677245332718177 := by
  apply lucas_primality 189677245332718177 (5 : ZMod 189677245332718177)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 189677245332718177 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((283 : ℕ)^1 * ((761 : ℕ)^1 * ((834027217 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 189677245332718177)^94838622666359088 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 189677245332718177)^63225748444239392 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 189677245332718177)^17243385939338016 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 283 := Nat.prime_eq_prime_of_dvd_pow hq prime_283 hd
            subst q
            change (5 : ZMod 189677245332718177)^670237616016672 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 761 := Nat.prime_eq_prime_of_dvd_pow hq prime_761 hd
              subst q
              change (5 : ZMod 189677245332718177)^249247365746016 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 834027217 := Nat.prime_eq_prime_of_dvd_pow hq prime_834027217 hd
              subst q
              change (5 : ZMod 189677245332718177)^227423328 ≠ 1
              reduce_mod_char
              decide

theorem prime_191183608905939451 : Nat.Prime 191183608905939451 := by
  apply lucas_primality 191183608905939451 (3 : ZMod 191183608905939451)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 191183608905939451 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^2 * ((17 : ℕ)^1 * ((53 : ℕ)^1 * ((577 : ℕ)^1 * ((817217273 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 191183608905939451)^95591804452969725 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 191183608905939451)^63727869635313150 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 191183608905939451)^38236721781187890 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (3 : ZMod 191183608905939451)^11246094641525850 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
              subst q
              change (3 : ZMod 191183608905939451)^3607237903885650 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 577 := Nat.prime_eq_prime_of_dvd_pow hq prime_577 hd
                subst q
                change (3 : ZMod 191183608905939451)^331340743337850 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 817217273 := Nat.prime_eq_prime_of_dvd_pow hq prime_817217273 hd
                subst q
                change (3 : ZMod 191183608905939451)^233944650 ≠ 1
                reduce_mod_char
                decide

theorem prime_192699928576000031 : Nat.Prime 192699928576000031 := by
  apply lucas_primality 192699928576000031 (7 : ZMod 192699928576000031)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 192699928576000031 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((353 : ℕ)^1 * ((54589214894051 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 192699928576000031)^96349964288000015 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 192699928576000031)^38539985715200006 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 353 := Nat.prime_eq_prime_of_dvd_pow hq prime_353 hd
          subst q
          change (7 : ZMod 192699928576000031)^545892148940510 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 54589214894051 := Nat.prime_eq_prime_of_dvd_pow hq prime_54589214894051 hd
          subst q
          change (7 : ZMod 192699928576000031)^3530 ≠ 1
          reduce_mod_char
          decide

theorem prime_194226256916188573 : Nat.Prime 194226256916188573 := by
  apply lucas_primality 194226256916188573 (2 : ZMod 194226256916188573)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 194226256916188573 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((16185521409682381 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 194226256916188573)^97113128458094286 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 194226256916188573)^64742085638729524 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 16185521409682381 := Nat.prime_eq_prime_of_dvd_pow hq prime_16185521409682381 hd
        subst q
        change (2 : ZMod 194226256916188573)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_195762646707730021 : Nat.Prime 195762646707730021 := by
  apply lucas_primality 195762646707730021 (7 : ZMod 195762646707730021)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 195762646707730021 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((287117 : ℕ)^1 * ((222817601 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 195762646707730021)^97881323353865010 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 195762646707730021)^65254215569243340 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 195762646707730021)^39152529341546004 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (7 : ZMod 195762646707730021)^11515449806337060 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 287117 := Nat.prime_eq_prime_of_dvd_pow hq prime_287117 hd
              subst q
              change (7 : ZMod 195762646707730021)^681821859060 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 222817601 := Nat.prime_eq_prime_of_dvd_pow hq prime_222817601 hd
              subst q
              change (7 : ZMod 195762646707730021)^878578020 ≠ 1
              reduce_mod_char
              decide

theorem prime_197309150940332923 : Nat.Prime 197309150940332923 := by
  apply lucas_primality 197309150940332923 (3 : ZMod 197309150940332923)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 197309150940332923 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((71 : ℕ)^1 * ((3929 : ℕ)^1 * ((5125399991 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 197309150940332923)^98654575470166461 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 197309150940332923)^65769716980110974 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (3 : ZMod 197309150940332923)^8578658736536214 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
            subst q
            change (3 : ZMod 197309150940332923)^2779002125920182 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 3929 := Nat.prime_eq_prime_of_dvd_pow hq prime_3929 hd
              subst q
              change (3 : ZMod 197309150940332923)^50218669111818 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 5125399991 := Nat.prime_eq_prime_of_dvd_pow hq prime_5125399991 hd
              subst q
              change (3 : ZMod 197309150940332923)^38496342 ≠ 1
              reduce_mod_char
              decide

theorem prime_198865822812737567 : Nat.Prime 198865822812737567 := by
  apply lucas_primality 198865822812737567 (5 : ZMod 198865822812737567)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 198865822812737567 - 1 = (2 : ℕ)^1 * ((269 : ℕ)^1 * ((659 : ℕ)^1 * ((560909068073 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 198865822812737567)^99432911406368783 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
        subst q
        change (5 : ZMod 198865822812737567)^739278151720214 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 659 := Nat.prime_eq_prime_of_dvd_pow hq prime_659 hd
          subst q
          change (5 : ZMod 198865822812737567)^301769078623274 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 560909068073 := Nat.prime_eq_prime_of_dvd_pow hq prime_560909068073 hd
          subst q
          change (5 : ZMod 198865822812737567)^354542 ≠ 1
          reduce_mod_char
          decide

theorem prime_200432715733265647 : Nat.Prime 200432715733265647 := by
  apply lucas_primality 200432715733265647 (3 : ZMod 200432715733265647)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 200432715733265647 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((158014867 : ℕ)^1 * ((211407023 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 200432715733265647)^100216357866632823 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 200432715733265647)^66810905244421882 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 158014867 := Nat.prime_eq_prime_of_dvd_pow hq prime_158014867 hd
          subst q
          change (3 : ZMod 200432715733265647)^1268442138 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 211407023 := Nat.prime_eq_prime_of_dvd_pow hq prime_211407023 hd
          subst q
          change (3 : ZMod 200432715733265647)^948089202 ≠ 1
          reduce_mod_char
          decide

theorem prime_202009883320369231 : Nat.Prime 202009883320369231 := by
  apply lucas_primality 202009883320369231 (3 : ZMod 202009883320369231)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 202009883320369231 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((6733662777345641 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 202009883320369231)^101004941660184615 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 202009883320369231)^67336627773456410 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 202009883320369231)^40401976664073846 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 6733662777345641 := Nat.prime_eq_prime_of_dvd_pow hq prime_6733662777345641 hd
          subst q
          change (3 : ZMod 202009883320369231)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_203597379403181669 : Nat.Prime 203597379403181669 := by
  apply lucas_primality 203597379403181669 (2 : ZMod 203597379403181669)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 203597379403181669 - 1 = (2 : ℕ)^2 * ((157 : ℕ)^1 * ((324199648731181 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 203597379403181669)^101798689701590834 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
        subst q
        change (2 : ZMod 203597379403181669)^1296798594924724 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 324199648731181 := Nat.prime_eq_prime_of_dvd_pow hq prime_324199648731181 hd
        subst q
        change (2 : ZMod 203597379403181669)^628 ≠ 1
        reduce_mod_char
        decide

theorem prime_205195258022068253 : Nat.Prime 205195258022068253 := by
  apply lucas_primality 205195258022068253 (2 : ZMod 205195258022068253)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 205195258022068253 - 1 = (2 : ℕ)^2 * ((1111559 : ℕ)^1 * ((46150329857 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 205195258022068253)^102597629011034126 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1111559 := Nat.prime_eq_prime_of_dvd_pow hq prime_1111559 hd
        subst q
        change (2 : ZMod 205195258022068253)^184601319428 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 46150329857 := Nat.prime_eq_prime_of_dvd_pow hq prime_46150329857 hd
        subst q
        change (2 : ZMod 205195258022068253)^4446236 ≠ 1
        reduce_mod_char
        decide

theorem prime_206803573429178903 : Nat.Prime 206803573429178903 := by
  apply lucas_primality 206803573429178903 (5 : ZMod 206803573429178903)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 206803573429178903 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^2 * ((283 : ℕ)^1 * ((1499 : ℕ)^1 * ((2014441243 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 206803573429178903)^103401786714589451 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 206803573429178903)^18800324857198082 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 283 := Nat.prime_eq_prime_of_dvd_pow hq prime_283 hd
          subst q
          change (5 : ZMod 206803573429178903)^730754676428194 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1499 := Nat.prime_eq_prime_of_dvd_pow hq prime_1499 hd
            subst q
            change (5 : ZMod 206803573429178903)^137961022968098 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2014441243 := Nat.prime_eq_prime_of_dvd_pow hq prime_2014441243 hd
            subst q
            change (5 : ZMod 206803573429178903)^102660514 ≠ 1
            reduce_mod_char
            decide

theorem prime_208422380089000043 : Nat.Prime 208422380089000043 := by
  apply lucas_primality 208422380089000043 (5 : ZMod 208422380089000043)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 208422380089000043 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((41 : ℕ)^1 * ((389 : ℕ)^1 * ((933432369647 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 208422380089000043)^104211190044500021 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 208422380089000043)^29774625727000006 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (5 : ZMod 208422380089000043)^5083472685097562 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 389 := Nat.prime_eq_prime_of_dvd_pow hq prime_389 hd
            subst q
            change (5 : ZMod 208422380089000043)^535790180177378 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 933432369647 := Nat.prime_eq_prime_of_dvd_pow hq prime_933432369647 hd
            subst q
            change (5 : ZMod 208422380089000043)^223286 ≠ 1
            reduce_mod_char
            decide

theorem prime_210051732678908137 : Nat.Prime 210051732678908137 := by
  apply lucas_primality 210051732678908137 (5 : ZMod 210051732678908137)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 210051732678908137 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((541 : ℕ)^2 * ((1373 : ℕ)^1 * ((1489 : ℕ)^1 * ((14627 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 210051732678908137)^105025866339454068 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 210051732678908137)^70017244226302712 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 541 := Nat.prime_eq_prime_of_dvd_pow hq prime_541 hd
          subst q
          change (5 : ZMod 210051732678908137)^388265679628296 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1373 := Nat.prime_eq_prime_of_dvd_pow hq prime_1373 hd
            subst q
            change (5 : ZMod 210051732678908137)^152987423655432 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1489 := Nat.prime_eq_prime_of_dvd_pow hq prime_1489 hd
              subst q
              change (5 : ZMod 210051732678908137)^141068994411624 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 14627 := Nat.prime_eq_prime_of_dvd_pow hq prime_14627 hd
              subst q
              change (5 : ZMod 210051732678908137)^14360547800568 ≠ 1
              reduce_mod_char
              decide

theorem prime_211691686089723943 : Nat.Prime 211691686089723943 := by
  apply lucas_primality 211691686089723943 (3 : ZMod 211691686089723943)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 211691686089723943 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((307 : ℕ)^1 * ((114924911015051 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 211691686089723943)^105845843044861971 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 211691686089723943)^70563895363241314 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 307 := Nat.prime_eq_prime_of_dvd_pow hq prime_307 hd
          subst q
          change (3 : ZMod 211691686089723943)^689549466090306 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 114924911015051 := Nat.prime_eq_prime_of_dvd_pow hq prime_114924911015051 hd
          subst q
          change (3 : ZMod 211691686089723943)^1842 ≠ 1
          reduce_mod_char
          decide

theorem prime_213342295426266911 : Nat.Prime 213342295426266911 := by
  apply lucas_primality 213342295426266911 (7 : ZMod 213342295426266911)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 213342295426266911 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((9662407 : ℕ)^1 * ((2207962213 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 213342295426266911)^106671147713133455 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 213342295426266911)^42668459085253382 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 9662407 := Nat.prime_eq_prime_of_dvd_pow hq prime_9662407 hd
          subst q
          change (7 : ZMod 213342295426266911)^22079622130 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2207962213 := Nat.prime_eq_prime_of_dvd_pow hq prime_2207962213 hd
          subst q
          change (7 : ZMod 213342295426266911)^96624070 ≠ 1
          reduce_mod_char
          decide

theorem prime_215003616007911011 : Nat.Prime 215003616007911011 := by
  apply lucas_primality 215003616007911011 (2 : ZMod 215003616007911011)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 215003616007911011 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((2843 : ℕ)^2 * ((9257 : ℕ)^1 * ((41051 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 215003616007911011)^107501808003955505 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 215003616007911011)^43000723201582202 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 215003616007911011)^30714802286844430 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2843 := Nat.prime_eq_prime_of_dvd_pow hq prime_2843 hd
            subst q
            change (2 : ZMod 215003616007911011)^75625612384070 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 9257 := Nat.prime_eq_prime_of_dvd_pow hq prime_9257 hd
              subst q
              change (2 : ZMod 215003616007911011)^23226057686930 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 41051 := Nat.prime_eq_prime_of_dvd_pow hq prime_41051 hd
              subst q
              change (2 : ZMod 215003616007911011)^5237475725510 ≠ 1
              reduce_mod_char
              decide

theorem prime_216675703369140737 : Nat.Prime 216675703369140737 := by
  apply lucas_primality 216675703369140737 (3 : ZMod 216675703369140737)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 216675703369140737 - 1 = (2 : ℕ)^9 * ((7 : ℕ)^2 * ((23 : ℕ)^1 * ((59 : ℕ)^1 * ((6364500521 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 216675703369140737)^108337851684570368 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 216675703369140737)^30953671909877248 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (3 : ZMod 216675703369140737)^9420682755180032 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
            subst q
            change (3 : ZMod 216675703369140737)^3672469548629504 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 6364500521 := Nat.prime_eq_prime_of_dvd_pow hq prime_6364500521 hd
            subst q
            change (3 : ZMod 216675703369140737)^34044416 ≠ 1
            reduce_mod_char
            decide

theorem prime_218358613260107783 : Nat.Prime 218358613260107783 := by
  apply lucas_primality 218358613260107783 (5 : ZMod 218358613260107783)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 218358613260107783 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^2 * ((11 : ℕ)^1 * ((202559010445369 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 218358613260107783)^109179306630053891 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 218358613260107783)^31194087608586826 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 218358613260107783)^19850783023646162 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 202559010445369 := Nat.prime_eq_prime_of_dvd_pow hq prime_202559010445369 hd
          subst q
          change (5 : ZMod 218358613260107783)^1078 ≠ 1
          reduce_mod_char
          decide

theorem prime_220052401647189499 : Nat.Prime 220052401647189499 := by
  apply lucas_primality 220052401647189499 (2 : ZMod 220052401647189499)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 220052401647189499 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((8273 : ℕ)^1 * ((54881 : ℕ)^1 * ((26925797 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 220052401647189499)^110026200823594749 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 220052401647189499)^73350800549063166 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 8273 := Nat.prime_eq_prime_of_dvd_pow hq prime_8273 hd
          subst q
          change (2 : ZMod 220052401647189499)^26598863972826 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 54881 := Nat.prime_eq_prime_of_dvd_pow hq prime_54881 hd
            subst q
            change (2 : ZMod 220052401647189499)^4009628134458 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 26925797 := Nat.prime_eq_prime_of_dvd_pow hq prime_26925797 hd
            subst q
            change (2 : ZMod 220052401647189499)^8172549234 ≠ 1
            reduce_mod_char
            decide

theorem prime_221757124713546421 : Nat.Prime 221757124713546421 := by
  apply lucas_primality 221757124713546421 (2 : ZMod 221757124713546421)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 221757124713546421 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((563 : ℕ)^1 * ((729416238121 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 221757124713546421)^110878562356773210 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 221757124713546421)^73919041571182140 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 221757124713546421)^44351424942709284 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 563 := Nat.prime_eq_prime_of_dvd_pow hq prime_563 hd
            subst q
            change (2 : ZMod 221757124713546421)^393884768585340 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 729416238121 := Nat.prime_eq_prime_of_dvd_pow hq prime_729416238121 hd
            subst q
            change (2 : ZMod 221757124713546421)^304020 ≠ 1
            reduce_mod_char
            decide

theorem prime_223472838859681387 : Nat.Prime 223472838859681387 := by
  apply lucas_primality 223472838859681387 (2 : ZMod 223472838859681387)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 223472838859681387 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((59 : ℕ)^1 * ((197 : ℕ)^1 * ((3204462973697 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 223472838859681387)^111736419429840693 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 223472838859681387)^74490946286560462 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (2 : ZMod 223472838859681387)^3787675234909854 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
            subst q
            change (2 : ZMod 223472838859681387)^1134379892688738 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3204462973697 := Nat.prime_eq_prime_of_dvd_pow hq prime_3204462973697 hd
            subst q
            change (2 : ZMod 223472838859681387)^69738 ≠ 1
            reduce_mod_char
            decide

theorem prime_225199600704000017 : Nat.Prime 225199600704000017 := by
  apply lucas_primality 225199600704000017 (3 : ZMod 225199600704000017)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 225199600704000017 - 1 = (2 : ℕ)^4 * ((485101 : ℕ)^1 * ((29014524901 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 225199600704000017)^112599800352000008 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 485101 := Nat.prime_eq_prime_of_dvd_pow hq prime_485101 hd
        subst q
        change (3 : ZMod 225199600704000017)^464232398416 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 29014524901 := Nat.prime_eq_prime_of_dvd_pow hq prime_29014524901 hd
        subst q
        change (3 : ZMod 225199600704000017)^7761616 ≠ 1
        reduce_mod_char
        decide

theorem prime_226520601297633859 : Nat.Prime 226520601297633859 := by
  apply lucas_primality 226520601297633859 (2 : ZMod 226520601297633859)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 226520601297633859 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((19368257 : ℕ)^1 * ((102591721 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 226520601297633859)^113260300648816929 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 226520601297633859)^75506867099211286 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 226520601297633859)^11922136910401782 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19368257 := Nat.prime_eq_prime_of_dvd_pow hq prime_19368257 hd
            subst q
            change (2 : ZMod 226520601297633859)^11695456194 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 102591721 := Nat.prime_eq_prime_of_dvd_pow hq prime_102591721 hd
            subst q
            change (2 : ZMod 226520601297633859)^2207981298 ≠ 1
            reduce_mod_char
            decide

theorem prime_226937467083370721 : Nat.Prime 226937467083370721 := by
  apply lucas_primality 226937467083370721 (3 : ZMod 226937467083370721)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 226937467083370721 - 1 = (2 : ℕ)^5 * ((5 : ℕ)^1 * ((252001 : ℕ)^1 * ((5628387067 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 226937467083370721)^113468733541685360 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 226937467083370721)^45387493416674144 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 252001 := Nat.prime_eq_prime_of_dvd_pow hq prime_252001 hd
          subst q
          change (3 : ZMod 226937467083370721)^900541930720 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 5628387067 := Nat.prime_eq_prime_of_dvd_pow hq prime_5628387067 hd
          subst q
          change (3 : ZMod 226937467083370721)^40320160 ≠ 1
          reduce_mod_char
          decide

theorem prime_228327063707535157 : Nat.Prime 228327063707535157 := by
  apply lucas_primality 228327063707535157 (11 : ZMod 228327063707535157)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 228327063707535157 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((17 : ℕ)^1 * ((29 : ℕ)^1 * ((41 : ℕ)^1 * ((523 : ℕ)^1 * ((619 : ℕ)^1 * ((10651 : ℕ)^1))))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 228327063707535157)^114163531853767578 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 228327063707535157)^76109021235845052 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (11 : ZMod 228327063707535157)^32618151958219308 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (11 : ZMod 228327063707535157)^17563620285195012 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
              subst q
              change (11 : ZMod 228327063707535157)^13431003747502068 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
                subst q
                change (11 : ZMod 228327063707535157)^7873347024397764 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
                  subst q
                  change (11 : ZMod 228327063707535157)^5568952773354516 ≠ 1
                  reduce_mod_char
                  decide
                · rcases hq.dvd_mul.mp hd with hd | hd
                  · have heq : q = 523 := Nat.prime_eq_prime_of_dvd_pow hq prime_523 hd
                    subst q
                    change (11 : ZMod 228327063707535157)^436571823532572 ≠ 1
                    reduce_mod_char
                    decide
                  · rcases hq.dvd_mul.mp hd with hd | hd
                    · have heq : q = 619 := Nat.prime_eq_prime_of_dvd_pow hq prime_619 hd
                      subst q
                      change (11 : ZMod 228327063707535157)^368864400173724 ≠ 1
                      reduce_mod_char
                      decide
                    · have heq : q = 10651 := Nat.prime_eq_prime_of_dvd_pow hq prime_10651 hd
                      subst q
                      change (11 : ZMod 228327063707535157)^21437148033756 ≠ 1
                      reduce_mod_char
                      decide

theorem prime_228686495053685827 : Nat.Prime 228686495053685827 := by
  apply lucas_primality 228686495053685827 (2 : ZMod 228686495053685827)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 228686495053685827 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((953 : ℕ)^1 * ((21348323 : ℕ)^1 * ((1873409 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 228686495053685827)^114343247526842913 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 228686495053685827)^76228831684561942 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 953 := Nat.prime_eq_prime_of_dvd_pow hq prime_953 hd
          subst q
          change (2 : ZMod 228686495053685827)^239964842658642 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 21348323 := Nat.prime_eq_prime_of_dvd_pow hq prime_21348323 hd
            subst q
            change (2 : ZMod 228686495053685827)^10712152662 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1873409 := Nat.prime_eq_prime_of_dvd_pow hq prime_1873409 hd
            subst q
            change (2 : ZMod 228686495053685827)^122069710914 ≠ 1
            reduce_mod_char
            decide

theorem prime_230446741890423983 : Nat.Prime 230446741890423983 := by
  apply lucas_primality 230446741890423983 (5 : ZMod 230446741890423983)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 230446741890423983 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((19079 : ℕ)^1 * ((59119 : ℕ)^1 * ((1326683 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 230446741890423983)^115223370945211991 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 230446741890423983)^32920963127203426 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 230446741890423983)^20949703808220362 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19079 := Nat.prime_eq_prime_of_dvd_pow hq prime_19079 hd
            subst q
            change (5 : ZMod 230446741890423983)^12078554530658 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 59119 := Nat.prime_eq_prime_of_dvd_pow hq prime_59119 hd
              subst q
              change (5 : ZMod 230446741890423983)^3898014883378 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1326683 := Nat.prime_eq_prime_of_dvd_pow hq prime_1326683 hd
              subst q
              change (5 : ZMod 230446741890423983)^173701435754 ≠ 1
              reduce_mod_char
              decide

theorem prime_232218265089212477 : Nat.Prime 232218265089212477 := by
  apply lucas_primality 232218265089212477 (2 : ZMod 232218265089212477)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 232218265089212477 - 1 = (2 : ℕ)^2 * ((47 : ℕ)^1 * ((24435811 : ℕ)^1 * ((50548907 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 232218265089212477)^116109132544606238 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (2 : ZMod 232218265089212477)^4940814150834308 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 24435811 := Nat.prime_eq_prime_of_dvd_pow hq prime_24435811 hd
          subst q
          change (2 : ZMod 232218265089212477)^9503194516 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 50548907 := Nat.prime_eq_prime_of_dvd_pow hq prime_50548907 hd
          subst q
          change (2 : ZMod 232218265089212477)^4593932468 ≠ 1
          reduce_mod_char
          decide

theorem prime_234001122366390667 : Nat.Prime 234001122366390667 := by
  apply lucas_primality 234001122366390667 (2 : ZMod 234001122366390667)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 234001122366390667 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((241 : ℕ)^1 * ((23118071761153 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 234001122366390667)^117000561183195333 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 234001122366390667)^78000374122130222 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 234001122366390667)^33428731766627238 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 241 := Nat.prime_eq_prime_of_dvd_pow hq prime_241 hd
            subst q
            change (2 : ZMod 234001122366390667)^970959013968426 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 23118071761153 := Nat.prime_eq_prime_of_dvd_pow hq prime_23118071761153 hd
            subst q
            change (2 : ZMod 234001122366390667)^10122 ≠ 1
            reduce_mod_char
            decide

theorem prime_235795371659574367 : Nat.Prime 235795371659574367 := by
  apply lucas_primality 235795371659574367 (5 : ZMod 235795371659574367)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 235795371659574367 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((419 : ℕ)^1 * ((102643 : ℕ)^1 * ((913777933 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 235795371659574367)^117897685829787183 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 235795371659574367)^78598457219858122 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 419 := Nat.prime_eq_prime_of_dvd_pow hq prime_419 hd
          subst q
          change (5 : ZMod 235795371659574367)^562757450261514 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 102643 := Nat.prime_eq_prime_of_dvd_pow hq prime_102643 hd
            subst q
            change (5 : ZMod 235795371659574367)^2297237723562 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 913777933 := Nat.prime_eq_prime_of_dvd_pow hq prime_913777933 hd
            subst q
            change (5 : ZMod 235795371659574367)^258044502 ≠ 1
            reduce_mod_char
            decide

theorem prime_237601071128220467 : Nat.Prime 237601071128220467 := by
  apply lucas_primality 237601071128220467 (2 : ZMod 237601071128220467)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 237601071128220467 - 1 = (2 : ℕ)^1 * ((118800535564110233 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 237601071128220467)^118800535564110233 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 118800535564110233 := Nat.prime_eq_prime_of_dvd_pow hq prime_118800535564110233 hd
      subst q
      change (2 : ZMod 237601071128220467)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_239418279154192447 : Nat.Prime 239418279154192447 := by
  apply lucas_primality 239418279154192447 (3 : ZMod 239418279154192447)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 239418279154192447 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((113 : ℕ)^1 * ((5323 : ℕ)^1 * ((6991 : ℕ)^1 * ((13693 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 239418279154192447)^119709139577096223 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 239418279154192447)^79806093051397482 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 239418279154192447)^34202611307741778 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (3 : ZMod 239418279154192447)^21765298104926586 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
              subst q
              change (3 : ZMod 239418279154192447)^2118745833222942 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 5323 := Nat.prime_eq_prime_of_dvd_pow hq prime_5323 hd
                subst q
                change (3 : ZMod 239418279154192447)^44978072356602 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 6991 := Nat.prime_eq_prime_of_dvd_pow hq prime_6991 hd
                  subst q
                  change (3 : ZMod 239418279154192447)^34246642705506 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 13693 := Nat.prime_eq_prime_of_dvd_pow hq prime_13693 hd
                  subst q
                  change (3 : ZMod 239418279154192447)^17484720598422 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_241247054342326777 : Nat.Prime 241247054342326777 := by
  apply lucas_primality 241247054342326777 (7 : ZMod 241247054342326777)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 241247054342326777 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((402023 : ℕ)^1 * ((25003446563 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 241247054342326777)^120623527171163388 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 241247054342326777)^80415684780775592 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 402023 := Nat.prime_eq_prime_of_dvd_pow hq prime_402023 hd
          subst q
          change (7 : ZMod 241247054342326777)^600082717512 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 25003446563 := Nat.prime_eq_prime_of_dvd_pow hq prime_25003446563 hd
          subst q
          change (7 : ZMod 241247054342326777)^9648552 ≠ 1
          reduce_mod_char
          decide

theorem prime_243087455521000009 : Nat.Prime 243087455521000009 := by
  apply lucas_primality 243087455521000009 (7 : ZMod 243087455521000009)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 243087455521000009 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((41 : ℕ)^1 * ((43 : ℕ)^1 * ((59 : ℕ)^1 * ((32458296817 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 243087455521000009)^121543727760500004 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 243087455521000009)^81029151840333336 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (7 : ZMod 243087455521000009)^5928962329780488 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (7 : ZMod 243087455521000009)^5653196640023256 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
              subst q
              change (7 : ZMod 243087455521000009)^4120126364762712 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 32458296817 := Nat.prime_eq_prime_of_dvd_pow hq prime_32458296817 hd
              subst q
              change (7 : ZMod 243087455521000009)^7489224 ≠ 1
              reduce_mod_char
              decide

theorem prime_243507153127997309 : Nat.Prime 243507153127997309 := by
  apply lucas_primality 243507153127997309 (2 : ZMod 243507153127997309)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 243507153127997309 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((683 : ℕ)^1 * ((948053 : ℕ)^1 * ((8546843 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 243507153127997309)^121753576563998654 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 243507153127997309)^22137013920727028 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 683 := Nat.prime_eq_prime_of_dvd_pow hq prime_683 hd
          subst q
          change (2 : ZMod 243507153127997309)^356525846453876 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 948053 := Nat.prime_eq_prime_of_dvd_pow hq prime_948053 hd
            subst q
            change (2 : ZMod 243507153127997309)^256849725836 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 8546843 := Nat.prime_eq_prime_of_dvd_pow hq prime_8546843 hd
            subst q
            change (2 : ZMod 243507153127997309)^28490888756 ≠ 1
            reduce_mod_char
            decide

theorem prime_244939541742696323 : Nat.Prime 244939541742696323 := by
  apply lucas_primality 244939541742696323 (2 : ZMod 244939541742696323)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 244939541742696323 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((73 : ℕ)^1 * ((98686358478121 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 244939541742696323)^122469770871348161 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 244939541742696323)^14408208337805666 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
          subst q
          change (2 : ZMod 244939541742696323)^3355336188256114 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 98686358478121 := Nat.prime_eq_prime_of_dvd_pow hq prime_98686358478121 hd
          subst q
          change (2 : ZMod 244939541742696323)^2482 ≠ 1
          reduce_mod_char
          decide

theorem prime_245943453004004033 : Nat.Prime 245943453004004033 := by
  apply lucas_primality 245943453004004033 (3 : ZMod 245943453004004033)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 245943453004004033 - 1 = (2 : ℕ)^6 * ((3803 : ℕ)^1 * ((1010482895921 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 245943453004004033)^122971726502002016 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3803 := Nat.prime_eq_prime_of_dvd_pow hq prime_3803 hd
        subst q
        change (3 : ZMod 245943453004004033)^64670905338944 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1010482895921 := Nat.prime_eq_prime_of_dvd_pow hq prime_1010482895921 hd
        subst q
        change (3 : ZMod 245943453004004033)^243392 ≠ 1
        reduce_mod_char
        decide

theorem prime_246803372284575751 : Nat.Prime 246803372284575751 := by
  apply lucas_primality 246803372284575751 (12 : ZMod 246803372284575751)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 246803372284575751 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^3 * ((7 : ℕ)^3 * ((959391145907 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (12 : ZMod 246803372284575751)^123401686142287875 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (12 : ZMod 246803372284575751)^82267790761525250 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (12 : ZMod 246803372284575751)^49360674456915150 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (12 : ZMod 246803372284575751)^35257624612082250 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 959391145907 := Nat.prime_eq_prime_of_dvd_pow hq prime_959391145907 hd
            subst q
            change (12 : ZMod 246803372284575751)^257250 ≠ 1
            reduce_mod_char
            decide

theorem prime_248679006649044053 : Nat.Prime 248679006649044053 := by
  apply lucas_primality 248679006649044053 (2 : ZMod 248679006649044053)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 248679006649044053 - 1 = (2 : ℕ)^2 * ((307 : ℕ)^1 * ((11083 : ℕ)^1 * ((58603 : ℕ)^1 * ((311791 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 248679006649044053)^124339503324522026 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 307 := Nat.prime_eq_prime_of_dvd_pow hq prime_307 hd
        subst q
        change (2 : ZMod 248679006649044053)^810029337619036 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11083 := Nat.prime_eq_prime_of_dvd_pow hq prime_11083 hd
          subst q
          change (2 : ZMod 248679006649044053)^22437878430844 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 58603 := Nat.prime_eq_prime_of_dvd_pow hq prime_58603 hd
            subst q
            change (2 : ZMod 248679006649044053)^4243451813884 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 311791 := Nat.prime_eq_prime_of_dvd_pow hq prime_311791 hd
            subst q
            change (2 : ZMod 248679006649044053)^797582376172 ≠ 1
            reduce_mod_char
            decide

theorem prime_250566504564321863 : Nat.Prime 250566504564321863 := by
  apply lucas_primality 250566504564321863 (5 : ZMod 250566504564321863)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 250566504564321863 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((2069 : ℕ)^1 * ((5113 : ℕ)^1 * ((1691837689 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 250566504564321863)^125283252282160931 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 250566504564321863)^35795214937760266 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2069 := Nat.prime_eq_prime_of_dvd_pow hq prime_2069 hd
          subst q
          change (5 : ZMod 250566504564321863)^121105125453998 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 5113 := Nat.prime_eq_prime_of_dvd_pow hq prime_5113 hd
            subst q
            change (5 : ZMod 250566504564321863)^49005770499574 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1691837689 := Nat.prime_eq_prime_of_dvd_pow hq prime_1691837689 hd
            subst q
            change (5 : ZMod 250566504564321863)^148103158 ≠ 1
            reduce_mod_char
            decide

theorem prime_252465925985015681 : Nat.Prime 252465925985015681 := by
  apply lucas_primality 252465925985015681 (6 : ZMod 252465925985015681)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 252465925985015681 - 1 = (2 : ℕ)^7 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((337 : ℕ)^1 * ((2689 : ℕ)^1 * ((62187637 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 252465925985015681)^126232962992507840 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 252465925985015681)^50493185197003136 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 252465925985015681)^36066560855002240 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 337 := Nat.prime_eq_prime_of_dvd_pow hq prime_337 hd
            subst q
            change (6 : ZMod 252465925985015681)^749157050400640 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 2689 := Nat.prime_eq_prime_of_dvd_pow hq prime_2689 hd
              subst q
              change (6 : ZMod 252465925985015681)^93888406837120 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 62187637 := Nat.prime_eq_prime_of_dvd_pow hq prime_62187637 hd
              subst q
              change (6 : ZMod 252465925985015681)^4059744640 ≠ 1
              reduce_mod_char
              decide

theorem prime_254377331092688957 : Nat.Prime 254377331092688957 := by
  apply lucas_primality 254377331092688957 (2 : ZMod 254377331092688957)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 254377331092688957 - 1 = (2 : ℕ)^2 * ((31 : ℕ)^1 * ((211 : ℕ)^1 * ((127591 : ℕ)^1 * ((76199869 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 254377331092688957)^127188665546344478 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (2 : ZMod 254377331092688957)^8205720357828676 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 211 := Nat.prime_eq_prime_of_dvd_pow hq prime_211 hd
          subst q
          change (2 : ZMod 254377331092688957)^1205579768211796 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 127591 := Nat.prime_eq_prime_of_dvd_pow hq prime_127591 hd
            subst q
            change (2 : ZMod 254377331092688957)^1993693372516 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 76199869 := Nat.prime_eq_prime_of_dvd_pow hq prime_76199869 hd
            subst q
            change (2 : ZMod 254377331092688957)^3338290924 ≠ 1
            reduce_mod_char
            decide

theorem prime_256300780296434351 : Nat.Prime 256300780296434351 := by
  apply lucas_primality 256300780296434351 (7 : ZMod 256300780296434351)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 256300780296434351 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((17 : ℕ)^1 * ((599699 : ℕ)^1 * ((502802789 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 256300780296434351)^128150390148217175 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 256300780296434351)^51260156059286870 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (7 : ZMod 256300780296434351)^15076516488025550 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 599699 := Nat.prime_eq_prime_of_dvd_pow hq prime_599699 hd
            subst q
            change (7 : ZMod 256300780296434351)^427382370650 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 502802789 := Nat.prime_eq_prime_of_dvd_pow hq prime_502802789 hd
            subst q
            change (7 : ZMod 256300780296434351)^509744150 ≠ 1
            reduce_mod_char
            decide

theorem prime_258236334233446489 : Nat.Prime 258236334233446489 := by
  apply lucas_primality 258236334233446489 (22 : ZMod 258236334233446489)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 258236334233446489 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((29 : ℕ)^1 * ((193 : ℕ)^1 * ((1922431170221 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (22 : ZMod 258236334233446489)^129118167116723244 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (22 : ZMod 258236334233446489)^86078778077815496 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (22 : ZMod 258236334233446489)^8904701180463672 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
            subst q
            change (22 : ZMod 258236334233446489)^1338012094473816 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1922431170221 := Nat.prime_eq_prime_of_dvd_pow hq prime_1922431170221 hd
            subst q
            change (22 : ZMod 258236334233446489)^134328 ≠ 1
            reduce_mod_char
            decide

theorem prime_260184053769595213 : Nat.Prime 260184053769595213 := by
  apply lucas_primality 260184053769595213 (2 : ZMod 260184053769595213)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 260184053769595213 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((179083 : ℕ)^1 * ((5264016389 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 260184053769595213)^130092026884797606 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 260184053769595213)^86728017923198404 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 260184053769595213)^11312350163895444 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 179083 := Nat.prime_eq_prime_of_dvd_pow hq prime_179083 hd
            subst q
            change (2 : ZMod 260184053769595213)^1452868523364 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 5264016389 := Nat.prime_eq_prime_of_dvd_pow hq prime_5264016389 hd
            subst q
            change (2 : ZMod 260184053769595213)^49426908 ≠ 1
            reduce_mod_char
            decide

theorem prime_262144000000000037 : Nat.Prime 262144000000000037 := by
  apply lucas_primality 262144000000000037 (2 : ZMod 262144000000000037)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 262144000000000037 - 1 = (2 : ℕ)^2 * ((11381813 : ℕ)^1 * ((5757957893 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 262144000000000037)^131072000000000018 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11381813 := Nat.prime_eq_prime_of_dvd_pow hq prime_11381813 hd
        subst q
        change (2 : ZMod 262144000000000037)^23031831572 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5757957893 := Nat.prime_eq_prime_of_dvd_pow hq prime_5757957893 hd
        subst q
        change (2 : ZMod 262144000000000037)^45527252 ≠ 1
        reduce_mod_char
        decide

theorem prime_264116234249604829 : Nat.Prime 264116234249604829 := by
  apply lucas_primality 264116234249604829 (2 : ZMod 264116234249604829)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 264116234249604829 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((7 : ℕ)^2 * ((13 : ℕ)^1 * ((127 : ℕ)^1 * ((337 : ℕ)^1 * ((421 : ℕ)^1 * ((213067 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 264116234249604829)^132058117124802414 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 264116234249604829)^88038744749868276 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 264116234249604829)^37730890607086404 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (2 : ZMod 264116234249604829)^20316633403815756 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
              subst q
              change (2 : ZMod 264116234249604829)^2079655387792164 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 337 := Nat.prime_eq_prime_of_dvd_pow hq prime_337 hd
                subst q
                change (2 : ZMod 264116234249604829)^783727698070044 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 421 := Nat.prime_eq_prime_of_dvd_pow hq prime_421 hd
                  subst q
                  change (2 : ZMod 264116234249604829)^627354475652268 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 213067 := Nat.prime_eq_prime_of_dvd_pow hq prime_213067 hd
                  subst q
                  change (2 : ZMod 264116234249604829)^1239592401684 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_266100818073753701 : Nat.Prime 266100818073753701 := by
  apply lucas_primality 266100818073753701 (2 : ZMod 266100818073753701)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 266100818073753701 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((17 : ℕ)^1 * ((29 : ℕ)^1 * ((881 : ℕ)^1 * ((6126654389 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 266100818073753701)^133050409036876850 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 266100818073753701)^53220163614750740 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 266100818073753701)^15652989298456100 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (2 : ZMod 266100818073753701)^9175890278405300 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 881 := Nat.prime_eq_prime_of_dvd_pow hq prime_881 hd
              subst q
              change (2 : ZMod 266100818073753701)^302044061377700 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 6126654389 := Nat.prime_eq_prime_of_dvd_pow hq prime_6126654389 hd
              subst q
              change (2 : ZMod 266100818073753701)^43433300 ≠ 1
              reduce_mod_char
              decide

theorem prime_268097813258767139 : Nat.Prime 268097813258767139 := by
  apply lucas_primality 268097813258767139 (2 : ZMod 268097813258767139)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 268097813258767139 - 1 = (2 : ℕ)^1 * ((134048906629383569 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 268097813258767139)^134048906629383569 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 134048906629383569 := Nat.prime_eq_prime_of_dvd_pow hq prime_134048906629383569 hd
      subst q
      change (2 : ZMod 268097813258767139)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_270107281822519357 : Nat.Prime 270107281822519357 := by
  apply lucas_primality 270107281822519357 (2 : ZMod 270107281822519357)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 270107281822519357 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((31 : ℕ)^1 * ((229 : ℕ)^1 * ((3170719841087 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 270107281822519357)^135053640911259678 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 270107281822519357)^90035760607506452 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (2 : ZMod 270107281822519357)^8713138123307076 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 229 := Nat.prime_eq_prime_of_dvd_pow hq prime_229 hd
            subst q
            change (2 : ZMod 270107281822519357)^1179507780884364 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3170719841087 := Nat.prime_eq_prime_of_dvd_pow hq prime_3170719841087 hd
            subst q
            change (2 : ZMod 270107281822519357)^85188 ≠ 1
            reduce_mod_char
            decide

theorem prime_272129286015015683 : Nat.Prime 272129286015015683 := by
  apply lucas_primality 272129286015015683 (5 : ZMod 272129286015015683)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 272129286015015683 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((53 : ℕ)^1 * ((83 : ℕ)^1 * ((577 : ℕ)^1 * ((4873296397 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 272129286015015683)^136064643007507841 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 272129286015015683)^24739026001365062 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (5 : ZMod 272129286015015683)^5134514830471994 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
            subst q
            change (5 : ZMod 272129286015015683)^3278666096566454 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 577 := Nat.prime_eq_prime_of_dvd_pow hq prime_577 hd
              subst q
              change (5 : ZMod 272129286015015683)^471627878708866 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 4873296397 := Nat.prime_eq_prime_of_dvd_pow hq prime_4873296397 hd
              subst q
              change (5 : ZMod 272129286015015683)^55840906 ≠ 1
              reduce_mod_char
              decide

theorem prime_274163888318971477 : Nat.Prime 274163888318971477 := by
  apply lucas_primality 274163888318971477 (2 : ZMod 274163888318971477)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 274163888318971477 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((4481 : ℕ)^1 * ((104053808567 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 274163888318971477)^137081944159485738 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 274163888318971477)^91387962772990492 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 274163888318971477)^39166269759853068 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 4481 := Nat.prime_eq_prime_of_dvd_pow hq prime_4481 hd
            subst q
            change (2 : ZMod 274163888318971477)^61183639437396 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 104053808567 := Nat.prime_eq_prime_of_dvd_pow hq prime_104053808567 hd
            subst q
            change (2 : ZMod 274163888318971477)^2634828 ≠ 1
            reduce_mod_char
            decide

theorem prime_276211151450391251 : Nat.Prime 276211151450391251 := by
  apply lucas_primality 276211151450391251 (2 : ZMod 276211151450391251)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 276211151450391251 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^4 * ((157 : ℕ)^1 * ((521 : ℕ)^1 * ((19801 : ℕ)^1 * ((136429 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 276211151450391251)^138105575725195625 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 276211151450391251)^55242230290078250 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
          subst q
          change (2 : ZMod 276211151450391251)^1759306697136250 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 521 := Nat.prime_eq_prime_of_dvd_pow hq prime_521 hd
            subst q
            change (2 : ZMod 276211151450391251)^530155760941250 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 19801 := Nat.prime_eq_prime_of_dvd_pow hq prime_19801 hd
              subst q
              change (2 : ZMod 276211151450391251)^13949353641250 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 136429 := Nat.prime_eq_prime_of_dvd_pow hq prime_136429 hd
              subst q
              change (2 : ZMod 276211151450391251)^2024577996250 ≠ 1
              reduce_mod_char
              decide

theorem prime_278271138359148547 : Nat.Prime 278271138359148547 := by
  apply lucas_primality 278271138359148547 (2 : ZMod 278271138359148547)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 278271138359148547 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((739 : ℕ)^1 * ((62758488578969 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 278271138359148547)^139135569179574273 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 278271138359148547)^92757046119716182 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 739 := Nat.prime_eq_prime_of_dvd_pow hq prime_739 hd
          subst q
          change (2 : ZMod 278271138359148547)^376550931473814 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 62758488578969 := Nat.prime_eq_prime_of_dvd_pow hq prime_62758488578969 hd
          subst q
          change (2 : ZMod 278271138359148547)^4434 ≠ 1
          reduce_mod_char
          decide

theorem prime_280343912229566693 : Nat.Prime 280343912229566693 := by
  apply lucas_primality 280343912229566693 (2 : ZMod 280343912229566693)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 280343912229566693 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((421 : ℕ)^1 * ((74771 : ℕ)^1 * ((171266531 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 280343912229566693)^140171956114783346 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 280343912229566693)^21564916325351284 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 421 := Nat.prime_eq_prime_of_dvd_pow hq prime_421 hd
          subst q
          change (2 : ZMod 280343912229566693)^665900029048852 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 74771 := Nat.prime_eq_prime_of_dvd_pow hq prime_74771 hd
            subst q
            change (2 : ZMod 280343912229566693)^3749366896652 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 171266531 := Nat.prime_eq_prime_of_dvd_pow hq prime_171266531 hd
            subst q
            change (2 : ZMod 280343912229566693)^1636886732 ≠ 1
            reduce_mod_char
            decide

theorem prime_282429536481000047 : Nat.Prime 282429536481000047 := by
  apply lucas_primality 282429536481000047 (5 : ZMod 282429536481000047)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 282429536481000047 - 1 = (2 : ℕ)^1 * ((12619 : ℕ)^1 * ((11190646504517 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 282429536481000047)^141214768240500023 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 12619 := Nat.prime_eq_prime_of_dvd_pow hq prime_12619 hd
        subst q
        change (5 : ZMod 282429536481000047)^22381293009034 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 11190646504517 := Nat.prime_eq_prime_of_dvd_pow hq prime_11190646504517 hd
        subst q
        change (5 : ZMod 282429536481000047)^25238 ≠ 1
        reduce_mod_char
        decide

theorem prime_284528074768416373 : Nat.Prime 284528074768416373 := by
  apply lucas_primality 284528074768416373 (2 : ZMod 284528074768416373)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 284528074768416373 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((37 : ℕ)^1 * ((1171 : ℕ)^1 * ((51151 : ℕ)^1 * ((465161 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 284528074768416373)^142264037384208186 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 284528074768416373)^94842691589472124 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 284528074768416373)^12370785859496364 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
            subst q
            change (2 : ZMod 284528074768416373)^7689947966713956 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1171 := Nat.prime_eq_prime_of_dvd_pow hq prime_1171 hd
              subst q
              change (2 : ZMod 284528074768416373)^242978714575932 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 51151 := Nat.prime_eq_prime_of_dvd_pow hq prime_51151 hd
                subst q
                change (2 : ZMod 284528074768416373)^5562512458572 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 465161 := Nat.prime_eq_prime_of_dvd_pow hq prime_465161 hd
                subst q
                change (2 : ZMod 284528074768416373)^611676548052 ≠ 1
                reduce_mod_char
                decide

theorem prime_286639590982979627 : Nat.Prime 286639590982979627 := by
  apply lucas_primality 286639590982979627 (2 : ZMod 286639590982979627)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 286639590982979627 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((23 : ℕ)^1 * ((4349 : ℕ)^1 * ((8737 : ℕ)^1 * ((23427641 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 286639590982979627)^143319795491489813 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 286639590982979627)^40948512997568518 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 286639590982979627)^12462590912303462 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 4349 := Nat.prime_eq_prime_of_dvd_pow hq prime_4349 hd
            subst q
            change (2 : ZMod 286639590982979627)^65909310412274 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 8737 := Nat.prime_eq_prime_of_dvd_pow hq prime_8737 hd
              subst q
              change (2 : ZMod 286639590982979627)^32807553048298 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 23427641 := Nat.prime_eq_prime_of_dvd_pow hq prime_23427641 hd
              subst q
              change (2 : ZMod 286639590982979627)^12235102586 ≠ 1
              reduce_mod_char
              decide

theorem prime_288764149252633277 : Nat.Prime 288764149252633277 := by
  apply lucas_primality 288764149252633277 (2 : ZMod 288764149252633277)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 288764149252633277 - 1 = (2 : ℕ)^2 * ((72191037313158319 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 288764149252633277)^144382074626316638 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 72191037313158319 := Nat.prime_eq_prime_of_dvd_pow hq prime_72191037313158319 hd
      subst q
      change (2 : ZMod 288764149252633277)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_290901813942684743 : Nat.Prime 290901813942684743 := by
  apply lucas_primality 290901813942684743 (5 : ZMod 290901813942684743)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 290901813942684743 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((59 : ℕ)^1 * ((101 : ℕ)^1 * ((1033 : ℕ)^1 * ((3375551099 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 290901813942684743)^145450906971342371 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 290901813942684743)^41557401991812106 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (5 : ZMod 290901813942684743)^4930539219367538 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
            subst q
            change (5 : ZMod 290901813942684743)^2880215979630542 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1033 := Nat.prime_eq_prime_of_dvd_pow hq prime_1033 hd
              subst q
              change (5 : ZMod 290901813942684743)^281608725985174 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 3375551099 := Nat.prime_eq_prime_of_dvd_pow hq prime_3375551099 hd
              subst q
              change (5 : ZMod 290901813942684743)^86179058 ≠ 1
              reduce_mod_char
              decide

theorem prime_293052649656390649 : Nat.Prime 293052649656390649 := by
  apply lucas_primality 293052649656390649 (19 : ZMod 293052649656390649)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 293052649656390649 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((31 : ℕ)^1 * ((71 : ℕ)^1 * ((5547717886877 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 293052649656390649)^146526324828195324 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 293052649656390649)^97684216552130216 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (19 : ZMod 293052649656390649)^9453311279238408 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
            subst q
            change (19 : ZMod 293052649656390649)^4127502107836488 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 5547717886877 := Nat.prime_eq_prime_of_dvd_pow hq prime_5547717886877 hd
            subst q
            change (19 : ZMod 293052649656390649)^52824 ≠ 1
            reduce_mod_char
            decide

theorem prime_295216721235542059 : Nat.Prime 295216721235542059 := by
  apply lucas_primality 295216721235542059 (2 : ZMod 295216721235542059)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 295216721235542059 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((43 : ℕ)^1 * ((1144250857502101 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 295216721235542059)^147608360617771029 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 295216721235542059)^98405573745180686 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (2 : ZMod 295216721235542059)^6865505145012606 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1144250857502101 := Nat.prime_eq_prime_of_dvd_pow hq prime_1144250857502101 hd
          subst q
          change (2 : ZMod 295216721235542059)^258 ≠ 1
          reduce_mod_char
          decide

theorem prime_297394093761051173 : Nat.Prime 297394093761051173 := by
  apply lucas_primality 297394093761051173 (2 : ZMod 297394093761051173)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 297394093761051173 - 1 = (2 : ℕ)^2 * ((290041 : ℕ)^1 * ((256337977873 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 297394093761051173)^148697046880525586 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 290041 := Nat.prime_eq_prime_of_dvd_pow hq prime_290041 hd
        subst q
        change (2 : ZMod 297394093761051173)^1025351911492 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 256337977873 := Nat.prime_eq_prime_of_dvd_pow hq prime_256337977873 hd
        subst q
        change (2 : ZMod 297394093761051173)^1160164 ≠ 1
        reduce_mod_char
        decide

theorem prime_299584832553538673 : Nat.Prime 299584832553538673 := by
  apply lucas_primality 299584832553538673 (3 : ZMod 299584832553538673)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 299584832553538673 - 1 = (2 : ℕ)^4 * ((7 : ℕ)^1 * ((37 : ℕ)^1 * ((1693 : ℕ)^1 * ((42701498641 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 299584832553538673)^149792416276769336 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 299584832553538673)^42797833221934096 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (3 : ZMod 299584832553538673)^8096887366311856 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1693 := Nat.prime_eq_prime_of_dvd_pow hq prime_1693 hd
            subst q
            change (3 : ZMod 299584832553538673)^176955010368304 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 42701498641 := Nat.prime_eq_prime_of_dvd_pow hq prime_42701498641 hd
            subst q
            change (3 : ZMod 299584832553538673)^7015792 ≠ 1
            reduce_mod_char
            decide

theorem prime_301789003173921113 : Nat.Prime 301789003173921113 := by
  apply lucas_primality 301789003173921113 (3 : ZMod 301789003173921113)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 301789003173921113 - 1 = (2 : ℕ)^3 * ((19 : ℕ)^1 * ((103 : ℕ)^1 * ((19276252118927 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 301789003173921113)^150894501586960556 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (3 : ZMod 301789003173921113)^15883631745995848 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
          subst q
          change (3 : ZMod 301789003173921113)^2929990322076904 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 19276252118927 := Nat.prime_eq_prime_of_dvd_pow hq prime_19276252118927 hd
          subst q
          change (3 : ZMod 301789003173921113)^15656 ≠ 1
          reduce_mod_char
          decide

theorem prime_304006671424000003 : Nat.Prime 304006671424000003 := by
  apply lucas_primality 304006671424000003 (2 : ZMod 304006671424000003)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 304006671424000003 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((43 : ℕ)^1 * ((1913 : ℕ)^1 * ((2953 : ℕ)^1 * ((208585921 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 304006671424000003)^152003335712000001 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 304006671424000003)^101335557141333334 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (2 : ZMod 304006671424000003)^7069922591255814 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1913 := Nat.prime_eq_prime_of_dvd_pow hq prime_1913 hd
            subst q
            change (2 : ZMod 304006671424000003)^158916189975954 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 2953 := Nat.prime_eq_prime_of_dvd_pow hq prime_2953 hd
              subst q
              change (2 : ZMod 304006671424000003)^102948415653234 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 208585921 := Nat.prime_eq_prime_of_dvd_pow hq prime_208585921 hd
              subst q
              change (2 : ZMod 304006671424000003)^1457464962 ≠ 1
              reduce_mod_char
              decide

theorem prime_306237903347050937 : Nat.Prime 306237903347050937 := by
  apply lucas_primality 306237903347050937 (3 : ZMod 306237903347050937)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 306237903347050937 - 1 = (2 : ℕ)^3 * ((17 : ℕ)^1 * ((31 : ℕ)^1 * ((79 : ℕ)^1 * ((104659 : ℕ)^1 * ((8785261 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 306237903347050937)^153118951673525468 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (3 : ZMod 306237903347050937)^18013994314532408 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (3 : ZMod 306237903347050937)^9878642043453256 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
            subst q
            change (3 : ZMod 306237903347050937)^3876429156291784 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 104659 := Nat.prime_eq_prime_of_dvd_pow hq prime_104659 hd
              subst q
              change (3 : ZMod 306237903347050937)^2926054169704 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 8785261 := Nat.prime_eq_prime_of_dvd_pow hq prime_8785261 hd
              subst q
              change (3 : ZMod 306237903347050937)^34858145176 ≠ 1
              reduce_mod_char
              decide

theorem prime_308482765228413509 : Nat.Prime 308482765228413509 := by
  apply lucas_primality 308482765228413509 (2 : ZMod 308482765228413509)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 308482765228413509 - 1 = (2 : ℕ)^2 * ((293 : ℕ)^1 * ((58901 : ℕ)^1 * ((4468694089 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 308482765228413509)^154241382614206754 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 293 := Nat.prime_eq_prime_of_dvd_pow hq prime_293 hd
        subst q
        change (2 : ZMod 308482765228413509)^1052842202144756 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 58901 := Nat.prime_eq_prime_of_dvd_pow hq prime_58901 hd
          subst q
          change (2 : ZMod 308482765228413509)^5237309472308 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4468694089 := Nat.prime_eq_prime_of_dvd_pow hq prime_4468694089 hd
          subst q
          change (2 : ZMod 308482765228413509)^69031972 ≠ 1
          reduce_mod_char
          decide

theorem prime_310741323596082329 : Nat.Prime 310741323596082329 := by
  apply lucas_primality 310741323596082329 (3 : ZMod 310741323596082329)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 310741323596082329 - 1 = (2 : ℕ)^3 * ((157 : ℕ)^1 * ((761 : ℕ)^1 * ((827 : ℕ)^1 * ((2857 : ℕ)^1 * ((137597 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 310741323596082329)^155370661798041164 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
        subst q
        change (3 : ZMod 310741323596082329)^1979244099338104 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 761 := Nat.prime_eq_prime_of_dvd_pow hq prime_761 hd
          subst q
          change (3 : ZMod 310741323596082329)^408332882517848 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 827 := Nat.prime_eq_prime_of_dvd_pow hq prime_827 hd
            subst q
            change (3 : ZMod 310741323596082329)^375745252232264 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 2857 := Nat.prime_eq_prime_of_dvd_pow hq prime_2857 hd
              subst q
              change (3 : ZMod 310741323596082329)^108764901503704 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 137597 := Nat.prime_eq_prime_of_dvd_pow hq prime_137597 hd
              subst q
              change (3 : ZMod 310741323596082329)^2258343740024 ≠ 1
              reduce_mod_char
              decide

theorem prime_313013645221298317 : Nat.Prime 313013645221298317 := by
  apply lucas_primality 313013645221298317 (2 : ZMod 313013645221298317)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 313013645221298317 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((433 : ℕ)^1 * ((60241271212721 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 313013645221298317)^156506822610649158 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 313013645221298317)^104337881740432772 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 433 := Nat.prime_eq_prime_of_dvd_pow hq prime_433 hd
          subst q
          change (2 : ZMod 313013645221298317)^722895254552652 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 60241271212721 := Nat.prime_eq_prime_of_dvd_pow hq prime_60241271212721 hd
          subst q
          change (2 : ZMod 313013645221298317)^5196 ≠ 1
          reduce_mod_char
          decide

theorem prime_315299797119140657 : Nat.Prime 315299797119140657 := by
  apply lucas_primality 315299797119140657 (3 : ZMod 315299797119140657)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 315299797119140657 - 1 = (2 : ℕ)^4 * ((33403 : ℕ)^1 * ((589954115497 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 315299797119140657)^157649898559570328 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 33403 := Nat.prime_eq_prime_of_dvd_pow hq prime_33403 hd
        subst q
        change (3 : ZMod 315299797119140657)^9439265847952 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 589954115497 := Nat.prime_eq_prime_of_dvd_pow hq prime_589954115497 hd
        subst q
        change (3 : ZMod 315299797119140657)^534448 ≠ 1
        reduce_mod_char
        decide

theorem prime_317599846549120621 : Nat.Prime 317599846549120621 := by
  apply lucas_primality 317599846549120621 (2 : ZMod 317599846549120621)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 317599846549120621 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((38047 : ℕ)^1 * ((15458455699 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 317599846549120621)^158799923274560310 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 317599846549120621)^105866615516373540 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 317599846549120621)^63519969309824124 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 38047 := Nat.prime_eq_prime_of_dvd_pow hq prime_38047 hd
            subst q
            change (2 : ZMod 317599846549120621)^8347566077460 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 15458455699 := Nat.prime_eq_prime_of_dvd_pow hq prime_15458455699 hd
            subst q
            change (2 : ZMod 317599846549120621)^20545380 ≠ 1
            reduce_mod_char
            decide

theorem prime_318537006681261323 : Nat.Prime 318537006681261323 := by
  apply lucas_primality 318537006681261323 (2 : ZMod 318537006681261323)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 318537006681261323 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((71 : ℕ)^1 * ((9735701 : ℕ)^1 * ((13553623 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 318537006681261323)^159268503340630661 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 318537006681261323)^18737470981250666 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
          subst q
          change (2 : ZMod 318537006681261323)^4486436713820582 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 9735701 := Nat.prime_eq_prime_of_dvd_pow hq prime_9735701 hd
            subst q
            change (2 : ZMod 318537006681261323)^32718445922 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 13553623 := Nat.prime_eq_prime_of_dvd_pow hq prime_13553623 hd
            subst q
            change (2 : ZMod 318537006681261323)^23501982214 ≠ 1
            reduce_mod_char
            decide

theorem prime_319913861015774099 : Nat.Prime 319913861015774099 := by
  apply lucas_primality 319913861015774099 (2 : ZMod 319913861015774099)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 319913861015774099 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((345769 : ℕ)^1 * ((27212477713 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 319913861015774099)^159956930507887049 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 319913861015774099)^18818462412692594 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 345769 := Nat.prime_eq_prime_of_dvd_pow hq prime_345769 hd
          subst q
          change (2 : ZMod 319913861015774099)^925224242242 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 27212477713 := Nat.prime_eq_prime_of_dvd_pow hq prime_27212477713 hd
          subst q
          change (2 : ZMod 319913861015774099)^11756146 ≠ 1
          reduce_mod_char
          decide

theorem prime_322241908269256933 : Nat.Prime 322241908269256933 := by
  apply lucas_primality 322241908269256933 (5 : ZMod 322241908269256933)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 322241908269256933 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((2441226577797401 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 322241908269256933)^161120954134628466 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 322241908269256933)^107413969423085644 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 322241908269256933)^29294718933568812 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2441226577797401 := Nat.prime_eq_prime_of_dvd_pow hq prime_2441226577797401 hd
          subst q
          change (5 : ZMod 322241908269256933)^132 ≠ 1
          reduce_mod_char
          decide

theorem prime_324584056305938633 : Nat.Prime 324584056305938633 := by
  apply lucas_primality 324584056305938633 (3 : ZMod 324584056305938633)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 324584056305938633 - 1 = (2 : ℕ)^3 * ((7 : ℕ)^1 * ((3557 : ℕ)^1 * ((1629503475571 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 324584056305938633)^162292028152969316 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 324584056305938633)^46369150900848376 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 3557 := Nat.prime_eq_prime_of_dvd_pow hq prime_3557 hd
          subst q
          change (3 : ZMod 324584056305938633)^91252194631976 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1629503475571 := Nat.prime_eq_prime_of_dvd_pow hq prime_1629503475571 hd
          subst q
          change (3 : ZMod 324584056305938633)^199192 ≠ 1
          reduce_mod_char
          decide

theorem prime_326940373369000007 : Nat.Prime 326940373369000007 := by
  apply lucas_primality 326940373369000007 (5 : ZMod 326940373369000007)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 326940373369000007 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^2 * ((11 : ℕ)^1 * ((313 : ℕ)^1 * ((968959122529 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 326940373369000007)^163470186684500003 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 326940373369000007)^46705767624142858 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 326940373369000007)^29721852124454546 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 313 := Nat.prime_eq_prime_of_dvd_pow hq prime_313 hd
            subst q
            change (5 : ZMod 326940373369000007)^1044537934086262 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 968959122529 := Nat.prime_eq_prime_of_dvd_pow hq prime_968959122529 hd
            subst q
            change (5 : ZMod 326940373369000007)^337414 ≠ 1
            reduce_mod_char
            decide

theorem prime_328723248515071471 : Nat.Prime 328723248515071471 := by
  apply lucas_primality 328723248515071471 (6 : ZMod 328723248515071471)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 328723248515071471 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((41 : ℕ)^1 * ((293 : ℕ)^1 * ((564881 : ℕ)^1 * ((1614733 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 328723248515071471)^164361624257535735 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 328723248515071471)^109574416171690490 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 328723248515071471)^65744649703014294 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (6 : ZMod 328723248515071471)^8017640207684670 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 293 := Nat.prime_eq_prime_of_dvd_pow hq prime_293 hd
              subst q
              change (6 : ZMod 328723248515071471)^1121922349880790 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 564881 := Nat.prime_eq_prime_of_dvd_pow hq prime_564881 hd
                subst q
                change (6 : ZMod 328723248515071471)^581933625870 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 1614733 := Nat.prime_eq_prime_of_dvd_pow hq prime_1614733 hd
                subst q
                change (6 : ZMod 328723248515071471)^203577463590 ≠ 1
                reduce_mod_char
                decide

theorem prime_329310927949028497 : Nat.Prime 329310927949028497 := by
  apply lucas_primality 329310927949028497 (5 : ZMod 329310927949028497)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 329310927949028497 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((6860644332271427 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 329310927949028497)^164655463974514248 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 329310927949028497)^109770309316342832 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 6860644332271427 := Nat.prime_eq_prime_of_dvd_pow hq prime_6860644332271427 hd
        subst q
        change (5 : ZMod 329310927949028497)^48 ≠ 1
        reduce_mod_char
        decide

theorem prime_331695788784615439 : Nat.Prime 331695788784615439 := by
  apply lucas_primality 331695788784615439 (3 : ZMod 331695788784615439)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 331695788784615439 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((263 : ℕ)^1 * ((210200119635371 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 331695788784615439)^165847894392307719 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 331695788784615439)^110565262928205146 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 263 := Nat.prime_eq_prime_of_dvd_pow hq prime_263 hd
          subst q
          change (3 : ZMod 331695788784615439)^1261200717812226 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 210200119635371 := Nat.prime_eq_prime_of_dvd_pow hq prime_210200119635371 hd
          subst q
          change (3 : ZMod 331695788784615439)^1578 ≠ 1
          reduce_mod_char
          decide

theorem prime_334095024862954391 : Nat.Prime 334095024862954391 := by
  apply lucas_primality 334095024862954391 (7 : ZMod 334095024862954391)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 334095024862954391 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((1801 : ℕ)^1 * ((549547 : ℕ)^1 * ((4822291 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 334095024862954391)^167047512431477195 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 334095024862954391)^66819004972590878 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 334095024862954391)^47727860694707770 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1801 := Nat.prime_eq_prime_of_dvd_pow hq prime_1801 hd
            subst q
            change (7 : ZMod 334095024862954391)^185505288652390 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 549547 := Nat.prime_eq_prime_of_dvd_pow hq prime_549547 hd
              subst q
              change (7 : ZMod 334095024862954391)^607946226370 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 4822291 := Nat.prime_eq_prime_of_dvd_pow hq prime_4822291 hd
              subst q
              change (7 : ZMod 334095024862954391)^69281390290 ≠ 1
              reduce_mod_char
              decide

theorem prime_336508705420439623 : Nat.Prime 336508705420439623 := by
  apply lucas_primality 336508705420439623 (3 : ZMod 336508705420439623)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 336508705420439623 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((23167 : ℕ)^1 * ((185069 : ℕ)^1 * ((1868717 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 336508705420439623)^168254352710219811 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 336508705420439623)^112169568473479874 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 336508705420439623)^48072672202919946 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23167 := Nat.prime_eq_prime_of_dvd_pow hq prime_23167 hd
            subst q
            change (3 : ZMod 336508705420439623)^14525346631866 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 185069 := Nat.prime_eq_prime_of_dvd_pow hq prime_185069 hd
              subst q
              change (3 : ZMod 336508705420439623)^1818287803038 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1868717 := Nat.prime_eq_prime_of_dvd_pow hq prime_1868717 hd
              subst q
              change (3 : ZMod 336508705420439623)^180074727966 ≠ 1
              reduce_mod_char
              decide

theorem prime_338936899943265641 : Nat.Prime 338936899943265641 := by
  apply lucas_primality 338936899943265641 (6 : ZMod 338936899943265641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 338936899943265641 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((113 : ℕ)^1 * ((827 : ℕ)^1 * ((90672357691 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 338936899943265641)^169468449971632820 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 338936899943265641)^67787379988653128 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
          subst q
          change (6 : ZMod 338936899943265641)^2999441592418280 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 827 := Nat.prime_eq_prime_of_dvd_pow hq prime_827 hd
            subst q
            change (6 : ZMod 338936899943265641)^409839056763320 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 90672357691 := Nat.prime_eq_prime_of_dvd_pow hq prime_90672357691 hd
            subst q
            change (6 : ZMod 338936899943265641)^3738040 ≠ 1
            reduce_mod_char
            decide

theorem prime_341379678168027157 : Nat.Prime 341379678168027157 := by
  apply lucas_primality 341379678168027157 (2 : ZMod 341379678168027157)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 341379678168027157 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((502321 : ℕ)^1 * ((8090531329 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 341379678168027157)^170689839084013578 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 341379678168027157)^113793226056009052 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 341379678168027157)^48768525452575308 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 502321 := Nat.prime_eq_prime_of_dvd_pow hq prime_502321 hd
            subst q
            change (2 : ZMod 341379678168027157)^679604631636 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 8090531329 := Nat.prime_eq_prime_of_dvd_pow hq prime_8090531329 hd
            subst q
            change (2 : ZMod 341379678168027157)^42194964 ≠ 1
            reduce_mod_char
            decide

theorem prime_343837110082320013 : Nat.Prime 343837110082320013 := by
  apply lucas_primality 343837110082320013 (6 : ZMod 343837110082320013)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 343837110082320013 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((1916443 : ℕ)^1 * ((14951184307 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 343837110082320013)^171918555041160006 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 343837110082320013)^114612370027440004 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1916443 := Nat.prime_eq_prime_of_dvd_pow hq prime_1916443 hd
          subst q
          change (6 : ZMod 343837110082320013)^179414211684 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 14951184307 := Nat.prime_eq_prime_of_dvd_pow hq prime_14951184307 hd
          subst q
          change (6 : ZMod 343837110082320013)^22997316 ≠ 1
          reduce_mod_char
          decide

theorem prime_346309265925342827 : Nat.Prime 346309265925342827 := by
  apply lucas_primality 346309265925342827 (2 : ZMod 346309265925342827)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 346309265925342827 - 1 = (2 : ℕ)^1 * ((8999 : ℕ)^1 * ((21911 : ℕ)^1 * ((27241 : ℕ)^1 * ((32237 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 346309265925342827)^173154632962671413 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 8999 := Nat.prime_eq_prime_of_dvd_pow hq prime_8999 hd
        subst q
        change (2 : ZMod 346309265925342827)^38483083223174 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 21911 := Nat.prime_eq_prime_of_dvd_pow hq prime_21911 hd
          subst q
          change (2 : ZMod 346309265925342827)^15805269769766 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 27241 := Nat.prime_eq_prime_of_dvd_pow hq prime_27241 hd
            subst q
            change (2 : ZMod 346309265925342827)^12712795636186 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 32237 := Nat.prime_eq_prime_of_dvd_pow hq prime_32237 hd
            subst q
            change (2 : ZMod 346309265925342827)^10742602162898 ≠ 1
            reduce_mod_char
            decide

theorem prime_348796216188498977 : Nat.Prime 348796216188498977 := by
  apply lucas_primality 348796216188498977 (3 : ZMod 348796216188498977)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 348796216188498977 - 1 = (2 : ℕ)^5 * ((13523 : ℕ)^1 * ((241667 : ℕ)^1 * ((3335273 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 348796216188498977)^174398108094249488 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13523 := Nat.prime_eq_prime_of_dvd_pow hq prime_13523 hd
        subst q
        change (3 : ZMod 348796216188498977)^25792813442912 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 241667 := Nat.prime_eq_prime_of_dvd_pow hq prime_241667 hd
          subst q
          change (3 : ZMod 348796216188498977)^1443292696928 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3335273 := Nat.prime_eq_prime_of_dvd_pow hq prime_3335273 hd
          subst q
          change (3 : ZMod 348796216188498977)^104578010912 ≠ 1
          reduce_mod_char
          decide

theorem prime_351298031616000031 : Nat.Prime 351298031616000031 := by
  apply lucas_primality 351298031616000031 (3 : ZMod 351298031616000031)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 351298031616000031 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11709934387200001 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 351298031616000031)^175649015808000015 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 351298031616000031)^117099343872000010 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 351298031616000031)^70259606323200006 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11709934387200001 := Nat.prime_eq_prime_of_dvd_pow hq prime_11709934387200001 hd
          subst q
          change (3 : ZMod 351298031616000031)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_353814783205469059 : Nat.Prime 353814783205469059 := by
  apply lucas_primality 353814783205469059 (2 : ZMod 353814783205469059)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 353814783205469059 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((23 : ℕ)^2 * ((6179087 : ℕ)^1 * ((546677 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 353814783205469059)^176907391602734529 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 353814783205469059)^117938261068489686 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 353814783205469059)^32164980291406278 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (2 : ZMod 353814783205469059)^15383251443716046 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 6179087 := Nat.prime_eq_prime_of_dvd_pow hq prime_6179087 hd
              subst q
              change (2 : ZMod 353814783205469059)^57260042334 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 546677 := Nat.prime_eq_prime_of_dvd_pow hq prime_546677 hd
              subst q
              change (2 : ZMod 353814783205469059)^647209930554 ≠ 1
              reduce_mod_char
              decide

theorem prime_356346542208545359 : Nat.Prime 356346542208545359 := by
  apply lucas_primality 356346542208545359 (7 : ZMod 356346542208545359)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 356346542208545359 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((79 : ℕ)^1 * ((751785954026467 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 356346542208545359)^178173271104272679 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 356346542208545359)^118782180736181786 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (7 : ZMod 356346542208545359)^4510715724158802 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 751785954026467 := Nat.prime_eq_prime_of_dvd_pow hq prime_751785954026467 hd
          subst q
          change (7 : ZMod 356346542208545359)^474 ≠ 1
          reduce_mod_char
          decide

theorem prime_358194355500657331 : Nat.Prime 358194355500657331 := by
  apply lucas_primality 358194355500657331 (3 : ZMod 358194355500657331)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 358194355500657331 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((18679 : ℕ)^1 * ((213070147403 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 358194355500657331)^179097177750328665 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 358194355500657331)^119398118500219110 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 358194355500657331)^71638871100131466 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 18679 := Nat.prime_eq_prime_of_dvd_pow hq prime_18679 hd
            subst q
            change (3 : ZMod 358194355500657331)^19176313266270 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 213070147403 := Nat.prime_eq_prime_of_dvd_pow hq prime_213070147403 hd
            subst q
            change (3 : ZMod 358194355500657331)^1681110 ≠ 1
            reduce_mod_char
            decide

theorem prime_358893380131489453 : Nat.Prime 358893380131489453 := by
  apply lucas_primality 358893380131489453 (5 : ZMod 358893380131489453)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 358893380131489453 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((14285569 : ℕ)^1 * ((2093566009 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 358893380131489453)^179446690065744726 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 358893380131489453)^119631126710496484 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 14285569 := Nat.prime_eq_prime_of_dvd_pow hq prime_14285569 hd
          subst q
          change (5 : ZMod 358893380131489453)^25122792108 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2093566009 := Nat.prime_eq_prime_of_dvd_pow hq prime_2093566009 hd
          subst q
          change (5 : ZMod 358893380131489453)^171426828 ≠ 1
          reduce_mod_char
          decide

theorem prime_361455368735789059 : Nat.Prime 361455368735789059 := by
  apply lucas_primality 361455368735789059 (2 : ZMod 361455368735789059)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 361455368735789059 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13219 : ℕ)^1 * ((4557270705497 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 361455368735789059)^180727684367894529 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 361455368735789059)^120485122911929686 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13219 := Nat.prime_eq_prime_of_dvd_pow hq prime_13219 hd
          subst q
          change (2 : ZMod 361455368735789059)^27343624232982 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4557270705497 := Nat.prime_eq_prime_of_dvd_pow hq prime_4557270705497 hd
          subst q
          change (2 : ZMod 361455368735789059)^79314 ≠ 1
          reduce_mod_char
          decide

theorem prime_364032580038765641 : Nat.Prime 364032580038765641 := by
  apply lucas_primality 364032580038765641 (6 : ZMod 364032580038765641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 364032580038765641 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((535342029468773 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 364032580038765641)^182016290019382820 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 364032580038765641)^72806516007753128 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (6 : ZMod 364032580038765641)^21413681178750920 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 535342029468773 := Nat.prime_eq_prime_of_dvd_pow hq prime_535342029468773 hd
          subst q
          change (6 : ZMod 364032580038765641)^680 ≠ 1
          reduce_mod_char
          decide

theorem prime_366625086314181811 : Nat.Prime 366625086314181811 := by
  apply lucas_primality 366625086314181811 (3 : ZMod 366625086314181811)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 366625086314181811 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((281 : ℕ)^1 * ((421 : ℕ)^1 * ((4231 : ℕ)^1 * ((24415717 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 366625086314181811)^183312543157090905 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 366625086314181811)^122208362104727270 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 366625086314181811)^73325017262836362 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 281 := Nat.prime_eq_prime_of_dvd_pow hq prime_281 hd
            subst q
            change (3 : ZMod 366625086314181811)^1304715609659010 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 421 := Nat.prime_eq_prime_of_dvd_pow hq prime_421 hd
              subst q
              change (3 : ZMod 366625086314181811)^870843435425610 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 4231 := Nat.prime_eq_prime_of_dvd_pow hq prime_4231 hd
                subst q
                change (3 : ZMod 366625086314181811)^86652112104510 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 24415717 := Nat.prime_eq_prime_of_dvd_pow hq prime_24415717 hd
                subst q
                change (3 : ZMod 366625086314181811)^15015945930 ≠ 1
                reduce_mod_char
                decide

theorem prime_369232960092848933 : Nat.Prime 369232960092848933 := by
  apply lucas_primality 369232960092848933 (2 : ZMod 369232960092848933)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 369232960092848933 - 1 = (2 : ℕ)^2 * ((92308240023212233 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 369232960092848933)^184616480046424466 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 92308240023212233 := Nat.prime_eq_prime_of_dvd_pow hq prime_92308240023212233 hd
      subst q
      change (2 : ZMod 369232960092848933)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_371856274163236883 : Nat.Prime 371856274163236883 := by
  apply lucas_primality 371856274163236883 (5 : ZMod 371856274163236883)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 371856274163236883 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((821939 : ℕ)^1 * ((11905617601 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 371856274163236883)^185928137081618441 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (5 : ZMod 371856274163236883)^19571382850696678 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 821939 := Nat.prime_eq_prime_of_dvd_pow hq prime_821939 hd
          subst q
          change (5 : ZMod 371856274163236883)^452413468838 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11905617601 := Nat.prime_eq_prime_of_dvd_pow hq prime_11905617601 hd
          subst q
          change (5 : ZMod 371856274163236883)^31233682 ≠ 1
          reduce_mod_char
          decide

theorem prime_374495101572082427 : Nat.Prime 374495101572082427 := by
  apply lucas_primality 374495101572082427 (2 : ZMod 374495101572082427)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 374495101572082427 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((12373 : ℕ)^1 * ((1164120080237 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 374495101572082427)^187247550786041213 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 374495101572082427)^28807315505544802 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 12373 := Nat.prime_eq_prime_of_dvd_pow hq prime_12373 hd
          subst q
          change (2 : ZMod 374495101572082427)^30267122086162 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1164120080237 := Nat.prime_eq_prime_of_dvd_pow hq prime_1164120080237 hd
          subst q
          change (2 : ZMod 374495101572082427)^321698 ≠ 1
          reduce_mod_char
          decide

theorem prime_374565184962086693 : Nat.Prime 374565184962086693 := by
  apply lucas_primality 374565184962086693 (2 : ZMod 374565184962086693)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 374565184962086693 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((2016139 : ℕ)^1 * ((6635121901 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 374565184962086693)^187282592481043346 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 374565184962086693)^53509312137440956 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2016139 := Nat.prime_eq_prime_of_dvd_pow hq prime_2016139 hd
          subst q
          change (2 : ZMod 374565184962086693)^185783413228 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 6635121901 := Nat.prime_eq_prime_of_dvd_pow hq prime_6635121901 hd
          subst q
          change (2 : ZMod 374565184962086693)^56451892 ≠ 1
          reduce_mod_char
          decide

theorem prime_377149515625000021 : Nat.Prime 377149515625000021 := by
  apply lucas_primality 377149515625000021 (6 : ZMod 377149515625000021)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 377149515625000021 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((384367 : ℕ)^1 * ((2336243843 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 377149515625000021)^188574757812500010 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 377149515625000021)^125716505208333340 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 377149515625000021)^75429903125000004 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (6 : ZMod 377149515625000021)^53878502232142860 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 384367 := Nat.prime_eq_prime_of_dvd_pow hq prime_384367 hd
              subst q
              change (6 : ZMod 377149515625000021)^981222414060 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 2336243843 := Nat.prime_eq_prime_of_dvd_pow hq prime_2336243843 hd
              subst q
              change (6 : ZMod 377149515625000021)^161434140 ≠ 1
              reduce_mod_char
              decide

theorem prime_379819589887092659 : Nat.Prime 379819589887092659 := by
  apply lucas_primality 379819589887092659 (2 : ZMod 379819589887092659)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 379819589887092659 - 1 = (2 : ℕ)^1 * ((293 : ℕ)^2 * ((2212137531521 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 379819589887092659)^189909794943546329 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 293 := Nat.prime_eq_prime_of_dvd_pow hq prime_293 hd
        subst q
        change (2 : ZMod 379819589887092659)^1296312593471306 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2212137531521 := Nat.prime_eq_prime_of_dvd_pow hq prime_2212137531521 hd
        subst q
        change (2 : ZMod 379819589887092659)^171698 ≠ 1
        reduce_mod_char
        decide

theorem prime_382505398183563311 : Nat.Prime 382505398183563311 := by
  apply lucas_primality 382505398183563311 (13 : ZMod 382505398183563311)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 382505398183563311 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((31 : ℕ)^1 * ((1233888381237301 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 382505398183563311)^191252699091781655 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (13 : ZMod 382505398183563311)^76501079636712662 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (13 : ZMod 382505398183563311)^12338883812373010 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1233888381237301 := Nat.prime_eq_prime_of_dvd_pow hq prime_1233888381237301 hd
          subst q
          change (13 : ZMod 382505398183563311)^310 ≠ 1
          reduce_mod_char
          decide

theorem prime_385207014600327533 : Nat.Prime 385207014600327533 := by
  apply lucas_primality 385207014600327533 (2 : ZMod 385207014600327533)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 385207014600327533 - 1 = (2 : ℕ)^2 * ((577 : ℕ)^1 * ((3733 : ℕ)^1 * ((44709559663 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 385207014600327533)^192603507300163766 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 577 := Nat.prime_eq_prime_of_dvd_pow hq prime_577 hd
        subst q
        change (2 : ZMod 385207014600327533)^667603144887916 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 3733 := Nat.prime_eq_prime_of_dvd_pow hq prime_3733 hd
          subst q
          change (2 : ZMod 385207014600327533)^103189663702204 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 44709559663 := Nat.prime_eq_prime_of_dvd_pow hq prime_44709559663 hd
          subst q
          change (2 : ZMod 385207014600327533)^8615764 ≠ 1
          reduce_mod_char
          decide

theorem prime_385825381408691407 : Nat.Prime 385825381408691407 := by
  apply lucas_primality 385825381408691407 (5 : ZMod 385825381408691407)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 385825381408691407 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((19 : ℕ)^1 * ((179 : ℕ)^1 * ((223 : ℕ)^1 * ((269 : ℕ)^1 * ((1154551 : ℕ)^1)))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 385825381408691407)^192912690704345703 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 385825381408691407)^128608460469563802 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 385825381408691407)^55117911629813058 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (5 : ZMod 385825381408691407)^29678875492976262 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
              subst q
              change (5 : ZMod 385825381408691407)^20306599021510074 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 179 := Nat.prime_eq_prime_of_dvd_pow hq prime_179 hd
                subst q
                change (5 : ZMod 385825381408691407)^2155449058149114 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 223 := Nat.prime_eq_prime_of_dvd_pow hq prime_223 hd
                  subst q
                  change (5 : ZMod 385825381408691407)^1730158661025522 ≠ 1
                  reduce_mod_char
                  decide
                · rcases hq.dvd_mul.mp hd with hd | hd
                  · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
                    subst q
                    change (5 : ZMod 385825381408691407)^1434295098173574 ≠ 1
                    reduce_mod_char
                    decide
                  · have heq : q = 1154551 := Nat.prime_eq_prime_of_dvd_pow hq prime_1154551 hd
                    subst q
                    change (5 : ZMod 385825381408691407)^334177859106 ≠ 1
                    reduce_mod_char
                    decide

theorem prime_387924513484626527 : Nat.Prime 387924513484626527 := by
  apply lucas_primality 387924513484626527 (5 : ZMod 387924513484626527)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 387924513484626527 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((1181 : ℕ)^1 * ((2707 : ℕ)^1 * ((9871 : ℕ)^1 * ((267233 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 387924513484626527)^193962256742313263 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (5 : ZMod 387924513484626527)^16866283194983762 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1181 := Nat.prime_eq_prime_of_dvd_pow hq prime_1181 hd
          subst q
          change (5 : ZMod 387924513484626527)^328471222256246 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2707 := Nat.prime_eq_prime_of_dvd_pow hq prime_2707 hd
            subst q
            change (5 : ZMod 387924513484626527)^143304216285418 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 9871 := Nat.prime_eq_prime_of_dvd_pow hq prime_9871 hd
              subst q
              change (5 : ZMod 387924513484626527)^39299413786306 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 267233 := Nat.prime_eq_prime_of_dvd_pow hq prime_267233 hd
              subst q
              change (5 : ZMod 387924513484626527)^1451634017822 ≠ 1
              reduce_mod_char
              decide

theorem prime_390657969445640753 : Nat.Prime 390657969445640753 := by
  apply lucas_primality 390657969445640753 (3 : ZMod 390657969445640753)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 390657969445640753 - 1 = (2 : ℕ)^4 * ((24416123090352547 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 390657969445640753)^195328984722820376 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 24416123090352547 := Nat.prime_eq_prime_of_dvd_pow hq prime_24416123090352547 hd
      subst q
      change (3 : ZMod 390657969445640753)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_393407457355104259 : Nat.Prime 393407457355104259 := by
  apply lucas_primality 393407457355104259 (2 : ZMod 393407457355104259)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 393407457355104259 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((5960719050834913 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 393407457355104259)^196703728677552129 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 393407457355104259)^131135819118368086 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 393407457355104259)^35764314305009478 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 5960719050834913 := Nat.prime_eq_prime_of_dvd_pow hq prime_5960719050834913 hd
          subst q
          change (2 : ZMod 393407457355104259)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_396173052347920867 : Nat.Prime 396173052347920867 := by
  apply lucas_primality 396173052347920867 (5 : ZMod 396173052347920867)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 396173052347920867 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((1394711 : ℕ)^1 * ((5260256789 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 396173052347920867)^198086526173960433 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 396173052347920867)^132057684115973622 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1394711 := Nat.prime_eq_prime_of_dvd_pow hq prime_1394711 hd
          subst q
          change (5 : ZMod 396173052347920867)^284053866606 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 5260256789 := Nat.prime_eq_prime_of_dvd_pow hq prime_5260256789 hd
          subst q
          change (5 : ZMod 396173052347920867)^75314394 ≠ 1
          reduce_mod_char
          decide

theorem prime_398954829822778961 : Nat.Prime 398954829822778961 := by
  apply lucas_primality 398954829822778961 (3 : ZMod 398954829822778961)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 398954829822778961 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((4986935372784737 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 398954829822778961)^199477414911389480 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 398954829822778961)^79790965964555792 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4986935372784737 := Nat.prime_eq_prime_of_dvd_pow hq prime_4986935372784737 hd
        subst q
        change (3 : ZMod 398954829822778961)^80 ≠ 1
        reduce_mod_char
        decide

theorem prime_401752865442768857 : Nat.Prime 401752865442768857 := by
  apply lucas_primality 401752865442768857 (3 : ZMod 401752865442768857)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 401752865442768857 - 1 = (2 : ℕ)^3 * ((19373 : ℕ)^1 * ((524063 : ℕ)^1 * ((4946393 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 401752865442768857)^200876432721384428 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19373 := Nat.prime_eq_prime_of_dvd_pow hq prime_19373 hd
        subst q
        change (3 : ZMod 401752865442768857)^20737772438072 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 524063 := Nat.prime_eq_prime_of_dvd_pow hq prime_524063 hd
          subst q
          change (3 : ZMod 401752865442768857)^766611772712 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4946393 := Nat.prime_eq_prime_of_dvd_pow hq prime_4946393 hd
          subst q
          change (3 : ZMod 401752865442768857)^81221379992 ≠ 1
          reduce_mod_char
          decide

theorem prime_403376643999807853 : Nat.Prime 403376643999807853 := by
  apply lucas_primality 403376643999807853 (2 : ZMod 403376643999807853)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 403376643999807853 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((2331587 : ℕ)^1 * ((1310645353 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 403376643999807853)^201688321999903926 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 403376643999807853)^134458881333269284 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 403376643999807853)^36670603999982532 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2331587 := Nat.prime_eq_prime_of_dvd_pow hq prime_2331587 hd
            subst q
            change (2 : ZMod 403376643999807853)^173005186596 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1310645353 := Nat.prime_eq_prime_of_dvd_pow hq prime_1310645353 hd
            subst q
            change (2 : ZMod 403376643999807853)^307769484 ≠ 1
            reduce_mod_char
            decide

theorem prime_404567235136000021 : Nat.Prime 404567235136000021 := by
  apply lucas_primality 404567235136000021 (2 : ZMod 404567235136000021)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 404567235136000021 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^2 * ((23 : ℕ)^1 * ((5982952309021 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 404567235136000021)^202283617568000010 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 404567235136000021)^134855745045333340 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 404567235136000021)^80913447027200004 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (2 : ZMod 404567235136000021)^57795319305142860 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
              subst q
              change (2 : ZMod 404567235136000021)^17589879788521740 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 5982952309021 := Nat.prime_eq_prime_of_dvd_pow hq prime_5982952309021 hd
              subst q
              change (2 : ZMod 404567235136000021)^67620 ≠ 1
              reduce_mod_char
              decide

theorem prime_407398015096219183 : Nat.Prime 407398015096219183 := by
  apply lucas_primality 407398015096219183 (5 : ZMod 407398015096219183)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 407398015096219183 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((461 : ℕ)^1 * ((797 : ℕ)^1 * ((341227 : ℕ)^1 * ((77369 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 407398015096219183)^203699007548109591 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 407398015096219183)^135799338365406394 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 407398015096219183)^58199716442317026 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 461 := Nat.prime_eq_prime_of_dvd_pow hq prime_461 hd
            subst q
            change (5 : ZMod 407398015096219183)^883726713874662 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 797 := Nat.prime_eq_prime_of_dvd_pow hq prime_797 hd
              subst q
              change (5 : ZMod 407398015096219183)^511164385315206 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 341227 := Nat.prime_eq_prime_of_dvd_pow hq prime_341227 hd
                subst q
                change (5 : ZMod 407398015096219183)^1193920806666 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 77369 := Nat.prime_eq_prime_of_dvd_pow hq prime_77369 hd
                subst q
                change (5 : ZMod 407398015096219183)^5265649227678 ≠ 1
                reduce_mod_char
                decide

theorem prime_410245281783429193 : Nat.Prime 410245281783429193 := by
  apply lucas_primality 410245281783429193 (5 : ZMod 410245281783429193)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 410245281783429193 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((59 : ℕ)^1 * ((2099 : ℕ)^1 * ((46009408321 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 410245281783429193)^205122640891714596 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 410245281783429193)^136748427261143064 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (5 : ZMod 410245281783429193)^6953309860736088 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2099 := Nat.prime_eq_prime_of_dvd_pow hq prime_2099 hd
            subst q
            change (5 : ZMod 410245281783429193)^195447966547608 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 46009408321 := Nat.prime_eq_prime_of_dvd_pow hq prime_46009408321 hd
            subst q
            change (5 : ZMod 410245281783429193)^8916552 ≠ 1
            reduce_mod_char
            decide

theorem prime_413109111924508777 : Nat.Prime 413109111924508777 := by
  apply lucas_primality 413109111924508777 (5 : ZMod 413109111924508777)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 413109111924508777 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((97 : ℕ)^1 * ((127 : ℕ)^1 * ((11321 : ℕ)^1 * ((17631743 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 413109111924508777)^206554555962254388 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 413109111924508777)^137703037308169592 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 413109111924508777)^59015587417786968 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
            subst q
            change (5 : ZMod 413109111924508777)^4258856823964008 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
              subst q
              change (5 : ZMod 413109111924508777)^3252827652948888 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 11321 := Nat.prime_eq_prime_of_dvd_pow hq prime_11321 hd
                subst q
                change (5 : ZMod 413109111924508777)^36490514258856 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 17631743 := Nat.prime_eq_prime_of_dvd_pow hq prime_17631743 hd
                subst q
                change (5 : ZMod 413109111924508777)^23429851032 ≠ 1
                reduce_mod_char
                decide

theorem prime_415989582513831943 : Nat.Prime 415989582513831943 := by
  apply lucas_primality 415989582513831943 (5 : ZMod 415989582513831943)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 415989582513831943 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((107 : ℕ)^1 * ((773 : ℕ)^1 * ((10886222531 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 415989582513831943)^207994791256915971 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 415989582513831943)^138663194171277314 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 415989582513831943)^59427083216261706 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (5 : ZMod 415989582513831943)^37817234773984722 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
              subst q
              change (5 : ZMod 415989582513831943)^3887753107605906 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 773 := Nat.prime_eq_prime_of_dvd_pow hq prime_773 hd
                subst q
                change (5 : ZMod 415989582513831943)^538149524597454 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 10886222531 := Nat.prime_eq_prime_of_dvd_pow hq prime_10886222531 hd
                subst q
                change (5 : ZMod 415989582513831943)^38212482 ≠ 1
                reduce_mod_char
                decide

theorem prime_418886770813890641 : Nat.Prime 418886770813890641 := by
  apply lucas_primality 418886770813890641 (3 : ZMod 418886770813890641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 418886770813890641 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((31 : ℕ)^1 * ((168905955973343 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 418886770813890641)^209443385406945320 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 418886770813890641)^83777354162778128 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (3 : ZMod 418886770813890641)^13512476477867440 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 168905955973343 := Nat.prime_eq_prime_of_dvd_pow hq prime_168905955973343 hd
          subst q
          change (3 : ZMod 418886770813890641)^2480 ≠ 1
          reduce_mod_char
          decide

theorem prime_421800754355914823 : Nat.Prime 421800754355914823 := by
  apply lucas_primality 421800754355914823 (5 : ZMod 421800754355914823)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 421800754355914823 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((362381 : ℕ)^1 * ((1004977 : ℕ)^1 * ((82729 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 421800754355914823)^210900377177957411 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 421800754355914823)^60257250622273546 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 362381 := Nat.prime_eq_prime_of_dvd_pow hq prime_362381 hd
          subst q
          change (5 : ZMod 421800754355914823)^1163970391262 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1004977 := Nat.prime_eq_prime_of_dvd_pow hq prime_1004977 hd
            subst q
            change (5 : ZMod 421800754355914823)^419711848486 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 82729 := Nat.prime_eq_prime_of_dvd_pow hq prime_82729 hd
            subst q
            change (5 : ZMod 421800754355914823)^5098583983318 ≠ 1
            reduce_mod_char
            decide

theorem prime_424731610940495779 : Nat.Prime 424731610940495779 := by
  apply lucas_primality 424731610940495779 (2 : ZMod 424731610940495779)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 424731610940495779 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((401 : ℕ)^2 * ((17033 : ℕ)^1 * ((8615137 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 424731610940495779)^212365805470247889 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 424731610940495779)^141577203646831926 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 401 := Nat.prime_eq_prime_of_dvd_pow hq prime_401 hd
          subst q
          change (2 : ZMod 424731610940495779)^1059181074664578 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17033 := Nat.prime_eq_prime_of_dvd_pow hq prime_17033 hd
            subst q
            change (2 : ZMod 424731610940495779)^24935807605266 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 8615137 := Nat.prime_eq_prime_of_dvd_pow hq prime_8615137 hd
            subst q
            change (2 : ZMod 424731610940495779)^49300621794 ≠ 1
            reduce_mod_char
            decide

theorem prime_427679418638209093 : Nat.Prime 427679418638209093 := by
  apply lucas_primality 427679418638209093 (5 : ZMod 427679418638209093)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 427679418638209093 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((35639951553184091 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 427679418638209093)^213839709319104546 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 427679418638209093)^142559806212736364 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 35639951553184091 := Nat.prime_eq_prime_of_dvd_pow hq prime_35639951553184091 hd
        subst q
        change (5 : ZMod 427679418638209093)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_430644255790238389 : Nat.Prime 430644255790238389 := by
  apply lucas_primality 430644255790238389 (6 : ZMod 430644255790238389)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 430644255790238389 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((19 : ℕ)^1 * ((23 : ℕ)^1 * ((5059 : ℕ)^1 * ((5410906651 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 430644255790238389)^215322127895119194 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 430644255790238389)^143548085263412796 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (6 : ZMod 430644255790238389)^22665487146854652 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (6 : ZMod 430644255790238389)^18723663295227756 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 5059 := Nat.prime_eq_prime_of_dvd_pow hq prime_5059 hd
              subst q
              change (6 : ZMod 430644255790238389)^85124383433532 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 5410906651 := Nat.prime_eq_prime_of_dvd_pow hq prime_5410906651 hd
              subst q
              change (6 : ZMod 430644255790238389)^79588188 ≠ 1
              reduce_mod_char
              decide

theorem prime_433626201009000023 : Nat.Prime 433626201009000023 := by
  apply lucas_primality 433626201009000023 (5 : ZMod 433626201009000023)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 433626201009000023 - 1 = (2 : ℕ)^1 * ((373 : ℕ)^1 * ((299711 : ℕ)^1 * ((1939429537 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 433626201009000023)^216813100504500011 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 373 := Nat.prime_eq_prime_of_dvd_pow hq prime_373 hd
        subst q
        change (5 : ZMod 433626201009000023)^1162536731927614 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 299711 := Nat.prime_eq_prime_of_dvd_pow hq prime_299711 hd
          subst q
          change (5 : ZMod 433626201009000023)^1446814434602 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1939429537 := Nat.prime_eq_prime_of_dvd_pow hq prime_1939429537 hd
          subst q
          change (5 : ZMod 433626201009000023)^223584406 ≠ 1
          reduce_mod_char
          decide

theorem prime_436625333178768817 : Nat.Prime 436625333178768817 := by
  apply lucas_primality 436625333178768817 (7 : ZMod 436625333178768817)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 436625333178768817 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((63781 : ℕ)^1 * ((142618665557 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 436625333178768817)^218312666589384408 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 436625333178768817)^145541777726256272 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 63781 := Nat.prime_eq_prime_of_dvd_pow hq prime_63781 hd
          subst q
          change (7 : ZMod 436625333178768817)^6845695946736 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 142618665557 := Nat.prime_eq_prime_of_dvd_pow hq prime_142618665557 hd
          subst q
          change (7 : ZMod 436625333178768817)^3061488 ≠ 1
          reduce_mod_char
          decide

theorem prime_439641731456303177 : Nat.Prime 439641731456303177 := by
  apply lucas_primality 439641731456303177 (3 : ZMod 439641731456303177)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 439641731456303177 - 1 = (2 : ℕ)^3 * ((547 : ℕ)^1 * ((100466574830051 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 439641731456303177)^219820865728151588 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 547 := Nat.prime_eq_prime_of_dvd_pow hq prime_547 hd
        subst q
        change (3 : ZMod 439641731456303177)^803732598640408 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 100466574830051 := Nat.prime_eq_prime_of_dvd_pow hq prime_100466574830051 hd
        subst q
        change (3 : ZMod 439641731456303177)^4376 ≠ 1
        reduce_mod_char
        decide

theorem prime_442675475271472739 : Nat.Prime 442675475271472739 := by
  apply lucas_primality 442675475271472739 (2 : ZMod 442675475271472739)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 442675475271472739 - 1 = (2 : ℕ)^1 * ((26309 : ℕ)^1 * ((8413004585341 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 442675475271472739)^221337737635736369 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 26309 := Nat.prime_eq_prime_of_dvd_pow hq prime_26309 hd
        subst q
        change (2 : ZMod 442675475271472739)^16826009170682 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 8413004585341 := Nat.prime_eq_prime_of_dvd_pow hq prime_8413004585341 hd
        subst q
        change (2 : ZMod 442675475271472739)^52618 ≠ 1
        reduce_mod_char
        decide

theorem prime_445726644327885419 : Nat.Prime 445726644327885419 := by
  apply lucas_primality 445726644327885419 (2 : ZMod 445726644327885419)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 445726644327885419 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((193 : ℕ)^1 * ((3119 : ℕ)^1 * ((21777949931 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 445726644327885419)^222863322163942709 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 445726644327885419)^26219214372228554 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
          subst q
          change (2 : ZMod 445726644327885419)^2309464478382826 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3119 := Nat.prime_eq_prime_of_dvd_pow hq prime_3119 hd
            subst q
            change (2 : ZMod 445726644327885419)^142906907447222 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 21777949931 := Nat.prime_eq_prime_of_dvd_pow hq prime_21777949931 hd
            subst q
            change (2 : ZMod 445726644327885419)^20466878 ≠ 1
            reduce_mod_char
            decide

theorem prime_448795318603515733 : Nat.Prime 448795318603515733 := by
  apply lucas_primality 448795318603515733 (6 : ZMod 448795318603515733)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 448795318603515733 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((263 : ℕ)^1 * ((883 : ℕ)^1 * ((53682083753 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 448795318603515733)^224397659301757866 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 448795318603515733)^149598439534505244 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 263 := Nat.prime_eq_prime_of_dvd_pow hq prime_263 hd
          subst q
          change (6 : ZMod 448795318603515733)^1706446078340364 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 883 := Nat.prime_eq_prime_of_dvd_pow hq prime_883 hd
            subst q
            change (6 : ZMod 448795318603515733)^508261968973404 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 53682083753 := Nat.prime_eq_prime_of_dvd_pow hq prime_53682083753 hd
            subst q
            change (6 : ZMod 448795318603515733)^8360244 ≠ 1
            reduce_mod_char
            decide

theorem prime_451881578351333401 : Nat.Prime 451881578351333401 := by
  apply lucas_primality 451881578351333401 (7 : ZMod 451881578351333401)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 451881578351333401 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((753135963918889 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 451881578351333401)^225940789175666700 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 451881578351333401)^150627192783777800 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 451881578351333401)^90376315670266680 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 753135963918889 := Nat.prime_eq_prime_of_dvd_pow hq prime_753135963918889 hd
          subst q
          change (7 : ZMod 451881578351333401)^600 ≠ 1
          reduce_mod_char
          decide

theorem prime_454985504099933707 : Nat.Prime 454985504099933707 := by
  apply lucas_primality 454985504099933707 (2 : ZMod 454985504099933707)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 454985504099933707 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((89 : ℕ)^1 * ((199 : ℕ)^1 * ((2161 : ℕ)^1 * ((14479 : ℕ)^1 * ((45613 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 454985504099933707)^227492752049966853 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 454985504099933707)^151661834699977902 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (2 : ZMod 454985504099933707)^5112196675280154 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 199 := Nat.prime_eq_prime_of_dvd_pow hq prime_199 hd
            subst q
            change (2 : ZMod 454985504099933707)^2286359317085094 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 2161 := Nat.prime_eq_prime_of_dvd_pow hq prime_2161 hd
              subst q
              change (2 : ZMod 454985504099933707)^210543963026346 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 14479 := Nat.prime_eq_prime_of_dvd_pow hq prime_14479 hd
                subst q
                change (2 : ZMod 454985504099933707)^31423820989014 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 45613 := Nat.prime_eq_prime_of_dvd_pow hq prime_45613 hd
                subst q
                change (2 : ZMod 454985504099933707)^9974908558962 ≠ 1
                reduce_mod_char
                decide

theorem prime_455107169091097657 : Nat.Prime 455107169091097657 := by
  apply lucas_primality 455107169091097657 (5 : ZMod 455107169091097657)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 455107169091097657 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((23 : ℕ)^1 * ((79 : ℕ)^1 * ((991 : ℕ)^1 * ((1231 : ℕ)^1 * ((407377 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 455107169091097657)^227553584545548828 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 455107169091097657)^151702389697032552 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 455107169091097657)^65015309870156808 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (5 : ZMod 455107169091097657)^19787268221352072 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
              subst q
              change (5 : ZMod 455107169091097657)^5760850241659464 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 991 := Nat.prime_eq_prime_of_dvd_pow hq prime_991 hd
                subst q
                change (5 : ZMod 455107169091097657)^459240332079816 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 1231 := Nat.prime_eq_prime_of_dvd_pow hq prime_1231 hd
                  subst q
                  change (5 : ZMod 455107169091097657)^369705255151176 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 407377 := Nat.prime_eq_prime_of_dvd_pow hq prime_407377 hd
                  subst q
                  change (5 : ZMod 455107169091097657)^1117164614328 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_458107176654167143 : Nat.Prime 458107176654167143 := by
  apply lucas_primality 458107176654167143 (5 : ZMod 458107176654167143)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 458107176654167143 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((76351196109027857 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 458107176654167143)^229053588327083571 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 458107176654167143)^152702392218055714 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 76351196109027857 := Nat.prime_eq_prime_of_dvd_pow hq prime_76351196109027857 hd
        subst q
        change (5 : ZMod 458107176654167143)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_461246677095770767 : Nat.Prime 461246677095770767 := by
  apply lucas_primality 461246677095770767 (3 : ZMod 461246677095770767)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 461246677095770767 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((607 : ℕ)^1 * ((5167 : ℕ)^1 * ((17987 : ℕ)^1 * ((454229 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 461246677095770767)^230623338547885383 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 461246677095770767)^153748892365256922 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 607 := Nat.prime_eq_prime_of_dvd_pow hq prime_607 hd
          subst q
          change (3 : ZMod 461246677095770767)^759879204441138 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 5167 := Nat.prime_eq_prime_of_dvd_pow hq prime_5167 hd
            subst q
            change (3 : ZMod 461246677095770767)^89267791193298 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 17987 := Nat.prime_eq_prime_of_dvd_pow hq prime_17987 hd
              subst q
              change (3 : ZMod 461246677095770767)^25643335581018 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 454229 := Nat.prime_eq_prime_of_dvd_pow hq prime_454229 hd
              subst q
              change (3 : ZMod 461246677095770767)^1015449645654 ≠ 1
              reduce_mod_char
              decide

theorem prime_464404086784000031 : Nat.Prime 464404086784000031 := by
  apply lucas_primality 464404086784000031 (7 : ZMod 464404086784000031)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 464404086784000031 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((149 : ℕ)^1 * ((311680595157047 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 464404086784000031)^232202043392000015 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 464404086784000031)^92880817356800006 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
          subst q
          change (7 : ZMod 464404086784000031)^3116805951570470 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 311680595157047 := Nat.prime_eq_prime_of_dvd_pow hq prime_311680595157047 hd
          subst q
          change (7 : ZMod 464404086784000031)^1490 ≠ 1
          reduce_mod_char
          decide

theorem prime_467579487356261447 : Nat.Prime 467579487356261447 := by
  apply lucas_primality 467579487356261447 (5 : ZMod 467579487356261447)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 467579487356261447 - 1 = (2 : ℕ)^1 * ((29 : ℕ)^1 * ((608177 : ℕ)^1 * ((13255541231 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 467579487356261447)^233789743678130723 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (5 : ZMod 467579487356261447)^16123430598491774 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 608177 := Nat.prime_eq_prime_of_dvd_pow hq prime_608177 hd
          subst q
          change (5 : ZMod 467579487356261447)^768821391398 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13255541231 := Nat.prime_eq_prime_of_dvd_pow hq prime_13255541231 hd
          subst q
          change (5 : ZMod 467579487356261447)^35274266 ≠ 1
          reduce_mod_char
          decide

theorem prime_470772960728745043 : Nat.Prime 470772960728745043 := by
  apply lucas_primality 470772960728745043 (5 : ZMod 470772960728745043)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 470772960728745043 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((19 : ℕ)^1 * ((6827 : ℕ)^1 * ((1775867 : ℕ)^1 * ((113539 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 470772960728745043)^235386480364372521 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 470772960728745043)^156924320242915014 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (5 : ZMod 470772960728745043)^24777524248881318 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 6827 := Nat.prime_eq_prime_of_dvd_pow hq prime_6827 hd
            subst q
            change (5 : ZMod 470772960728745043)^68957515853046 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1775867 := Nat.prime_eq_prime_of_dvd_pow hq prime_1775867 hd
              subst q
              change (5 : ZMod 470772960728745043)^265094717526 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 113539 := Nat.prime_eq_prime_of_dvd_pow hq prime_113539 hd
              subst q
              change (5 : ZMod 470772960728745043)^4146354651078 ≠ 1
              reduce_mod_char
              decide

theorem prime_473984589097059773 : Nat.Prime 473984589097059773 := by
  apply lucas_primality 473984589097059773 (2 : ZMod 473984589097059773)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 473984589097059773 - 1 = (2 : ℕ)^2 * ((1867 : ℕ)^1 * ((489613 : ℕ)^1 * ((129630433 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 473984589097059773)^236992294548529886 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1867 := Nat.prime_eq_prime_of_dvd_pow hq prime_1867 hd
        subst q
        change (2 : ZMod 473984589097059773)^253874980769716 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 489613 := Nat.prime_eq_prime_of_dvd_pow hq prime_489613 hd
          subst q
          change (2 : ZMod 473984589097059773)^968080073644 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 129630433 := Nat.prime_eq_prime_of_dvd_pow hq prime_129630433 hd
          subst q
          change (2 : ZMod 473984589097059773)^3656429884 ≠ 1
          reduce_mod_char
          decide

theorem prime_477214454936866873 : Nat.Prime 477214454936866873 := by
  apply lucas_primality 477214454936866873 (5 : ZMod 477214454936866873)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 477214454936866873 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((17477 : ℕ)^1 * ((1137720182089 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 477214454936866873)^238607227468433436 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 477214454936866873)^159071484978955624 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17477 := Nat.prime_eq_prime_of_dvd_pow hq prime_17477 hd
          subst q
          change (5 : ZMod 477214454936866873)^27305284370136 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1137720182089 := Nat.prime_eq_prime_of_dvd_pow hq prime_1137720182089 hd
          subst q
          change (5 : ZMod 477214454936866873)^419448 ≠ 1
          reduce_mod_char
          decide

theorem prime_480462641004515671 : Nat.Prime 480462641004515671 := by
  apply lucas_primality 480462641004515671 (3 : ZMod 480462641004515671)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 480462641004515671 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((43 : ℕ)^1 * ((49201 : ℕ)^1 * ((2523333941 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 480462641004515671)^240231320502257835 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 480462641004515671)^160154213668171890 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 480462641004515671)^96092528200903134 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (3 : ZMod 480462641004515671)^11173549790802690 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 49201 := Nat.prime_eq_prime_of_dvd_pow hq prime_49201 hd
              subst q
              change (3 : ZMod 480462641004515671)^9765302351670 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 2523333941 := Nat.prime_eq_prime_of_dvd_pow hq prime_2523333941 hd
              subst q
              change (3 : ZMod 480462641004515671)^190407870 ≠ 1
              reduce_mod_char
              decide

theorem prime_483729230337679967 : Nat.Prime 483729230337679967 := by
  apply lucas_primality 483729230337679967 (5 : ZMod 483729230337679967)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 483729230337679967 - 1 = (2 : ℕ)^1 * ((167 : ℕ)^1 * ((300733 : ℕ)^1 * ((4815870253 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 483729230337679967)^241864615168839983 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
        subst q
        change (5 : ZMod 483729230337679967)^2896582217590898 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 300733 := Nat.prime_eq_prime_of_dvd_pow hq prime_300733 hd
          subst q
          change (5 : ZMod 483729230337679967)^1608500664502 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4815870253 := Nat.prime_eq_prime_of_dvd_pow hq prime_4815870253 hd
          subst q
          change (5 : ZMod 483729230337679967)^100444822 ≠ 1
          reduce_mod_char
          decide

theorem prime_487014306255994619 : Nat.Prime 487014306255994619 := by
  apply lucas_primality 487014306255994619 (2 : ZMod 487014306255994619)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 487014306255994619 - 1 = (2 : ℕ)^1 * ((243507153127997309 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 487014306255994619)^243507153127997309 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 243507153127997309 := Nat.prime_eq_prime_of_dvd_pow hq prime_243507153127997309 hd
      subst q
      change (2 : ZMod 487014306255994619)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_490317952361693189 : Nat.Prime 490317952361693189 := by
  apply lucas_primality 490317952361693189 (2 : ZMod 490317952361693189)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 490317952361693189 - 1 = (2 : ℕ)^2 * ((197 : ℕ)^1 * ((277 : ℕ)^1 * ((471301 : ℕ)^1 * ((4766213 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 490317952361693189)^245158976180846594 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
        subst q
        change (2 : ZMod 490317952361693189)^2488923616049204 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 277 := Nat.prime_eq_prime_of_dvd_pow hq prime_277 hd
          subst q
          change (2 : ZMod 490317952361693189)^1770100911053044 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 471301 := Nat.prime_eq_prime_of_dvd_pow hq prime_471301 hd
            subst q
            change (2 : ZMod 490317952361693189)^1040349908788 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 4766213 := Nat.prime_eq_prime_of_dvd_pow hq prime_4766213 hd
            subst q
            change (2 : ZMod 490317952361693189)^102873697076 ≠ 1
            reduce_mod_char
            decide

theorem prime_493640252540246291 : Nat.Prime 493640252540246291 := by
  apply lucas_primality 493640252540246291 (6 : ZMod 493640252540246291)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 493640252540246291 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((463 : ℕ)^1 * ((106617765127483 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 493640252540246291)^246820126270123145 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 493640252540246291)^98728050508049258 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 463 := Nat.prime_eq_prime_of_dvd_pow hq prime_463 hd
          subst q
          change (6 : ZMod 493640252540246291)^1066177651274830 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 106617765127483 := Nat.prime_eq_prime_of_dvd_pow hq prime_106617765127483 hd
          subst q
          change (6 : ZMod 493640252540246291)^4630 ≠ 1
          reduce_mod_char
          decide

theorem prime_496981290961000039 : Nat.Prime 496981290961000039 := by
  apply lucas_primality 496981290961000039 (3 : ZMod 496981290961000039)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 496981290961000039 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((2371 : ℕ)^1 * ((34934717486363 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 496981290961000039)^248490645480500019 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 496981290961000039)^165660430320333346 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2371 := Nat.prime_eq_prime_of_dvd_pow hq prime_2371 hd
          subst q
          change (3 : ZMod 496981290961000039)^209608304918178 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 34934717486363 := Nat.prime_eq_prime_of_dvd_pow hq prime_34934717486363 hd
          subst q
          change (3 : ZMod 496981290961000039)^14226 ≠ 1
          reduce_mod_char
          decide

theorem prime_500341152077816869 : Nat.Prime 500341152077816869 := by
  apply lucas_primality 500341152077816869 (11 : ZMod 500341152077816869)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 500341152077816869 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((79 : ℕ)^1 * ((727 : ℕ)^1 * ((3361 : ℕ)^1 * ((263737 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 500341152077816869)^250170576038908434 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 500341152077816869)^166780384025938956 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (11 : ZMod 500341152077816869)^71477307439688124 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (11 : ZMod 500341152077816869)^38487780929062836 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
              subst q
              change (11 : ZMod 500341152077816869)^6333432304782492 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 727 := Nat.prime_eq_prime_of_dvd_pow hq prime_727 hd
                subst q
                change (11 : ZMod 500341152077816869)^688227169295484 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 3361 := Nat.prime_eq_prime_of_dvd_pow hq prime_3361 hd
                  subst q
                  change (11 : ZMod 500341152077816869)^148866751585188 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 263737 := Nat.prime_eq_prime_of_dvd_pow hq prime_263737 hd
                  subst q
                  change (11 : ZMod 500341152077816869)^1897121572164 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_503719920629714947 : Nat.Prime 503719920629714947 := by
  apply lucas_primality 503719920629714947 (2 : ZMod 503719920629714947)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 503719920629714947 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((262139 : ℕ)^1 * ((320262609169 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 503719920629714947)^251859960314857473 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 503719920629714947)^167906640209904982 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 262139 := Nat.prime_eq_prime_of_dvd_pow hq prime_262139 hd
          subst q
          change (2 : ZMod 503719920629714947)^1921575655014 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 320262609169 := Nat.prime_eq_prime_of_dvd_pow hq prime_320262609169 hd
          subst q
          change (2 : ZMod 503719920629714947)^1572834 ≠ 1
          reduce_mod_char
          decide

theorem prime_507117681641509871 : Nat.Prime 507117681641509871 := by
  apply lucas_primality 507117681641509871 (11 : ZMod 507117681641509871)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 507117681641509871 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((23 : ℕ)^1 * ((13693 : ℕ)^1 * ((161020922033 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 507117681641509871)^253558840820754935 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 507117681641509871)^101423536328301974 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (11 : ZMod 507117681641509871)^22048594853978690 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13693 := Nat.prime_eq_prime_of_dvd_pow hq prime_13693 hd
            subst q
            change (11 : ZMod 507117681641509871)^37034812067590 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 161020922033 := Nat.prime_eq_prime_of_dvd_pow hq prime_161020922033 hd
            subst q
            change (11 : ZMod 507117681641509871)^3149390 ≠ 1
            reduce_mod_char
            decide

theorem prime_510534520424456321 : Nat.Prime 510534520424456321 := by
  apply lucas_primality 510534520424456321 (12 : ZMod 510534520424456321)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 510534520424456321 - 1 = (2 : ℕ)^7 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((29 : ℕ)^1 * ((53 : ℕ)^1 * ((39923436673 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (12 : ZMod 510534520424456321)^255267260212228160 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (12 : ZMod 510534520424456321)^102106904084891264 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (12 : ZMod 510534520424456321)^39271886186496640 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (12 : ZMod 510534520424456321)^17604638635326080 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
              subst q
              change (12 : ZMod 510534520424456321)^9632726800461440 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 39923436673 := Nat.prime_eq_prime_of_dvd_pow hq prime_39923436673 hd
              subst q
              change (12 : ZMod 510534520424456321)^12787840 ≠ 1
              reduce_mod_char
              decide

theorem prime_513970522576890661 : Nat.Prime 513970522576890661 := by
  apply lucas_primality 513970522576890661 (10 : ZMod 513970522576890661)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 513970522576890661 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^8 * ((5 : ℕ)^1 * ((112249 : ℕ)^1 * ((34894397 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 513970522576890661)^256985261288445330 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 513970522576890661)^171323507525630220 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (10 : ZMod 513970522576890661)^102794104515378132 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 112249 := Nat.prime_eq_prime_of_dvd_pow hq prime_112249 hd
            subst q
            change (10 : ZMod 513970522576890661)^4578842774340 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 34894397 := Nat.prime_eq_prime_of_dvd_pow hq prime_34894397 hd
            subst q
            change (10 : ZMod 513970522576890661)^14729313780 ≠ 1
            reduce_mod_char
            decide

theorem prime_517425773984874529 : Nat.Prime 517425773984874529 := by
  apply lucas_primality 517425773984874529 (7 : ZMod 517425773984874529)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 517425773984874529 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((59 : ℕ)^1 * ((5373730620481 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 517425773984874529)^258712886992437264 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 517425773984874529)^172475257994958176 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (7 : ZMod 517425773984874529)^30436810234404384 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
            subst q
            change (7 : ZMod 517425773984874529)^8769928372624992 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 5373730620481 := Nat.prime_eq_prime_of_dvd_pow hq prime_5373730620481 hd
            subst q
            change (7 : ZMod 517425773984874529)^96288 ≠ 1
            reduce_mod_char
            decide

theorem prime_520900360822838603 : Nat.Prime 520900360822838603 := by
  apply lucas_primality 520900360822838603 (2 : ZMod 520900360822838603)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 520900360822838603 - 1 = (2 : ℕ)^1 * ((622011029 : ℕ)^1 * ((418722769 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 520900360822838603)^260450180411419301 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 622011029 := Nat.prime_eq_prime_of_dvd_pow hq prime_622011029 hd
        subst q
        change (2 : ZMod 520900360822838603)^837445538 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 418722769 := Nat.prime_eq_prime_of_dvd_pow hq prime_418722769 hd
        subst q
        change (2 : ZMod 520900360822838603)^1244022058 ≠ 1
        reduce_mod_char
        decide

theorem prime_524394369554227327 : Nat.Prime 524394369554227327 := by
  apply lucas_primality 524394369554227327 (3 : ZMod 524394369554227327)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 524394369554227327 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((378350915984291 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 524394369554227327)^262197184777113663 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 524394369554227327)^174798123184742442 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 524394369554227327)^74913481364889618 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (3 : ZMod 524394369554227327)^47672215414020666 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 378350915984291 := Nat.prime_eq_prime_of_dvd_pow hq prime_378350915984291 hd
            subst q
            change (3 : ZMod 524394369554227327)^1386 ≠ 1
            reduce_mod_char
            decide

theorem prime_527614839384912743 : Nat.Prime 527614839384912743 := by
  apply lucas_primality 527614839384912743 (5 : ZMod 527614839384912743)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 527614839384912743 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((821 : ℕ)^1 * ((2043721 : ℕ)^1 * ((9248543 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 527614839384912743)^263807419692456371 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (5 : ZMod 527614839384912743)^31036167022641926 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 821 := Nat.prime_eq_prime_of_dvd_pow hq prime_821 hd
          subst q
          change (5 : ZMod 527614839384912743)^642649012649102 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2043721 := Nat.prime_eq_prime_of_dvd_pow hq prime_2043721 hd
            subst q
            change (5 : ZMod 527614839384912743)^258163829302 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 9248543 := Nat.prime_eq_prime_of_dvd_pow hq prime_9248543 hd
            subst q
            change (5 : ZMod 527614839384912743)^57048427994 ≠ 1
            reduce_mod_char
            decide

theorem prime_527907886932144613 : Nat.Prime 527907886932144613 := by
  apply lucas_primality 527907886932144613 (2 : ZMod 527907886932144613)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 527907886932144613 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((63919469 : ℕ)^1 * ((688246079 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 527907886932144613)^263953943466072306 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 527907886932144613)^175969295644048204 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 63919469 := Nat.prime_eq_prime_of_dvd_pow hq prime_63919469 hd
          subst q
          change (2 : ZMod 527907886932144613)^8258952948 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 688246079 := Nat.prime_eq_prime_of_dvd_pow hq prime_688246079 hd
          subst q
          change (2 : ZMod 527907886932144613)^767033628 ≠ 1
          reduce_mod_char
          decide

theorem prime_531441000000000017 : Nat.Prime 531441000000000017 := by
  apply lucas_primality 531441000000000017 (3 : ZMod 531441000000000017)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 531441000000000017 - 1 = (2 : ℕ)^4 * ((17 : ℕ)^1 * ((1953827205882353 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 531441000000000017)^265720500000000008 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (3 : ZMod 531441000000000017)^31261235294117648 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1953827205882353 := Nat.prime_eq_prime_of_dvd_pow hq prime_1953827205882353 hd
        subst q
        change (3 : ZMod 531441000000000017)^272 ≠ 1
        reduce_mod_char
        decide

theorem prime_534993796092155417 : Nat.Prime 534993796092155417 := by
  apply lucas_primality 534993796092155417 (3 : ZMod 534993796092155417)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 534993796092155417 - 1 = (2 : ℕ)^3 * ((54377 : ℕ)^1 * ((790819 : ℕ)^1 * ((1555129 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 534993796092155417)^267496898046077708 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 54377 := Nat.prime_eq_prime_of_dvd_pow hq prime_54377 hd
        subst q
        change (3 : ZMod 534993796092155417)^9838604485208 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 790819 := Nat.prime_eq_prime_of_dvd_pow hq prime_790819 hd
          subst q
          change (3 : ZMod 534993796092155417)^676505997064 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1555129 := Nat.prime_eq_prime_of_dvd_pow hq prime_1555129 hd
          subst q
          change (3 : ZMod 534993796092155417)^344018918104 ≠ 1
          reduce_mod_char
          decide

theorem prime_538566362834572973 : Nat.Prime 538566362834572973 := by
  apply lucas_primality 538566362834572973 (2 : ZMod 538566362834572973)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 538566362834572973 - 1 = (2 : ℕ)^2 * ((31 : ℕ)^1 * ((12109 : ℕ)^1 * ((358681734217 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 538566362834572973)^269283181417286486 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (2 : ZMod 538566362834572973)^17373108478534612 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 12109 := Nat.prime_eq_prime_of_dvd_pow hq prime_12109 hd
          subst q
          change (2 : ZMod 538566362834572973)^44476535042908 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 358681734217 := Nat.prime_eq_prime_of_dvd_pow hq prime_358681734217 hd
          subst q
          change (2 : ZMod 538566362834572973)^1501516 ≠ 1
          reduce_mod_char
          decide

theorem prime_542158788145462979 : Nat.Prime 542158788145462979 := by
  apply lucas_primality 542158788145462979 (2 : ZMod 542158788145462979)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 542158788145462979 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^2 * ((233 : ℕ)^1 * ((373 : ℕ)^1 * ((592469 : ℕ)^1 * ((107441 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 542158788145462979)^271079394072731489 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 542158788145462979)^77451255449351854 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
          subst q
          change (2 : ZMod 542158788145462979)^2326861751697266 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 373 := Nat.prime_eq_prime_of_dvd_pow hq prime_373 hd
            subst q
            change (2 : ZMod 542158788145462979)^1453508815403386 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 592469 := Nat.prime_eq_prime_of_dvd_pow hq prime_592469 hd
              subst q
              change (2 : ZMod 542158788145462979)^915083807162 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 107441 := Nat.prime_eq_prime_of_dvd_pow hq prime_107441 hd
              subst q
              change (2 : ZMod 542158788145462979)^5046107055458 ≠ 1
              reduce_mod_char
              decide

theorem prime_545771160235933711 : Nat.Prime 545771160235933711 := by
  apply lucas_primality 545771160235933711 (3 : ZMod 545771160235933711)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 545771160235933711 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((456047 : ℕ)^1 * ((3068572387 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 545771160235933711)^272885580117966855 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 545771160235933711)^181923720078644570 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 545771160235933711)^109154232047186742 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (3 : ZMod 545771160235933711)^41982396941225670 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 456047 := Nat.prime_eq_prime_of_dvd_pow hq prime_456047 hd
              subst q
              change (3 : ZMod 545771160235933711)^1196743230930 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 3068572387 := Nat.prime_eq_prime_of_dvd_pow hq prime_3068572387 hd
              subst q
              change (3 : ZMod 545771160235933711)^177858330 ≠ 1
              reduce_mod_char
              decide

theorem prime_549403567610640697 : Nat.Prime 549403567610640697 := by
  apply lucas_primality 549403567610640697 (10 : ZMod 549403567610640697)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 549403567610640697 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((13147 : ℕ)^1 * ((21487 : ℕ)^1 * ((27011987 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 549403567610640697)^274701783805320348 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 549403567610640697)^183134522536880232 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13147 := Nat.prime_eq_prime_of_dvd_pow hq prime_13147 hd
          subst q
          change (10 : ZMod 549403567610640697)^41789272656168 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 21487 := Nat.prime_eq_prime_of_dvd_pow hq prime_21487 hd
            subst q
            change (10 : ZMod 549403567610640697)^25569114702408 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 27011987 := Nat.prime_eq_prime_of_dvd_pow hq prime_27011987 hd
            subst q
            change (10 : ZMod 549403567610640697)^20339250408 ≠ 1
            reduce_mod_char
            decide

theorem prime_553056099068437067 : Nat.Prime 553056099068437067 := by
  apply lucas_primality 553056099068437067 (2 : ZMod 553056099068437067)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 553056099068437067 - 1 = (2 : ℕ)^1 * ((53 : ℕ)^1 * ((5217510368570161 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 553056099068437067)^276528049534218533 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
        subst q
        change (2 : ZMod 553056099068437067)^10435020737140322 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5217510368570161 := Nat.prime_eq_prime_of_dvd_pow hq prime_5217510368570161 hd
        subst q
        change (2 : ZMod 553056099068437067)^106 ≠ 1
        reduce_mod_char
        decide

theorem prime_556728843703025471 : Nat.Prime 556728843703025471 := by
  apply lucas_primality 556728843703025471 (7 : ZMod 556728843703025471)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 556728843703025471 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((55672884370302547 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 556728843703025471)^278364421851512735 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 556728843703025471)^111345768740605094 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 55672884370302547 := Nat.prime_eq_prime_of_dvd_pow hq prime_55672884370302547 hd
        subst q
        change (7 : ZMod 556728843703025471)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_560421890903609393 : Nat.Prime 560421890903609393 := by
  apply lucas_primality 560421890903609393 (3 : ZMod 560421890903609393)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 560421890903609393 - 1 = (2 : ℕ)^4 * ((7 : ℕ)^1 * ((28039657 : ℕ)^1 * ((178453213 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 560421890903609393)^280210945451804696 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 560421890903609393)^80060270129087056 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 28039657 := Nat.prime_eq_prime_of_dvd_pow hq prime_28039657 hd
          subst q
          change (3 : ZMod 560421890903609393)^19986759856 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 178453213 := Nat.prime_eq_prime_of_dvd_pow hq prime_178453213 hd
          subst q
          change (3 : ZMod 560421890903609393)^3140441584 ≠ 1
          reduce_mod_char
          decide

theorem prime_564135330355546063 : Nat.Prime 564135330355546063 := by
  apply lucas_primality 564135330355546063 (3 : ZMod 564135330355546063)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 564135330355546063 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((41 : ℕ)^1 * ((7577 : ℕ)^1 * ((372223 : ℕ)^1 * ((813107 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 564135330355546063)^282067665177773031 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 564135330355546063)^188045110118515354 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (3 : ZMod 564135330355546063)^13759398301354782 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7577 := Nat.prime_eq_prime_of_dvd_pow hq prime_7577 hd
            subst q
            change (3 : ZMod 564135330355546063)^74453653207806 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 372223 := Nat.prime_eq_prime_of_dvd_pow hq prime_372223 hd
              subst q
              change (3 : ZMod 564135330355546063)^1515584287794 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 813107 := Nat.prime_eq_prime_of_dvd_pow hq prime_813107 hd
              subst q
              change (3 : ZMod 564135330355546063)^693802083066 ≠ 1
              reduce_mod_char
              decide

theorem prime_567869252041000003 : Nat.Prime 567869252041000003 := by
  apply lucas_primality 567869252041000003 (2 : ZMod 567869252041000003)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 567869252041000003 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((94644875340166667 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 567869252041000003)^283934626020500001 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 567869252041000003)^189289750680333334 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 94644875340166667 := Nat.prime_eq_prime_of_dvd_pow hq prime_94644875340166667 hd
        subst q
        change (2 : ZMod 567869252041000003)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_571529893014356651 : Nat.Prime 571529893014356651 := by
  apply lucas_primality 571529893014356651 (6 : ZMod 571529893014356651)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 571529893014356651 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((11 : ℕ)^1 * ((3366917 : ℕ)^1 * ((308634059 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 571529893014356651)^285764946507178325 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 571529893014356651)^114305978602871330 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (6 : ZMod 571529893014356651)^51957263001305150 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3366917 := Nat.prime_eq_prime_of_dvd_pow hq prime_3366917 hd
            subst q
            change (6 : ZMod 571529893014356651)^169748732450 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 308634059 := Nat.prime_eq_prime_of_dvd_pow hq prime_308634059 hd
            subst q
            change (6 : ZMod 571529893014356651)^1851804350 ≠ 1
            reduce_mod_char
            decide

theorem prime_571623746239597019 : Nat.Prime 571623746239597019 := by
  apply lucas_primality 571623746239597019 (2 : ZMod 571623746239597019)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 571623746239597019 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((53 : ℕ)^1 * ((490243350119723 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 571623746239597019)^285811873119798509 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 571623746239597019)^51965795112690638 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (2 : ZMod 571623746239597019)^10785353702633906 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 490243350119723 := Nat.prime_eq_prime_of_dvd_pow hq prime_490243350119723 hd
          subst q
          change (2 : ZMod 571623746239597019)^1166 ≠ 1
          reduce_mod_char
          decide

end LegendreK6.Pratt
