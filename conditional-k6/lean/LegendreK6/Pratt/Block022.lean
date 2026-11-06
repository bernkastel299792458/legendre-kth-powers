import LegendreK6.Pratt.Block021

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LegendreK6.Pratt

theorem prime_3628410392018947 : Nat.Prime 3628410392018947 := by
  apply lucas_primality 3628410392018947 (2 : ZMod 3628410392018947)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3628410392018947 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((18443 : ℕ)^1 * ((32789408737 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3628410392018947)^1814205196009473 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3628410392018947)^1209470130672982 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 18443 := Nat.prime_eq_prime_of_dvd_pow hq prime_18443 hd
          subst q
          change (2 : ZMod 3628410392018947)^196736452422 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 32789408737 := Nat.prime_eq_prime_of_dvd_pow hq prime_32789408737 hd
          subst q
          change (2 : ZMod 3628410392018947)^110658 ≠ 1
          reduce_mod_char
          decide

theorem prime_3684302682180851 : Nat.Prime 3684302682180851 := by
  apply lucas_primality 3684302682180851 (2 : ZMod 3684302682180851)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3684302682180851 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((37 : ℕ)^1 * ((3089 : ℕ)^1 * ((644711869 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3684302682180851)^1842151341090425 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 3684302682180851)^736860536436170 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (2 : ZMod 3684302682180851)^99575748167050 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3089 := Nat.prime_eq_prime_of_dvd_pow hq prime_3089 hd
            subst q
            change (2 : ZMod 3684302682180851)^1192716957650 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 644711869 := Nat.prime_eq_prime_of_dvd_pow hq prime_644711869 hd
            subst q
            change (2 : ZMod 3684302682180851)^5714650 ≠ 1
            reduce_mod_char
            decide

theorem prime_3690242267860111 : Nat.Prime 3690242267860111 := by
  apply lucas_primality 3690242267860111 (3 : ZMod 3690242267860111)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3690242267860111 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((123008075595337 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3690242267860111)^1845121133930055 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3690242267860111)^1230080755953370 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 3690242267860111)^738048453572022 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 123008075595337 := Nat.prime_eq_prime_of_dvd_pow hq prime_123008075595337 hd
          subst q
          change (3 : ZMod 3690242267860111)^30 ≠ 1
          reduce_mod_char
          decide

theorem prime_3740910611784259 : Nat.Prime 3740910611784259 := by
  apply lucas_primality 3740910611784259 (2 : ZMod 3740910611784259)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3740910611784259 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((257 : ℕ)^1 * ((12973326577 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3740910611784259)^1870455305892129 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3740910611784259)^1246970203928086 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 3740910611784259)^340082782889478 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (2 : ZMod 3740910611784259)^220053565399074 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 257 := Nat.prime_eq_prime_of_dvd_pow hq prime_257 hd
              subst q
              change (2 : ZMod 3740910611784259)^14556072419394 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 12973326577 := Nat.prime_eq_prime_of_dvd_pow hq prime_12973326577 hd
              subst q
              change (2 : ZMod 3740910611784259)^288354 ≠ 1
              reduce_mod_char
              decide

theorem prime_3778492316172971 : Nat.Prime 3778492316172971 := by
  apply lucas_primality 3778492316172971 (2 : ZMod 3778492316172971)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3778492316172971 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^2 * ((41479 : ℕ)^1 * ((75284383 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3778492316172971)^1889246158086485 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 3778492316172971)^755698463234594 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 3778492316172971)^343499301470270 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 41479 := Nat.prime_eq_prime_of_dvd_pow hq prime_41479 hd
            subst q
            change (2 : ZMod 3778492316172971)^91094103430 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 75284383 := Nat.prime_eq_prime_of_dvd_pow hq prime_75284383 hd
            subst q
            change (2 : ZMod 3778492316172971)^50189590 ≠ 1
            reduce_mod_char
            decide

theorem prime_3798241492515713 : Nat.Prime 3798241492515713 := by
  apply lucas_primality 3798241492515713 (3 : ZMod 3798241492515713)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3798241492515713 - 1 = (2 : ℕ)^7 * ((11 : ℕ)^1 * ((639563 : ℕ)^1 * ((4217903 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3798241492515713)^1899120746257856 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 3798241492515713)^345294681137792 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 639563 := Nat.prime_eq_prime_of_dvd_pow hq prime_639563 hd
          subst q
          change (3 : ZMod 3798241492515713)^5938807424 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4217903 := Nat.prime_eq_prime_of_dvd_pow hq prime_4217903 hd
          subst q
          change (3 : ZMod 3798241492515713)^900504704 ≠ 1
          reduce_mod_char
          decide

theorem prime_3813432514976017 : Nat.Prime 3813432514976017 := by
  apply lucas_primality 3813432514976017 (7 : ZMod 3813432514976017)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3813432514976017 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^6 * ((83 : ℕ)^6)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 3813432514976017)^1906716257488008 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 3813432514976017)^1271144171658672 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
        subst q
        change (7 : ZMod 3813432514976017)^45944970059952 ≠ 1
        reduce_mod_char
        decide

theorem prime_3856302691946531 : Nat.Prime 3856302691946531 := by
  apply lucas_primality 3856302691946531 (6 : ZMod 3856302691946531)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3856302691946531 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((788701 : ℕ)^1 * ((69849079 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 3856302691946531)^1928151345973265 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 3856302691946531)^771260538389306 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 3856302691946531)^550900384563790 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 788701 := Nat.prime_eq_prime_of_dvd_pow hq prime_788701 hd
            subst q
            change (6 : ZMod 3856302691946531)^4889435530 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 69849079 := Nat.prime_eq_prime_of_dvd_pow hq prime_69849079 hd
            subst q
            change (6 : ZMod 3856302691946531)^55209070 ≠ 1
            reduce_mod_char
            decide

theorem prime_3915101633817533 : Nat.Prime 3915101633817533 := by
  apply lucas_primality 3915101633817533 (2 : ZMod 3915101633817533)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3915101633817533 - 1 = (2 : ℕ)^2 * ((29989 : ℕ)^1 * ((155209 : ℕ)^1 * ((210283 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3915101633817533)^1957550816908766 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29989 := Nat.prime_eq_prime_of_dvd_pow hq prime_29989 hd
        subst q
        change (2 : ZMod 3915101633817533)^130551256588 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 155209 := Nat.prime_eq_prime_of_dvd_pow hq prime_155209 hd
          subst q
          change (2 : ZMod 3915101633817533)^25224707548 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 210283 := Nat.prime_eq_prime_of_dvd_pow hq prime_210283 hd
          subst q
          change (2 : ZMod 3915101633817533)^18618250804 ≠ 1
          reduce_mod_char
          decide

theorem prime_3974645798323327 : Nat.Prime 3974645798323327 := by
  apply lucas_primality 3974645798323327 (5 : ZMod 3974645798323327)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3974645798323327 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((61 : ℕ)^1 * ((7253 : ℕ)^1 * ((71298497 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3974645798323327)^1987322899161663 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 3974645798323327)^1324881932774442 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 3974645798323327)^567806542617618 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
            subst q
            change (5 : ZMod 3974645798323327)^65158127841366 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 7253 := Nat.prime_eq_prime_of_dvd_pow hq prime_7253 hd
              subst q
              change (5 : ZMod 3974645798323327)^548000247942 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 71298497 := Nat.prime_eq_prime_of_dvd_pow hq prime_71298497 hd
              subst q
              change (5 : ZMod 3974645798323327)^55746558 ≠ 1
              reduce_mod_char
              decide

theorem prime_3992648919253087 : Nat.Prime 3992648919253087 := by
  apply lucas_primality 3992648919253087 (3 : ZMod 3992648919253087)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3992648919253087 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((71 : ℕ)^1 * ((2203 : ℕ)^2 * ((101641 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3992648919253087)^1996324459626543 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3992648919253087)^1330882973084362 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (3 : ZMod 3992648919253087)^210139416802794 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
            subst q
            change (3 : ZMod 3992648919253087)^56234491820466 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 2203 := Nat.prime_eq_prime_of_dvd_pow hq prime_2203 hd
              subst q
              change (3 : ZMod 3992648919253087)^1812369005562 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 101641 := Nat.prime_eq_prime_of_dvd_pow hq prime_101641 hd
              subst q
              change (3 : ZMod 3992648919253087)^39281873646 ≠ 1
              reduce_mod_char
              decide

theorem prime_4010613184064351 : Nat.Prime 4010613184064351 := by
  apply lucas_primality 4010613184064351 (7 : ZMod 4010613184064351)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4010613184064351 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((4339 : ℕ)^1 * ((20641 : ℕ)^1 * ((895613 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 4010613184064351)^2005306592032175 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 4010613184064351)^802122636812870 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 4339 := Nat.prime_eq_prime_of_dvd_pow hq prime_4339 hd
          subst q
          change (7 : ZMod 4010613184064351)^924317396650 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 20641 := Nat.prime_eq_prime_of_dvd_pow hq prime_20641 hd
            subst q
            change (7 : ZMod 4010613184064351)^194303240350 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 895613 := Nat.prime_eq_prime_of_dvd_pow hq prime_895613 hd
            subst q
            change (7 : ZMod 4010613184064351)^4478064950 ≠ 1
            reduce_mod_char
            decide

theorem prime_4034942722397621 : Nat.Prime 4034942722397621 := by
  apply lucas_primality 4034942722397621 (2 : ZMod 4034942722397621)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4034942722397621 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((19 : ℕ)^1 * ((399353 : ℕ)^1 * ((2417153 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4034942722397621)^2017471361198810 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 4034942722397621)^806988544479524 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 4034942722397621)^366812974763420 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (2 : ZMod 4034942722397621)^212365406441980 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 399353 := Nat.prime_eq_prime_of_dvd_pow hq prime_399353 hd
              subst q
              change (2 : ZMod 4034942722397621)^10103699540 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 2417153 := Nat.prime_eq_prime_of_dvd_pow hq prime_2417153 hd
              subst q
              change (2 : ZMod 4034942722397621)^1669295540 ≠ 1
              reduce_mod_char
              decide

theorem prime_4096000000000061 : Nat.Prime 4096000000000061 := by
  apply lucas_primality 4096000000000061 (2 : ZMod 4096000000000061)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4096000000000061 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((113 : ℕ)^1 * ((1621 : ℕ)^1 * ((1118068711 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4096000000000061)^2048000000000030 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 4096000000000061)^819200000000012 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
          subst q
          change (2 : ZMod 4096000000000061)^36247787610620 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1621 := Nat.prime_eq_prime_of_dvd_pow hq prime_1621 hd
            subst q
            change (2 : ZMod 4096000000000061)^2526835286860 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1118068711 := Nat.prime_eq_prime_of_dvd_pow hq prime_1118068711 hd
            subst q
            change (2 : ZMod 4096000000000061)^3663460 ≠ 1
            reduce_mod_char
            decide

theorem prime_4105649096540171 : Nat.Prime 4105649096540171 := by
  apply lucas_primality 4105649096540171 (2 : ZMod 4105649096540171)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4105649096540171 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((410564909654017 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4105649096540171)^2052824548270085 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 4105649096540171)^821129819308034 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 410564909654017 := Nat.prime_eq_prime_of_dvd_pow hq prime_410564909654017 hd
        subst q
        change (2 : ZMod 4105649096540171)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_4157825282402411 : Nat.Prime 4157825282402411 := by
  apply lucas_primality 4157825282402411 (2 : ZMod 4157825282402411)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4157825282402411 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((66361 : ℕ)^1 * ((6265465081 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4157825282402411)^2078912641201205 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 4157825282402411)^831565056480482 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 66361 := Nat.prime_eq_prime_of_dvd_pow hq prime_66361 hd
          subst q
          change (2 : ZMod 4157825282402411)^62654650810 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 6265465081 := Nat.prime_eq_prime_of_dvd_pow hq prime_6265465081 hd
          subst q
          change (2 : ZMod 4157825282402411)^663610 ≠ 1
          reduce_mod_char
          decide

theorem prime_4220426278476893 : Nat.Prime 4220426278476893 := by
  apply lucas_primality 4220426278476893 (2 : ZMod 4220426278476893)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4220426278476893 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((53 : ℕ)^1 * ((443 : ℕ)^1 * ((25999 : ℕ)^1 * ((157133 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4220426278476893)^2110213139238446 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 4220426278476893)^383675116225172 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (2 : ZMod 4220426278476893)^79630684499564 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 443 := Nat.prime_eq_prime_of_dvd_pow hq prime_443 hd
            subst q
            change (2 : ZMod 4220426278476893)^9526921621844 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 25999 := Nat.prime_eq_prime_of_dvd_pow hq prime_25999 hd
              subst q
              change (2 : ZMod 4220426278476893)^162330331108 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 157133 := Nat.prime_eq_prime_of_dvd_pow hq prime_157133 hd
              subst q
              change (2 : ZMod 4220426278476893)^26858942924 ≠ 1
              reduce_mod_char
              decide

theorem prime_4283810754983933 : Nat.Prime 4283810754983933 := by
  apply lucas_primality 4283810754983933 (2 : ZMod 4283810754983933)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4283810754983933 - 1 = (2 : ℕ)^2 * ((787 : ℕ)^1 * ((10957 : ℕ)^1 * ((124194937 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4283810754983933)^2141905377491966 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 787 := Nat.prime_eq_prime_of_dvd_pow hq prime_787 hd
        subst q
        change (2 : ZMod 4283810754983933)^5443215698836 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 10957 := Nat.prime_eq_prime_of_dvd_pow hq prime_10957 hd
          subst q
          change (2 : ZMod 4283810754983933)^390965661676 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 124194937 := Nat.prime_eq_prime_of_dvd_pow hq prime_124194937 hd
          subst q
          change (2 : ZMod 4283810754983933)^34492636 ≠ 1
          reduce_mod_char
          decide

theorem prime_4347986536861711 : Nat.Prime 4347986536861711 := by
  apply lucas_primality 4347986536861711 (3 : ZMod 4347986536861711)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4347986536861711 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((173 : ℕ)^1 * ((1013 : ℕ)^1 * ((827011193 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4347986536861711)^2173993268430855 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 4347986536861711)^1449328845620570 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 4347986536861711)^869597307372342 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
            subst q
            change (3 : ZMod 4347986536861711)^25132870155270 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1013 := Nat.prime_eq_prime_of_dvd_pow hq prime_1013 hd
              subst q
              change (3 : ZMod 4347986536861711)^4292188091670 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 827011193 := Nat.prime_eq_prime_of_dvd_pow hq prime_827011193 hd
              subst q
              change (3 : ZMod 4347986536861711)^5257470 ≠ 1
              reduce_mod_char
              decide

theorem prime_4412961507515641 : Nat.Prime 4412961507515641 := by
  apply lucas_primality 4412961507515641 (7 : ZMod 4412961507515641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4412961507515641 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((363947 : ℕ)^1 * ((101044051 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 4412961507515641)^2206480753757820 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 4412961507515641)^1470987169171880 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 4412961507515641)^882592301503128 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 363947 := Nat.prime_eq_prime_of_dvd_pow hq prime_363947 hd
            subst q
            change (7 : ZMod 4412961507515641)^12125286120 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 101044051 := Nat.prime_eq_prime_of_dvd_pow hq prime_101044051 hd
            subst q
            change (7 : ZMod 4412961507515641)^43673640 ≠ 1
            reduce_mod_char
            decide

theorem prime_4478743609109069 : Nat.Prime 4478743609109069 := by
  apply lucas_primality 4478743609109069 (2 : ZMod 4478743609109069)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4478743609109069 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((2659 : ℕ)^1 * ((32391758101 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4478743609109069)^2239371804554534 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 4478743609109069)^344518739162236 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2659 := Nat.prime_eq_prime_of_dvd_pow hq prime_2659 hd
          subst q
          change (2 : ZMod 4478743609109069)^1684371421252 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 32391758101 := Nat.prime_eq_prime_of_dvd_pow hq prime_32391758101 hd
          subst q
          change (2 : ZMod 4478743609109069)^138268 ≠ 1
          reduce_mod_char
          decide

theorem prime_4545340842854509 : Nat.Prime 4545340842854509 := by
  apply lucas_primality 4545340842854509 (2 : ZMod 4545340842854509)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4545340842854509 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((378778403571209 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4545340842854509)^2272670421427254 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 4545340842854509)^1515113614284836 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 378778403571209 := Nat.prime_eq_prime_of_dvd_pow hq prime_378778403571209 hd
        subst q
        change (2 : ZMod 4545340842854509)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_4554777899892029 : Nat.Prime 4554777899892029 := by
  apply lucas_primality 4554777899892029 (2 : ZMod 4554777899892029)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4554777899892029 - 1 = (2 : ℕ)^2 * ((23 : ℕ)^1 * ((2767 : ℕ)^1 * ((17892466727 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4554777899892029)^2277388949946014 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (2 : ZMod 4554777899892029)^198033821734436 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2767 := Nat.prime_eq_prime_of_dvd_pow hq prime_2767 hd
          subst q
          change (2 : ZMod 4554777899892029)^1646106938884 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 17892466727 := Nat.prime_eq_prime_of_dvd_pow hq prime_17892466727 hd
          subst q
          change (2 : ZMod 4554777899892029)^254564 ≠ 1
          reduce_mod_char
          decide

theorem prime_4612761269305351 : Nat.Prime 4612761269305351 := by
  apply lucas_primality 4612761269305351 (6 : ZMod 4612761269305351)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4612761269305351 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((7 : ℕ)^1 * ((2239 : ℕ)^1 * ((22441 : ℕ)^1 * ((87433 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 4612761269305351)^2306380634652675 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 4612761269305351)^1537587089768450 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 4612761269305351)^922552253861070 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (6 : ZMod 4612761269305351)^658965895615050 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 2239 := Nat.prime_eq_prime_of_dvd_pow hq prime_2239 hd
              subst q
              change (6 : ZMod 4612761269305351)^2060188150650 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 22441 := Nat.prime_eq_prime_of_dvd_pow hq prime_22441 hd
                subst q
                change (6 : ZMod 4612761269305351)^205550611350 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 87433 := Nat.prime_eq_prime_of_dvd_pow hq prime_87433 hd
                subst q
                change (6 : ZMod 4612761269305351)^52757668950 ≠ 1
                reduce_mod_char
                decide

theorem prime_4630434214219141 : Nat.Prime 4630434214219141 := by
  apply lucas_primality 4630434214219141 (7 : ZMod 4630434214219141)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4630434214219141 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((23 : ℕ)^1 * ((623723 : ℕ)^1 * ((5379611 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 4630434214219141)^2315217107109570 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 4630434214219141)^1543478071406380 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 4630434214219141)^926086842843828 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (7 : ZMod 4630434214219141)^201323226705180 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 623723 := Nat.prime_eq_prime_of_dvd_pow hq prime_623723 hd
              subst q
              change (7 : ZMod 4630434214219141)^7423863180 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 5379611 := Nat.prime_eq_prime_of_dvd_pow hq prime_5379611 hd
              subst q
              change (7 : ZMod 4630434214219141)^860737740 ≠ 1
              reduce_mod_char
              decide

theorem prime_4652664185292391 : Nat.Prime 4652664185292391 := by
  apply lucas_primality 4652664185292391 (3 : ZMod 4652664185292391)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4652664185292391 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((19 : ℕ)^1 * ((53 : ℕ)^1 * ((227053 : ℕ)^1 * ((75367 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4652664185292391)^2326332092646195 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 4652664185292391)^1550888061764130 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 4652664185292391)^930532837058478 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (3 : ZMod 4652664185292391)^244877062383810 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
              subst q
              change (3 : ZMod 4652664185292391)^87786116703630 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 227053 := Nat.prime_eq_prime_of_dvd_pow hq prime_227053 hd
                subst q
                change (3 : ZMod 4652664185292391)^20491533630 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 75367 := Nat.prime_eq_prime_of_dvd_pow hq prime_75367 hd
                subst q
                change (3 : ZMod 4652664185292391)^61733440170 ≠ 1
                reduce_mod_char
                decide

theorem prime_4681013008649069 : Nat.Prime 4681013008649069 := by
  apply lucas_primality 4681013008649069 (2 : ZMod 4681013008649069)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4681013008649069 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^2 * ((13 : ℕ)^1 * ((19 : ℕ)^1 * ((181 : ℕ)^1 * ((211 : ℕ)^1 * ((787 : ℕ)^1 * ((3217 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 4681013008649069)^2340506504324534 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 4681013008649069)^668716144092724 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 4681013008649069)^360077923742236 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (2 : ZMod 4681013008649069)^246369105718372 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 181 := Nat.prime_eq_prime_of_dvd_pow hq prime_181 hd
              subst q
              change (2 : ZMod 4681013008649069)^25861950324028 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 211 := Nat.prime_eq_prime_of_dvd_pow hq prime_211 hd
                subst q
                change (2 : ZMod 4681013008649069)^22184895775588 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 787 := Nat.prime_eq_prime_of_dvd_pow hq prime_787 hd
                  subst q
                  change (2 : ZMod 4681013008649069)^5947919960164 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 3217 := Nat.prime_eq_prime_of_dvd_pow hq prime_3217 hd
                  subst q
                  change (2 : ZMod 4681013008649069)^1455086418604 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_4750104241000033 : Nat.Prime 4750104241000033 := by
  apply lucas_primality 4750104241000033 (5 : ZMod 4750104241000033)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4750104241000033 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((49480252510417 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 4750104241000033)^2375052120500016 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 4750104241000033)^1583368080333344 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 49480252510417 := Nat.prime_eq_prime_of_dvd_pow hq prime_49480252510417 hd
        subst q
        change (5 : ZMod 4750104241000033)^96 ≠ 1
        reduce_mod_char
        decide

theorem prime_4820043206694049 : Nat.Prime 4820043206694049 := by
  apply lucas_primality 4820043206694049 (7 : ZMod 4820043206694049)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4820043206694049 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((223 : ℕ)^1 * ((691 : ℕ)^1 * ((19166723 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 4820043206694049)^2410021603347024 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 4820043206694049)^1606681068898016 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (7 : ZMod 4820043206694049)^283531953334944 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 223 := Nat.prime_eq_prime_of_dvd_pow hq prime_223 hd
            subst q
            change (7 : ZMod 4820043206694049)^21614543527776 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 691 := Nat.prime_eq_prime_of_dvd_pow hq prime_691 hd
              subst q
              change (7 : ZMod 4820043206694049)^6975460501728 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 19166723 := Nat.prime_eq_prime_of_dvd_pow hq prime_19166723 hd
              subst q
              change (7 : ZMod 4820043206694049)^251479776 ≠ 1
              reduce_mod_char
              decide

theorem prime_4890838206582817 : Nat.Prime 4890838206582817 := by
  apply lucas_primality 4890838206582817 (5 : ZMod 4890838206582817)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4890838206582817 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((22129 : ℕ)^1 * ((2302238299 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 4890838206582817)^2445419103291408 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 4890838206582817)^1630279402194272 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 22129 := Nat.prime_eq_prime_of_dvd_pow hq prime_22129 hd
          subst q
          change (5 : ZMod 4890838206582817)^221014876704 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2302238299 := Nat.prime_eq_prime_of_dvd_pow hq prime_2302238299 hd
          subst q
          change (5 : ZMod 4890838206582817)^2124384 ≠ 1
          reduce_mod_char
          decide

theorem prime_4962497602330027 : Nat.Prime 4962497602330027 := by
  apply lucas_primality 4962497602330027 (17 : ZMod 4962497602330027)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4962497602330027 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((53 : ℕ)^1 * ((472889041579 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 4962497602330027)^2481248801165013 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 4962497602330027)^1654165867443342 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (17 : ZMod 4962497602330027)^451136145666366 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
            subst q
            change (17 : ZMod 4962497602330027)^93632030232642 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 472889041579 := Nat.prime_eq_prime_of_dvd_pow hq prime_472889041579 hd
            subst q
            change (17 : ZMod 4962497602330027)^10494 ≠ 1
            reduce_mod_char
            decide

theorem prime_4986935372784737 : Nat.Prime 4986935372784737 := by
  apply lucas_primality 4986935372784737 (3 : ZMod 4986935372784737)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4986935372784737 - 1 = (2 : ℕ)^5 * ((7 : ℕ)^1 * ((19 : ℕ)^2 * ((31 : ℕ)^1 * ((43 : ℕ)^1 * ((73 : ℕ)^1 * ((107 : ℕ)^1 * ((5923 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 4986935372784737)^2493467686392368 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 4986935372784737)^712419338969248 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (3 : ZMod 4986935372784737)^262470282778144 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (3 : ZMod 4986935372784737)^160868882993056 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
              subst q
              change (3 : ZMod 4986935372784737)^115975241227552 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
                subst q
                change (3 : ZMod 4986935372784737)^68314183188832 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
                  subst q
                  change (3 : ZMod 4986935372784737)^46606872642848 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 5923 := Nat.prime_eq_prime_of_dvd_pow hq prime_5923 hd
                  subst q
                  change (3 : ZMod 4986935372784737)^841961062432 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_5035029816707161 : Nat.Prime 5035029816707161 := by
  apply lucas_primality 5035029816707161 (7 : ZMod 5035029816707161)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5035029816707161 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((367 : ℕ)^1 * ((118399 : ℕ)^1 * ((965621 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 5035029816707161)^2517514908353580 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 5035029816707161)^1678343272235720 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 5035029816707161)^1007005963341432 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 367 := Nat.prime_eq_prime_of_dvd_pow hq prime_367 hd
            subst q
            change (7 : ZMod 5035029816707161)^13719427293480 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 118399 := Nat.prime_eq_prime_of_dvd_pow hq prime_118399 hd
              subst q
              change (7 : ZMod 5035029816707161)^42525948840 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 965621 := Nat.prime_eq_prime_of_dvd_pow hq prime_965621 hd
              subst q
              change (7 : ZMod 5035029816707161)^5214291960 ≠ 1
              reduce_mod_char
              decide

theorem prime_5108443333890629 : Nat.Prime 5108443333890629 := by
  apply lucas_primality 5108443333890629 (2 : ZMod 5108443333890629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5108443333890629 - 1 = (2 : ℕ)^2 * ((2617 : ℕ)^1 * ((576217 : ℕ)^1 * ((846913 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5108443333890629)^2554221666945314 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 2617 := Nat.prime_eq_prime_of_dvd_pow hq prime_2617 hd
        subst q
        change (2 : ZMod 5108443333890629)^1952022672484 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 576217 := Nat.prime_eq_prime_of_dvd_pow hq prime_576217 hd
          subst q
          change (2 : ZMod 5108443333890629)^8865485284 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 846913 := Nat.prime_eq_prime_of_dvd_pow hq prime_846913 hd
          subst q
          change (2 : ZMod 5108443333890629)^6031839556 ≠ 1
          reduce_mod_char
          decide

theorem prime_5182746699759689 : Nat.Prime 5182746699759689 := by
  apply lucas_primality 5182746699759689 (3 : ZMod 5182746699759689)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5182746699759689 - 1 = (2 : ℕ)^3 * ((2972219 : ℕ)^1 * ((217966219 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 5182746699759689)^2591373349879844 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 2972219 := Nat.prime_eq_prime_of_dvd_pow hq prime_2972219 hd
        subst q
        change (3 : ZMod 5182746699759689)^1743729752 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 217966219 := Nat.prime_eq_prime_of_dvd_pow hq prime_217966219 hd
        subst q
        change (3 : ZMod 5182746699759689)^23777752 ≠ 1
        reduce_mod_char
        decide

theorem prime_5217510368570161 : Nat.Prime 5217510368570161 := by
  apply lucas_primality 5217510368570161 (17 : ZMod 5217510368570161)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5217510368570161 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((16103 : ℕ)^1 * ((1350035803 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 5217510368570161)^2608755184285080 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 5217510368570161)^1739170122856720 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (17 : ZMod 5217510368570161)^1043502073714032 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 16103 := Nat.prime_eq_prime_of_dvd_pow hq prime_16103 hd
            subst q
            change (17 : ZMod 5217510368570161)^324008592720 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1350035803 := Nat.prime_eq_prime_of_dvd_pow hq prime_1350035803 hd
            subst q
            change (17 : ZMod 5217510368570161)^3864720 ≠ 1
            reduce_mod_char
            decide

theorem prime_5257948522194371 : Nat.Prime 5257948522194371 := by
  apply lucas_primality 5257948522194371 (2 : ZMod 5257948522194371)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5257948522194371 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((17389 : ℕ)^1 * ((30237210433 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5257948522194371)^2628974261097185 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 5257948522194371)^1051589704438874 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17389 := Nat.prime_eq_prime_of_dvd_pow hq prime_17389 hd
          subst q
          change (2 : ZMod 5257948522194371)^302372104330 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 30237210433 := Nat.prime_eq_prime_of_dvd_pow hq prime_30237210433 hd
          subst q
          change (2 : ZMod 5257948522194371)^173890 ≠ 1
          reduce_mod_char
          decide

theorem prime_5328409115070949 : Nat.Prime 5328409115070949 := by
  apply lucas_primality 5328409115070949 (6 : ZMod 5328409115070949)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5328409115070949 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5110739 : ℕ)^1 * ((86882561 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 5328409115070949)^2664204557535474 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 5328409115070949)^1776136371690316 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5110739 := Nat.prime_eq_prime_of_dvd_pow hq prime_5110739 hd
          subst q
          change (6 : ZMod 5328409115070949)^1042590732 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 86882561 := Nat.prime_eq_prime_of_dvd_pow hq prime_86882561 hd
          subst q
          change (6 : ZMod 5328409115070949)^61328868 ≠ 1
          reduce_mod_char
          decide

theorem prime_5334057471375433 : Nat.Prime 5334057471375433 := by
  apply lucas_primality 5334057471375433 (10 : ZMod 5334057471375433)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5334057471375433 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((17 : ℕ)^1 * ((97 : ℕ)^1 * ((571 : ℕ)^1 * ((26226913 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 5334057471375433)^2667028735687716 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 5334057471375433)^1778019157125144 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (10 : ZMod 5334057471375433)^313768086551496 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
            subst q
            change (10 : ZMod 5334057471375433)^54990283210056 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 571 := Nat.prime_eq_prime_of_dvd_pow hq prime_571 hd
              subst q
              change (10 : ZMod 5334057471375433)^9341606779992 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 26226913 := Nat.prime_eq_prime_of_dvd_pow hq prime_26226913 hd
              subst q
              change (10 : ZMod 5334057471375433)^203381064 ≠ 1
              reduce_mod_char
              decide

theorem prime_5411082280083539 : Nat.Prime 5411082280083539 := by
  apply lucas_primality 5411082280083539 (2 : ZMod 5411082280083539)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5411082280083539 - 1 = (2 : ℕ)^1 * ((4091 : ℕ)^1 * ((146437 : ℕ)^1 * ((4516207 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5411082280083539)^2705541140041769 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 4091 := Nat.prime_eq_prime_of_dvd_pow hq prime_4091 hd
        subst q
        change (2 : ZMod 5411082280083539)^1322679608918 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 146437 := Nat.prime_eq_prime_of_dvd_pow hq prime_146437 hd
          subst q
          change (2 : ZMod 5411082280083539)^36951605674 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4516207 := Nat.prime_eq_prime_of_dvd_pow hq prime_4516207 hd
          subst q
          change (2 : ZMod 5411082280083539)^1198147534 ≠ 1
          reduce_mod_char
          decide

theorem prime_5489031744000017 : Nat.Prime 5489031744000017 := by
  apply lucas_primality 5489031744000017 (3 : ZMod 5489031744000017)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5489031744000017 - 1 = (2 : ℕ)^4 * ((343064484000001 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 5489031744000017)^2744515872000008 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 343064484000001 := Nat.prime_eq_prime_of_dvd_pow hq prime_343064484000001 hd
      subst q
      change (3 : ZMod 5489031744000017)^16 ≠ 1
      reduce_mod_char
      decide

theorem prime_5567914722008549 : Nat.Prime 5567914722008549 := by
  apply lucas_primality 5567914722008549 (2 : ZMod 5567914722008549)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5567914722008549 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^2 * ((13 : ℕ)^1 * ((73 : ℕ)^1 * ((607 : ℕ)^1 * ((3643 : ℕ)^1 * ((13537 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5567914722008549)^2783957361004274 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 5567914722008549)^795416388858364 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 5567914722008549)^428301132462196 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
            subst q
            change (2 : ZMod 5567914722008549)^76272804411076 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 607 := Nat.prime_eq_prime_of_dvd_pow hq prime_607 hd
              subst q
              change (2 : ZMod 5567914722008549)^9172841387164 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 3643 := Nat.prime_eq_prime_of_dvd_pow hq prime_3643 hd
                subst q
                change (2 : ZMod 5567914722008549)^1528387241836 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 13537 := Nat.prime_eq_prime_of_dvd_pow hq prime_13537 hd
                subst q
                change (2 : ZMod 5567914722008549)^411310831204 ≠ 1
                reduce_mod_char
                decide

theorem prime_5647740136496789 : Nat.Prime 5647740136496789 := by
  apply lucas_primality 5647740136496789 (2 : ZMod 5647740136496789)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5647740136496789 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((19 : ℕ)^1 * ((37 : ℕ)^1 * ((173 : ℕ)^1 * ((9829 : ℕ)^1 * ((107377 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5647740136496789)^2823870068248394 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 5647740136496789)^513430921499708 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 5647740136496789)^297249480868252 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
            subst q
            change (2 : ZMod 5647740136496789)^152641625310724 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
              subst q
              change (2 : ZMod 5647740136496789)^32645896742756 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 9829 := Nat.prime_eq_prime_of_dvd_pow hq prime_9829 hd
                subst q
                change (2 : ZMod 5647740136496789)^574599667972 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 107377 := Nat.prime_eq_prime_of_dvd_pow hq prime_107377 hd
                subst q
                change (2 : ZMod 5647740136496789)^52597298644 ≠ 1
                reduce_mod_char
                decide

theorem prime_5728516973659159 : Nat.Prime 5728516973659159 := by
  apply lucas_primality 5728516973659159 (3 : ZMod 5728516973659159)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5728516973659159 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((19 : ℕ)^2 * ((377820668359 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 5728516973659159)^2864258486829579 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 5728516973659159)^1909505657886386 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 5728516973659159)^818359567665594 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (3 : ZMod 5728516973659159)^301500893350482 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 377820668359 := Nat.prime_eq_prime_of_dvd_pow hq prime_377820668359 hd
            subst q
            change (3 : ZMod 5728516973659159)^15162 ≠ 1
            reduce_mod_char
            decide

theorem prime_5810254283800591 : Nat.Prime 5810254283800591 := by
  apply lucas_primality 5810254283800591 (6 : ZMod 5810254283800591)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5810254283800591 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((431 : ℕ)^1 * ((34566329251 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 5810254283800591)^2905127141900295 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 5810254283800591)^1936751427933530 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 5810254283800591)^1162050856760118 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (6 : ZMod 5810254283800591)^446942637215430 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 431 := Nat.prime_eq_prime_of_dvd_pow hq prime_431 hd
              subst q
              change (6 : ZMod 5810254283800591)^13480868407890 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 34566329251 := Nat.prime_eq_prime_of_dvd_pow hq prime_34566329251 hd
              subst q
              change (6 : ZMod 5810254283800591)^168090 ≠ 1
              reduce_mod_char
              decide

theorem prime_5892961181640647 : Nat.Prime 5892961181640647 := by
  apply lucas_primality 5892961181640647 (5 : ZMod 5892961181640647)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5892961181640647 - 1 = (2 : ℕ)^1 * ((1801 : ℕ)^1 * ((1636024758923 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 5892961181640647)^2946480590820323 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1801 := Nat.prime_eq_prime_of_dvd_pow hq prime_1801 hd
        subst q
        change (5 : ZMod 5892961181640647)^3272049517846 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1636024758923 := Nat.prime_eq_prime_of_dvd_pow hq prime_1636024758923 hd
        subst q
        change (5 : ZMod 5892961181640647)^3602 ≠ 1
        reduce_mod_char
        decide

theorem prime_5960719050834913 : Nat.Prime 5960719050834913 := by
  apply lucas_primality 5960719050834913 (5 : ZMod 5960719050834913)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5960719050834913 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((31 : ℕ)^1 * ((61 : ℕ)^1 * ((5923 : ℕ)^1 * ((60919 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 5960719050834913)^2980359525417456 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 5960719050834913)^1986906350278304 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 5960719050834913)^851531292976416 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (5 : ZMod 5960719050834913)^458516850064224 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
              subst q
              change (5 : ZMod 5960719050834913)^192281259704352 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
                subst q
                change (5 : ZMod 5960719050834913)^97716705751392 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 5923 := Nat.prime_eq_prime_of_dvd_pow hq prime_5923 hd
                  subst q
                  change (5 : ZMod 5960719050834913)^1006368234144 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 60919 := Nat.prime_eq_prime_of_dvd_pow hq prime_60919 hd
                  subst q
                  change (5 : ZMod 5960719050834913)^97846633248 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_5976646846618181 : Nat.Prime 5976646846618181 := by
  apply lucas_primality 5976646846618181 (2 : ZMod 5976646846618181)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5976646846618181 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((298832342330909 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 5976646846618181)^2988323423309090 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 5976646846618181)^1195329369323636 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 298832342330909 := Nat.prime_eq_prime_of_dvd_pow hq prime_298832342330909 hd
        subst q
        change (2 : ZMod 5976646846618181)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_6061320523197337 : Nat.Prime 6061320523197337 := by
  apply lucas_primality 6061320523197337 (7 : ZMod 6061320523197337)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6061320523197337 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((37 : ℕ)^1 * ((6825811399997 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 6061320523197337)^3030660261598668 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 6061320523197337)^2020440174399112 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (7 : ZMod 6061320523197337)^163819473599928 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 6825811399997 := Nat.prime_eq_prime_of_dvd_pow hq prime_6825811399997 hd
          subst q
          change (7 : ZMod 6061320523197337)^888 ≠ 1
          reduce_mod_char
          decide

theorem prime_6146991521173541 : Nat.Prime 6146991521173541 := by
  apply lucas_primality 6146991521173541 (2 : ZMod 6146991521173541)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6146991521173541 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((18079386826981 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6146991521173541)^3073495760586770 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 6146991521173541)^1229398304234708 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 6146991521173541)^361587736539620 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 18079386826981 := Nat.prime_eq_prime_of_dvd_pow hq prime_18079386826981 hd
          subst q
          change (2 : ZMod 6146991521173541)^340 ≠ 1
          reduce_mod_char
          decide

theorem prime_6233669215980937 : Nat.Prime 6233669215980937 := by
  apply lucas_primality 6233669215980937 (5 : ZMod 6233669215980937)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6233669215980937 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((47 : ℕ)^1 * ((37217 : ℕ)^1 * ((148488661 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 6233669215980937)^3116834607990468 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 6233669215980937)^2077889738660312 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (5 : ZMod 6233669215980937)^132631259914488 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 37217 := Nat.prime_eq_prime_of_dvd_pow hq prime_37217 hd
            subst q
            change (5 : ZMod 6233669215980937)^167495209608 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 148488661 := Nat.prime_eq_prime_of_dvd_pow hq prime_148488661 hd
            subst q
            change (5 : ZMod 6233669215980937)^41980776 ≠ 1
            reduce_mod_char
            decide

theorem prime_6321363049000007 : Nat.Prime 6321363049000007 := by
  apply lucas_primality 6321363049000007 (5 : ZMod 6321363049000007)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6321363049000007 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((29 : ℕ)^1 * ((1043839 : ℕ)^1 * ((14915959 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 6321363049000007)^3160681524500003 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 6321363049000007)^903051864142858 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (5 : ZMod 6321363049000007)^217978036172414 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1043839 := Nat.prime_eq_prime_of_dvd_pow hq prime_1043839 hd
            subst q
            change (5 : ZMod 6321363049000007)^6055879354 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 14915959 := Nat.prime_eq_prime_of_dvd_pow hq prime_14915959 hd
            subst q
            change (5 : ZMod 6321363049000007)^423798634 ≠ 1
            reduce_mod_char
            decide

theorem prime_6410082527866093 : Nat.Prime 6410082527866093 := by
  apply lucas_primality 6410082527866093 (2 : ZMod 6410082527866093)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6410082527866093 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((53 : ℕ)^1 * ((438206352739 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6410082527866093)^3205041263933046 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 6410082527866093)^2136694175955364 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 6410082527866093)^278699240342004 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
            subst q
            change (2 : ZMod 6410082527866093)^120944953355964 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 438206352739 := Nat.prime_eq_prime_of_dvd_pow hq prime_438206352739 hd
            subst q
            change (2 : ZMod 6410082527866093)^14628 ≠ 1
            reduce_mod_char
            decide

theorem prime_6499837226778673 : Nat.Prime 6499837226778673 := by
  apply lucas_primality 6499837226778673 (5 : ZMod 6499837226778673)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6499837226778673 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((2473 : ℕ)^1 * ((5023 : ℕ)^1 * ((1557313 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 6499837226778673)^3249918613389336 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 6499837226778673)^2166612408926224 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 6499837226778673)^928548175254096 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2473 := Nat.prime_eq_prime_of_dvd_pow hq prime_2473 hd
            subst q
            change (5 : ZMod 6499837226778673)^2628320754864 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 5023 := Nat.prime_eq_prime_of_dvd_pow hq prime_5023 hd
              subst q
              change (5 : ZMod 6499837226778673)^1294014976464 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1557313 := Nat.prime_eq_prime_of_dvd_pow hq prime_1557313 hd
              subst q
              change (5 : ZMod 6499837226778673)^4173751344 ≠ 1
              reduce_mod_char
              decide

theorem prime_6590636786811197 : Nat.Prime 6590636786811197 := by
  apply lucas_primality 6590636786811197 (2 : ZMod 6590636786811197)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6590636786811197 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((19 : ℕ)^1 * ((67 : ℕ)^1 * ((397 : ℕ)^1 * ((2467 : ℕ)^1 * ((188791 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6590636786811197)^3295318393405598 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 6590636786811197)^941519540973028 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 6590636786811197)^346875620358484 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
            subst q
            change (2 : ZMod 6590636786811197)^98367713235988 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 397 := Nat.prime_eq_prime_of_dvd_pow hq prime_397 hd
              subst q
              change (2 : ZMod 6590636786811197)^16601100218668 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 2467 := Nat.prime_eq_prime_of_dvd_pow hq prime_2467 hd
                subst q
                change (2 : ZMod 6590636786811197)^2671518762388 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 188791 := Nat.prime_eq_prime_of_dvd_pow hq prime_188791 hd
                subst q
                change (2 : ZMod 6590636786811197)^34909697956 ≠ 1
                reduce_mod_char
                decide

theorem prime_6682490916222113 : Nat.Prime 6682490916222113 := by
  apply lucas_primality 6682490916222113 (3 : ZMod 6682490916222113)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6682490916222113 - 1 = (2 : ℕ)^5 * ((83 : ℕ)^1 * ((163859 : ℕ)^1 * ((15354653 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 6682490916222113)^3341245458111056 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
        subst q
        change (3 : ZMod 6682490916222113)^80511938749664 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 163859 := Nat.prime_eq_prime_of_dvd_pow hq prime_163859 hd
          subst q
          change (3 : ZMod 6682490916222113)^40781958368 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 15354653 := Nat.prime_eq_prime_of_dvd_pow hq prime_15354653 hd
          subst q
          change (3 : ZMod 6682490916222113)^435209504 ≠ 1
          reduce_mod_char
          decide

theorem prime_6733662777345641 : Nat.Prime 6733662777345641 := by
  apply lucas_primality 6733662777345641 (3 : ZMod 6733662777345641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6733662777345641 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((43 : ℕ)^1 * ((871037 : ℕ)^1 * ((4494551 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 6733662777345641)^3366831388672820 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 6733662777345641)^1346732555469128 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (3 : ZMod 6733662777345641)^156596808775480 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 871037 := Nat.prime_eq_prime_of_dvd_pow hq prime_871037 hd
            subst q
            change (3 : ZMod 6733662777345641)^7730627720 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 4494551 := Nat.prime_eq_prime_of_dvd_pow hq prime_4494551 hd
            subst q
            change (3 : ZMod 6733662777345641)^1498183640 ≠ 1
            reduce_mod_char
            decide

theorem prime_6775409390765651 : Nat.Prime 6775409390765651 := by
  apply lucas_primality 6775409390765651 (10 : ZMod 6775409390765651)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6775409390765651 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((17 : ℕ)^1 * ((41 : ℕ)^1 * ((495893 : ℕ)^1 * ((392053 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 6775409390765651)^3387704695382825 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (10 : ZMod 6775409390765651)^1355081878153130 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (10 : ZMod 6775409390765651)^398553493574450 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (10 : ZMod 6775409390765651)^165253887579650 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 495893 := Nat.prime_eq_prime_of_dvd_pow hq prime_495893 hd
              subst q
              change (10 : ZMod 6775409390765651)^13663047050 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 392053 := Nat.prime_eq_prime_of_dvd_pow hq prime_392053 hd
              subst q
              change (10 : ZMod 6775409390765651)^17281871050 ≠ 1
              reduce_mod_char
              decide

theorem prime_6860644332271427 : Nat.Prime 6860644332271427 := by
  apply lucas_primality 6860644332271427 (2 : ZMod 6860644332271427)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6860644332271427 - 1 = (2 : ℕ)^1 * ((41 : ℕ)^1 * ((9013 : ℕ)^1 * ((119297 : ℕ)^1 * ((77813 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 6860644332271427)^3430322166135713 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
        subst q
        change (2 : ZMod 6860644332271427)^167332788591986 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 9013 := Nat.prime_eq_prime_of_dvd_pow hq prime_9013 hd
          subst q
          change (2 : ZMod 6860644332271427)^761194311802 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 119297 := Nat.prime_eq_prime_of_dvd_pow hq prime_119297 hd
            subst q
            change (2 : ZMod 6860644332271427)^57508942658 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 77813 := Nat.prime_eq_prime_of_dvd_pow hq prime_77813 hd
            subst q
            change (2 : ZMod 6860644332271427)^88168356602 ≠ 1
            reduce_mod_char
            decide

theorem prime_6869402054004751 : Nat.Prime 6869402054004751 := by
  apply lucas_primality 6869402054004751 (17 : ZMod 6869402054004751)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6869402054004751 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^3 * ((13 : ℕ)^1 * ((971 : ℕ)^1 * ((725596351 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 6869402054004751)^3434701027002375 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 6869402054004751)^2289800684668250 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (17 : ZMod 6869402054004751)^1373880410800950 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (17 : ZMod 6869402054004751)^528415542615750 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 971 := Nat.prime_eq_prime_of_dvd_pow hq prime_971 hd
              subst q
              change (17 : ZMod 6869402054004751)^7074564422250 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 725596351 := Nat.prime_eq_prime_of_dvd_pow hq prime_725596351 hd
              subst q
              change (17 : ZMod 6869402054004751)^9467250 ≠ 1
              reduce_mod_char
              decide

theorem prime_6964478817623221 : Nat.Prime 6964478817623221 := by
  apply lucas_primality 6964478817623221 (6 : ZMod 6964478817623221)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 6964478817623221 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((37 : ℕ)^1 * ((773 : ℕ)^1 * ((4058412187 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 6964478817623221)^3482239408811610 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 6964478817623221)^2321492939207740 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 6964478817623221)^1392895763524644 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
            subst q
            change (6 : ZMod 6964478817623221)^188229157233060 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 773 := Nat.prime_eq_prime_of_dvd_pow hq prime_773 hd
              subst q
              change (6 : ZMod 6964478817623221)^9009675055140 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 4058412187 := Nat.prime_eq_prime_of_dvd_pow hq prime_4058412187 hd
              subst q
              change (6 : ZMod 6964478817623221)^1716060 ≠ 1
              reduce_mod_char
              decide

theorem prime_7060649661739589 : Nat.Prime 7060649661739589 := by
  apply lucas_primality 7060649661739589 (2 : ZMod 7060649661739589)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7060649661739589 - 1 = (2 : ℕ)^2 * ((229 : ℕ)^1 * ((7708132818493 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 7060649661739589)^3530324830869794 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 229 := Nat.prime_eq_prime_of_dvd_pow hq prime_229 hd
        subst q
        change (2 : ZMod 7060649661739589)^30832531273972 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7708132818493 := Nat.prime_eq_prime_of_dvd_pow hq prime_7708132818493 hd
        subst q
        change (2 : ZMod 7060649661739589)^916 ≠ 1
        reduce_mod_char
        decide

theorem prime_7061963044571429 : Nat.Prime 7061963044571429 := by
  apply lucas_primality 7061963044571429 (2 : ZMod 7061963044571429)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7061963044571429 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^2 * ((41 : ℕ)^1 * ((5639 : ℕ)^1 * ((12391 : ℕ)^1 * ((12577 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 7061963044571429)^3530981522285714 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 7061963044571429)^1008851863510204 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (2 : ZMod 7061963044571429)^172243001087108 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 5639 := Nat.prime_eq_prime_of_dvd_pow hq prime_5639 hd
            subst q
            change (2 : ZMod 7061963044571429)^1252343153852 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 12391 := Nat.prime_eq_prime_of_dvd_pow hq prime_12391 hd
              subst q
              change (2 : ZMod 7061963044571429)^569926805308 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 12577 := Nat.prime_eq_prime_of_dvd_pow hq prime_12577 hd
              subst q
              change (2 : ZMod 7061963044571429)^561498214564 ≠ 1
              reduce_mod_char
              decide

theorem prime_7157924635221413 : Nat.Prime 7157924635221413 := by
  apply lucas_primality 7157924635221413 (2 : ZMod 7157924635221413)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7157924635221413 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((23 : ℕ)^1 * ((29 : ℕ)^1 * ((127 : ℕ)^1 * ((1625003209 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 7157924635221413)^3578962317610706 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 7157924635221413)^550609587324724 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 7157924635221413)^311214114574844 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (2 : ZMod 7157924635221413)^246824987421428 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
              subst q
              change (2 : ZMod 7157924635221413)^56361611300956 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1625003209 := Nat.prime_eq_prime_of_dvd_pow hq prime_1625003209 hd
              subst q
              change (2 : ZMod 7157924635221413)^4404868 ≠ 1
              reduce_mod_char
              decide

theorem prime_7256313856000067 : Nat.Prime 7256313856000067 := by
  apply lucas_primality 7256313856000067 (5 : ZMod 7256313856000067)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7256313856000067 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((67 : ℕ)^1 * ((378682489093 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 7256313856000067)^3628156928000033 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 7256313856000067)^659664896000006 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (5 : ZMod 7256313856000067)^558177988923082 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
            subst q
            change (5 : ZMod 7256313856000067)^108303191880598 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 378682489093 := Nat.prime_eq_prime_of_dvd_pow hq prime_378682489093 hd
            subst q
            change (5 : ZMod 7256313856000067)^19162 ≠ 1
            reduce_mod_char
            decide

theorem prime_7355827511386667 : Nat.Prime 7355827511386667 := by
  apply lucas_primality 7355827511386667 (5 : ZMod 7355827511386667)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7355827511386667 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((9929 : ℕ)^1 * ((28493951329 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 7355827511386667)^3677913755693333 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (5 : ZMod 7355827511386667)^565832885491282 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 9929 := Nat.prime_eq_prime_of_dvd_pow hq prime_9929 hd
          subst q
          change (5 : ZMod 7355827511386667)^740842734554 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 28493951329 := Nat.prime_eq_prime_of_dvd_pow hq prime_28493951329 hd
          subst q
          change (5 : ZMod 7355827511386667)^258154 ≠ 1
          reduce_mod_char
          decide

theorem prime_7456475858388551 : Nat.Prime 7456475858388551 := by
  apply lucas_primality 7456475858388551 (7 : ZMod 7456475858388551)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7456475858388551 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((7 : ℕ)^1 * ((3812623 : ℕ)^1 * ((5587811 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 7456475858388551)^3728237929194275 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 7456475858388551)^1491295171677710 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 7456475858388551)^1065210836912650 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3812623 := Nat.prime_eq_prime_of_dvd_pow hq prime_3812623 hd
            subst q
            change (7 : ZMod 7456475858388551)^1955733850 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 5587811 := Nat.prime_eq_prime_of_dvd_pow hq prime_5587811 hd
            subst q
            change (7 : ZMod 7456475858388551)^1334418050 ≠ 1
            reduce_mod_char
            decide

theorem prime_7558269224026267 : Nat.Prime 7558269224026267 := by
  apply lucas_primality 7558269224026267 (5 : ZMod 7558269224026267)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7558269224026267 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((71 : ℕ)^1 * ((1971379557649 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 7558269224026267)^3779134612013133 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 7558269224026267)^2519423074675422 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
          subst q
          change (5 : ZMod 7558269224026267)^106454496113046 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1971379557649 := Nat.prime_eq_prime_of_dvd_pow hq prime_1971379557649 hd
          subst q
          change (5 : ZMod 7558269224026267)^3834 ≠ 1
          reduce_mod_char
          decide

theorem prime_7661218005651491 : Nat.Prime 7661218005651491 := by
  apply lucas_primality 7661218005651491 (6 : ZMod 7661218005651491)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7661218005651491 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((109445971509307 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 7661218005651491)^3830609002825745 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 7661218005651491)^1532243601130298 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 7661218005651491)^1094459715093070 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 109445971509307 := Nat.prime_eq_prime_of_dvd_pow hq prime_109445971509307 hd
          subst q
          change (6 : ZMod 7661218005651491)^70 ≠ 1
          reduce_mod_char
          decide

theorem prime_7761180154733587 : Nat.Prime 7761180154733587 := by
  apply lucas_primality 7761180154733587 (2 : ZMod 7761180154733587)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7761180154733587 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((235007 : ℕ)^1 * ((262105673 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 7761180154733587)^3880590077366793 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 7761180154733587)^2587060051577862 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 7761180154733587)^1108740022104798 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 235007 := Nat.prime_eq_prime_of_dvd_pow hq prime_235007 hd
            subst q
            change (2 : ZMod 7761180154733587)^33025314798 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 262105673 := Nat.prime_eq_prime_of_dvd_pow hq prime_262105673 hd
            subst q
            change (2 : ZMod 7761180154733587)^29610882 ≠ 1
            reduce_mod_char
            decide

theorem prime_7765332671265647 : Nat.Prime 7765332671265647 := by
  apply lucas_primality 7765332671265647 (5 : ZMod 7765332671265647)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7765332671265647 - 1 = (2 : ℕ)^1 * ((1217947 : ℕ)^1 * ((3187877909 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 7765332671265647)^3882666335632823 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1217947 := Nat.prime_eq_prime_of_dvd_pow hq prime_1217947 hd
        subst q
        change (5 : ZMod 7765332671265647)^6375755818 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3187877909 := Nat.prime_eq_prime_of_dvd_pow hq prime_3187877909 hd
        subst q
        change (5 : ZMod 7765332671265647)^2435894 ≠ 1
        reduce_mod_char
        decide

theorem prime_7870623759839327 : Nat.Prime 7870623759839327 := by
  apply lucas_primality 7870623759839327 (5 : ZMod 7870623759839327)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7870623759839327 - 1 = (2 : ℕ)^1 * ((1951 : ℕ)^1 * ((2017074259313 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 7870623759839327)^3935311879919663 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1951 := Nat.prime_eq_prime_of_dvd_pow hq prime_1951 hd
        subst q
        change (5 : ZMod 7870623759839327)^4034148518626 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2017074259313 := Nat.prime_eq_prime_of_dvd_pow hq prime_2017074259313 hd
        subst q
        change (5 : ZMod 7870623759839327)^3902 ≠ 1
        reduce_mod_char
        decide

theorem prime_7977101881632151 : Nat.Prime 7977101881632151 := by
  apply lucas_primality 7977101881632151 (3 : ZMod 7977101881632151)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 7977101881632151 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((1973 : ℕ)^1 * ((26954221597 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 7977101881632151)^3988550940816075 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 7977101881632151)^2659033960544050 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 7977101881632151)^1595420376326430 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1973 := Nat.prime_eq_prime_of_dvd_pow hq prime_1973 hd
            subst q
            change (3 : ZMod 7977101881632151)^4043133239550 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 26954221597 := Nat.prime_eq_prime_of_dvd_pow hq prime_26954221597 hd
            subst q
            change (3 : ZMod 7977101881632151)^295950 ≠ 1
            reduce_mod_char
            decide

theorem prime_8084777718513677 : Nat.Prime 8084777718513677 := by
  apply lucas_primality 8084777718513677 (2 : ZMod 8084777718513677)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8084777718513677 - 1 = (2 : ℕ)^2 * ((199 : ℕ)^1 * ((10156755927781 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8084777718513677)^4042388859256838 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 199 := Nat.prime_eq_prime_of_dvd_pow hq prime_199 hd
        subst q
        change (2 : ZMod 8084777718513677)^40627023711124 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 10156755927781 := Nat.prime_eq_prime_of_dvd_pow hq prime_10156755927781 hd
        subst q
        change (2 : ZMod 8084777718513677)^796 ≠ 1
        reduce_mod_char
        decide

theorem prime_8193662024284811 : Nat.Prime 8193662024284811 := by
  apply lucas_primality 8193662024284811 (10 : ZMod 8193662024284811)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8193662024284811 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((819366202428481 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 8193662024284811)^4096831012142405 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (10 : ZMod 8193662024284811)^1638732404856962 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 819366202428481 := Nat.prime_eq_prime_of_dvd_pow hq prime_819366202428481 hd
        subst q
        change (10 : ZMod 8193662024284811)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_8303765625000007 : Nat.Prime 8303765625000007 := by
  apply lucas_primality 8303765625000007 (3 : ZMod 8303765625000007)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8303765625000007 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((1061 : ℕ)^1 * ((1709 : ℕ)^1 * ((109035607 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 8303765625000007)^4151882812500003 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 8303765625000007)^2767921875000002 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 8303765625000007)^1186252232142858 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1061 := Nat.prime_eq_prime_of_dvd_pow hq prime_1061 hd
            subst q
            change (3 : ZMod 8303765625000007)^7826357799246 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1709 := Nat.prime_eq_prime_of_dvd_pow hq prime_1709 hd
              subst q
              change (3 : ZMod 8303765625000007)^4858844719134 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 109035607 := Nat.prime_eq_prime_of_dvd_pow hq prime_109035607 hd
              subst q
              change (3 : ZMod 8303765625000007)^76156458 ≠ 1
              reduce_mod_char
              decide

theorem prime_8415099419290337 : Nat.Prime 8415099419290337 := by
  apply lucas_primality 8415099419290337 (3 : ZMod 8415099419290337)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8415099419290337 - 1 = (2 : ℕ)^5 * ((23 : ℕ)^1 * ((227873 : ℕ)^1 * ((50175137 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 8415099419290337)^4207549709645168 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (3 : ZMod 8415099419290337)^365873887795232 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 227873 := Nat.prime_eq_prime_of_dvd_pow hq prime_227873 hd
          subst q
          change (3 : ZMod 8415099419290337)^36928900832 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 50175137 := Nat.prime_eq_prime_of_dvd_pow hq prime_50175137 hd
          subst q
          change (3 : ZMod 8415099419290337)^167714528 ≠ 1
          reduce_mod_char
          decide

theorem prime_8527674378686471 : Nat.Prime 8527674378686471 := by
  apply lucas_primality 8527674378686471 (7 : ZMod 8527674378686471)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8527674378686471 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((53 : ℕ)^1 * ((2298564522557 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 8527674378686471)^4263837189343235 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 8527674378686471)^1705534875737294 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 8527674378686471)^1218239196955210 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
            subst q
            change (7 : ZMod 8527674378686471)^160899516578990 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2298564522557 := Nat.prime_eq_prime_of_dvd_pow hq prime_2298564522557 hd
            subst q
            change (7 : ZMod 8527674378686471)^3710 ≠ 1
            reduce_mod_char
            decide

theorem prime_8641501547944367 : Nat.Prime 8641501547944367 := by
  apply lucas_primality 8641501547944367 (5 : ZMod 8641501547944367)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8641501547944367 - 1 = (2 : ℕ)^1 * ((499 : ℕ)^1 * ((8658819186317 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 8641501547944367)^4320750773972183 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 499 := Nat.prime_eq_prime_of_dvd_pow hq prime_499 hd
        subst q
        change (5 : ZMod 8641501547944367)^17317638372634 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 8658819186317 := Nat.prime_eq_prime_of_dvd_pow hq prime_8658819186317 hd
        subst q
        change (5 : ZMod 8641501547944367)^998 ≠ 1
        reduce_mod_char
        decide

theorem prime_8672046318279853 : Nat.Prime 8672046318279853 := by
  apply lucas_primality 8672046318279853 (2 : ZMod 8672046318279853)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8672046318279853 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((139 : ℕ)^1 * ((226046458093 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8672046318279853)^4336023159139926 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 8672046318279853)^2890682106093284 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 8672046318279853)^377045492099124 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
            subst q
            change (2 : ZMod 8672046318279853)^62388822433668 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 226046458093 := Nat.prime_eq_prime_of_dvd_pow hq prime_226046458093 hd
            subst q
            change (2 : ZMod 8672046318279853)^38364 ≠ 1
            reduce_mod_char
            decide

theorem prime_8756592045368899 : Nat.Prime 8756592045368899 := by
  apply lucas_primality 8756592045368899 (2 : ZMod 8756592045368899)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8756592045368899 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((9403 : ℕ)^1 * ((155209189361 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8756592045368899)^4378296022684449 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 8756592045368899)^2918864015122966 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 9403 := Nat.prime_eq_prime_of_dvd_pow hq prime_9403 hd
          subst q
          change (2 : ZMod 8756592045368899)^931255136166 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 155209189361 := Nat.prime_eq_prime_of_dvd_pow hq prime_155209189361 hd
          subst q
          change (2 : ZMod 8756592045368899)^56418 ≠ 1
          reduce_mod_char
          decide

theorem prime_8872957063140637 : Nat.Prime 8872957063140637 := by
  apply lucas_primality 8872957063140637 (2 : ZMod 8872957063140637)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8872957063140637 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((2069 : ℕ)^1 * ((357377036537 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 8872957063140637)^4436478531570318 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 8872957063140637)^2957652354380212 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2069 := Nat.prime_eq_prime_of_dvd_pow hq prime_2069 hd
          subst q
          change (2 : ZMod 8872957063140637)^4288524438444 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 357377036537 := Nat.prime_eq_prime_of_dvd_pow hq prime_357377036537 hd
          subst q
          change (2 : ZMod 8872957063140637)^24828 ≠ 1
          reduce_mod_char
          decide

theorem prime_8990607867641863 : Nat.Prime 8990607867641863 := by
  apply lucas_primality 8990607867641863 (5 : ZMod 8990607867641863)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8990607867641863 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((2483219 : ℕ)^1 * ((7836679 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 8990607867641863)^4495303933820931 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 8990607867641863)^2996869289213954 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 8990607867641863)^1284372552520266 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (5 : ZMod 8990607867641863)^817327987967442 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 2483219 := Nat.prime_eq_prime_of_dvd_pow hq prime_2483219 hd
              subst q
              change (5 : ZMod 8990607867641863)^3620545698 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 7836679 := Nat.prime_eq_prime_of_dvd_pow hq prime_7836679 hd
              subst q
              change (5 : ZMod 8990607867641863)^1147247178 ≠ 1
              reduce_mod_char
              decide

theorem prime_9109555799784059 : Nat.Prime 9109555799784059 := by
  apply lucas_primality 9109555799784059 (2 : ZMod 9109555799784059)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9109555799784059 - 1 = (2 : ℕ)^1 * ((4554777899892029 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9109555799784059)^4554777899892029 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 4554777899892029 := Nat.prime_eq_prime_of_dvd_pow hq prime_4554777899892029 hd
      subst q
      change (2 : ZMod 9109555799784059)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_9229812275335753 : Nat.Prime 9229812275335753 := by
  apply lucas_primality 9229812275335753 (5 : ZMod 9229812275335753)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9229812275335753 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((211 : ℕ)^1 * ((2473 : ℕ)^1 * ((7027 : ℕ)^1 * ((34961 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 9229812275335753)^4614906137667876 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 9229812275335753)^3076604091778584 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 211 := Nat.prime_eq_prime_of_dvd_pow hq prime_211 hd
          subst q
          change (5 : ZMod 9229812275335753)^43743186139032 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2473 := Nat.prime_eq_prime_of_dvd_pow hq prime_2473 hd
            subst q
            change (5 : ZMod 9229812275335753)^3732233026824 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 7027 := Nat.prime_eq_prime_of_dvd_pow hq prime_7027 hd
              subst q
              change (5 : ZMod 9229812275335753)^1313478337176 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 34961 := Nat.prime_eq_prime_of_dvd_pow hq prime_34961 hd
              subst q
              change (5 : ZMod 9229812275335753)^264003097032 ≠ 1
              reduce_mod_char
              decide

theorem prime_9351388785251273 : Nat.Prime 9351388785251273 := by
  apply lucas_primality 9351388785251273 (3 : ZMod 9351388785251273)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9351388785251273 - 1 = (2 : ℕ)^3 * ((19 : ℕ)^1 * ((2963 : ℕ)^1 * ((20763514897 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 9351388785251273)^4675694392625636 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (3 : ZMod 9351388785251273)^492178357118488 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2963 := Nat.prime_eq_prime_of_dvd_pow hq prime_2963 hd
          subst q
          change (3 : ZMod 9351388785251273)^3156054264344 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 20763514897 := Nat.prime_eq_prime_of_dvd_pow hq prime_20763514897 hd
          subst q
          change (3 : ZMod 9351388785251273)^450376 ≠ 1
          reduce_mod_char
          decide

theorem prime_9474296896000007 : Nat.Prime 9474296896000007 := by
  apply lucas_primality 9474296896000007 (5 : ZMod 9474296896000007)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9474296896000007 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((59 : ℕ)^1 * ((11470093094431 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 9474296896000007)^4737148448000003 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 9474296896000007)^1353470985142858 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (5 : ZMod 9474296896000007)^160581303322034 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11470093094431 := Nat.prime_eq_prime_of_dvd_pow hq prime_11470093094431 hd
          subst q
          change (5 : ZMod 9474296896000007)^826 ≠ 1
          reduce_mod_char
          decide

theorem prime_9598548249896779 : Nat.Prime 9598548249896779 := by
  apply lucas_primality 9598548249896779 (10 : ZMod 9598548249896779)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9598548249896779 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^6 * ((457 : ℕ)^1 * ((719 : ℕ)^1 * ((20035627 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 9598548249896779)^4799274124948389 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 9598548249896779)^3199516083298926 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 457 := Nat.prime_eq_prime_of_dvd_pow hq prime_457 hd
          subst q
          change (10 : ZMod 9598548249896779)^21003387855354 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 719 := Nat.prime_eq_prime_of_dvd_pow hq prime_719 hd
            subst q
            change (10 : ZMod 9598548249896779)^13349858483862 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 20035627 := Nat.prime_eq_prime_of_dvd_pow hq prime_20035627 hd
            subst q
            change (10 : ZMod 9598548249896779)^479074014 ≠ 1
            reduce_mod_char
            decide

theorem prime_9715785465491857 : Nat.Prime 9715785465491857 := by
  apply lucas_primality 9715785465491857 (7 : ZMod 9715785465491857)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9715785465491857 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^6 * ((97 : ℕ)^6)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 9715785465491857)^4857892732745928 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 9715785465491857)^3238595155163952 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
        subst q
        change (7 : ZMod 9715785465491857)^100162736757648 ≠ 1
        reduce_mod_char
        decide

theorem prime_9724154565432409 : Nat.Prime 9724154565432409 := by
  apply lucas_primality 9724154565432409 (13 : ZMod 9724154565432409)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9724154565432409 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((7591 : ℕ)^1 * ((25523 : ℕ)^1 * ((2091269 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 9724154565432409)^4862077282716204 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 9724154565432409)^3241384855144136 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7591 := Nat.prime_eq_prime_of_dvd_pow hq prime_7591 hd
          subst q
          change (13 : ZMod 9724154565432409)^1281011008488 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 25523 := Nat.prime_eq_prime_of_dvd_pow hq prime_25523 hd
            subst q
            change (13 : ZMod 9724154565432409)^380995751496 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2091269 := Nat.prime_eq_prime_of_dvd_pow hq prime_2091269 hd
            subst q
            change (13 : ZMod 9724154565432409)^4649882232 ≠ 1
            reduce_mod_char
            decide

theorem prime_9851127637605421 : Nat.Prime 9851127637605421 := by
  apply lucas_primality 9851127637605421 (2 : ZMod 9851127637605421)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9851127637605421 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((3025331 : ℕ)^1 * ((54270247 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9851127637605421)^4925563818802710 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 9851127637605421)^3283709212535140 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 9851127637605421)^1970225527521084 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3025331 := Nat.prime_eq_prime_of_dvd_pow hq prime_3025331 hd
            subst q
            change (2 : ZMod 9851127637605421)^3256214820 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 54270247 := Nat.prime_eq_prime_of_dvd_pow hq prime_54270247 hd
            subst q
            change (2 : ZMod 9851127637605421)^181519860 ≠ 1
            reduce_mod_char
            decide

theorem prime_9979479338254379 : Nat.Prime 9979479338254379 := by
  apply lucas_primality 9979479338254379 (2 : ZMod 9979479338254379)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9979479338254379 - 1 = (2 : ℕ)^1 * ((2897 : ℕ)^1 * ((55837 : ℕ)^1 * ((30846601 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 9979479338254379)^4989739669127189 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 2897 := Nat.prime_eq_prime_of_dvd_pow hq prime_2897 hd
        subst q
        change (2 : ZMod 9979479338254379)^3444763320074 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 55837 := Nat.prime_eq_prime_of_dvd_pow hq prime_55837 hd
          subst q
          change (2 : ZMod 9979479338254379)^178725206194 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 30846601 := Nat.prime_eq_prime_of_dvd_pow hq prime_30846601 hd
          subst q
          change (2 : ZMod 9979479338254379)^323519578 ≠ 1
          reduce_mod_char
          decide

theorem prime_10109221616390647 : Nat.Prime 10109221616390647 := by
  apply lucas_primality 10109221616390647 (6 : ZMod 10109221616390647)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10109221616390647 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((14731 : ℕ)^1 * ((114375824411 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 10109221616390647)^5054610808195323 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 10109221616390647)^3369740538796882 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 14731 := Nat.prime_eq_prime_of_dvd_pow hq prime_14731 hd
          subst q
          change (6 : ZMod 10109221616390647)^686254946466 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 114375824411 := Nat.prime_eq_prime_of_dvd_pow hq prime_114375824411 hd
          subst q
          change (6 : ZMod 10109221616390647)^88386 ≠ 1
          reduce_mod_char
          decide

theorem prime_10162199406732379 : Nat.Prime 10162199406732379 := by
  apply lucas_primality 10162199406732379 (3 : ZMod 10162199406732379)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10162199406732379 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((37 : ℕ)^1 * ((89923 : ℕ)^1 * ((509054113 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 10162199406732379)^5081099703366189 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 10162199406732379)^3387399802244126 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (3 : ZMod 10162199406732379)^274654038019794 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 89923 := Nat.prime_eq_prime_of_dvd_pow hq prime_89923 hd
            subst q
            change (3 : ZMod 10162199406732379)^113010013086 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 509054113 := Nat.prime_eq_prime_of_dvd_pow hq prime_509054113 hd
            subst q
            change (3 : ZMod 10162199406732379)^19962906 ≠ 1
            reduce_mod_char
            decide

theorem prime_10240366498532437 : Nat.Prime 10240366498532437 := by
  apply lucas_primality 10240366498532437 (6 : ZMod 10240366498532437)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10240366498532437 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((121909124982529 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 10240366498532437)^5120183249266218 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 10240366498532437)^3413455499510812 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 10240366498532437)^1462909499790348 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 121909124982529 := Nat.prime_eq_prime_of_dvd_pow hq prime_121909124982529 hd
          subst q
          change (6 : ZMod 10240366498532437)^84 ≠ 1
          reduce_mod_char
          decide

theorem prime_10372926089039047 : Nat.Prime 10372926089039047 := by
  apply lucas_primality 10372926089039047 (3 : ZMod 10372926089039047)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10372926089039047 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((659 : ℕ)^1 * ((3449 : ℕ)^1 * ((58509727 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 10372926089039047)^5186463044519523 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 10372926089039047)^3457642029679682 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 10372926089039047)^797917391464542 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 659 := Nat.prime_eq_prime_of_dvd_pow hq prime_659 hd
            subst q
            change (3 : ZMod 10372926089039047)^15740403776994 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 3449 := Nat.prime_eq_prime_of_dvd_pow hq prime_3449 hd
              subst q
              change (3 : ZMod 10372926089039047)^3007516987254 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 58509727 := Nat.prime_eq_prime_of_dvd_pow hq prime_58509727 hd
              subst q
              change (3 : ZMod 10372926089039047)^177285498 ≠ 1
              reduce_mod_char
              decide

theorem prime_10506912570445829 : Nat.Prime 10506912570445829 := by
  apply lucas_primality 10506912570445829 (2 : ZMod 10506912570445829)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10506912570445829 - 1 = (2 : ℕ)^2 * ((1049 : ℕ)^1 * ((2504030641193 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 10506912570445829)^5253456285222914 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1049 := Nat.prime_eq_prime_of_dvd_pow hq prime_1049 hd
        subst q
        change (2 : ZMod 10506912570445829)^10016122564772 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2504030641193 := Nat.prime_eq_prime_of_dvd_pow hq prime_2504030641193 hd
        subst q
        change (2 : ZMod 10506912570445829)^4196 ≠ 1
        reduce_mod_char
        decide

theorem prime_10642338203800763 : Nat.Prime 10642338203800763 := by
  apply lucas_primality 10642338203800763 (2 : ZMod 10642338203800763)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10642338203800763 - 1 = (2 : ℕ)^1 * ((20213233 : ℕ)^1 * ((263251757 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 10642338203800763)^5321169101900381 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 20213233 := Nat.prime_eq_prime_of_dvd_pow hq prime_20213233 hd
        subst q
        change (2 : ZMod 10642338203800763)^526503514 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 263251757 := Nat.prime_eq_prime_of_dvd_pow hq prime_263251757 hd
        subst q
        change (2 : ZMod 10642338203800763)^40426466 ≠ 1
        reduce_mod_char
        decide

theorem prime_10779215329000007 : Nat.Prime 10779215329000007 := by
  apply lucas_primality 10779215329000007 (10 : ZMod 10779215329000007)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10779215329000007 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((241 : ℕ)^1 * ((3413 : ℕ)^1 * ((936064513 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 10779215329000007)^5389607664500003 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (10 : ZMod 10779215329000007)^1539887904142858 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 241 := Nat.prime_eq_prime_of_dvd_pow hq prime_241 hd
          subst q
          change (10 : ZMod 10779215329000007)^44727034560166 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3413 := Nat.prime_eq_prime_of_dvd_pow hq prime_3413 hd
            subst q
            change (10 : ZMod 10779215329000007)^3158281666862 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 936064513 := Nat.prime_eq_prime_of_dvd_pow hq prime_936064513 hd
            subst q
            change (10 : ZMod 10779215329000007)^11515462 ≠ 1
            reduce_mod_char
            decide

theorem prime_10917556365126371 : Nat.Prime 10917556365126371 := by
  apply lucas_primality 10917556365126371 (2 : ZMod 10917556365126371)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 10917556365126371 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((583697 : ℕ)^1 * ((110024413 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 10917556365126371)^5458778182563185 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 10917556365126371)^2183511273025274 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 10917556365126371)^642209197948610 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 583697 := Nat.prime_eq_prime_of_dvd_pow hq prime_583697 hd
            subst q
            change (2 : ZMod 10917556365126371)^18704150210 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 110024413 := Nat.prime_eq_prime_of_dvd_pow hq prime_110024413 hd
            subst q
            change (2 : ZMod 10917556365126371)^99228490 ≠ 1
            reduce_mod_char
            decide

theorem prime_11057373810786419 : Nat.Prime 11057373810786419 := by
  apply lucas_primality 11057373810786419 (2 : ZMod 11057373810786419)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11057373810786419 - 1 = (2 : ℕ)^1 * ((1811731 : ℕ)^1 * ((3051604739 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 11057373810786419)^5528686905393209 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1811731 := Nat.prime_eq_prime_of_dvd_pow hq prime_1811731 hd
        subst q
        change (2 : ZMod 11057373810786419)^6103209478 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3051604739 := Nat.prime_eq_prime_of_dvd_pow hq prime_3051604739 hd
        subst q
        change (2 : ZMod 11057373810786419)^3623462 ≠ 1
        reduce_mod_char
        decide

theorem prime_11198680244449493 : Nat.Prime 11198680244449493 := by
  apply lucas_primality 11198680244449493 (2 : ZMod 11198680244449493)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11198680244449493 - 1 = (2 : ℕ)^2 * ((271 : ℕ)^1 * ((2191339 : ℕ)^1 * ((4714417 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 11198680244449493)^5599340122224746 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 271 := Nat.prime_eq_prime_of_dvd_pow hq prime_271 hd
        subst q
        change (2 : ZMod 11198680244449493)^41323543337452 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2191339 := Nat.prime_eq_prime_of_dvd_pow hq prime_2191339 hd
          subst q
          change (2 : ZMod 11198680244449493)^5110428028 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4714417 := Nat.prime_eq_prime_of_dvd_pow hq prime_4714417 hd
          subst q
          change (2 : ZMod 11198680244449493)^2375411476 ≠ 1
          reduce_mod_char
          decide

theorem prime_11341488324787883 : Nat.Prime 11341488324787883 := by
  apply lucas_primality 11341488324787883 (2 : ZMod 11341488324787883)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11341488324787883 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((117881 : ℕ)^1 * ((2829745133 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 11341488324787883)^5670744162393941 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 11341488324787883)^667146372046346 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 117881 := Nat.prime_eq_prime_of_dvd_pow hq prime_117881 hd
          subst q
          change (2 : ZMod 11341488324787883)^96211334522 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2829745133 := Nat.prime_eq_prime_of_dvd_pow hq prime_2829745133 hd
          subst q
          change (2 : ZMod 11341488324787883)^4007954 ≠ 1
          reduce_mod_char
          decide

theorem prime_11485810791015679 : Nat.Prime 11485810791015679 := by
  apply lucas_primality 11485810791015679 (15 : ZMod 11485810791015679)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11485810791015679 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((13 : ℕ)^1 * ((2371 : ℕ)^1 * ((20702092577 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (15 : ZMod 11485810791015679)^5742905395507839 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (15 : ZMod 11485810791015679)^3828603597005226 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (15 : ZMod 11485810791015679)^883523907001206 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2371 := Nat.prime_eq_prime_of_dvd_pow hq prime_2371 hd
            subst q
            change (15 : ZMod 11485810791015679)^4844289663018 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 20702092577 := Nat.prime_eq_prime_of_dvd_pow hq prime_20702092577 hd
            subst q
            change (15 : ZMod 11485810791015679)^554814 ≠ 1
            reduce_mod_char
            decide

theorem prime_11631660463231019 : Nat.Prime 11631660463231019 := by
  apply lucas_primality 11631660463231019 (2 : ZMod 11631660463231019)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11631660463231019 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((23 : ℕ)^1 * ((36123169140469 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 11631660463231019)^5815830231615509 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 11631660463231019)^1661665780461574 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 11631660463231019)^505724367966566 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 36123169140469 := Nat.prime_eq_prime_of_dvd_pow hq prime_36123169140469 hd
          subst q
          change (2 : ZMod 11631660463231019)^322 ≠ 1
          reduce_mod_char
          decide

theorem prime_11709934387200001 : Nat.Prime 11709934387200001 := by
  apply lucas_primality 11709934387200001 (17 : ZMod 11709934387200001)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11709934387200001 - 1 = (2 : ℕ)^17 * ((3 : ℕ)^5 * ((5 : ℕ)^5 * ((7 : ℕ)^6))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 11709934387200001)^5854967193600000 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 11709934387200001)^3903311462400000 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (17 : ZMod 11709934387200001)^2341986877440000 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (17 : ZMod 11709934387200001)^1672847769600000 ≠ 1
          reduce_mod_char
          decide

theorem prime_11779050242756903 : Nat.Prime 11779050242756903 := by
  apply lucas_primality 11779050242756903 (5 : ZMod 11779050242756903)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11779050242756903 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((163 : ℕ)^1 * ((400199 : ℕ)^1 * ((12897889 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 11779050242756903)^5889525121378451 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 11779050242756903)^1682721463250986 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
          subst q
          change (5 : ZMod 11779050242756903)^72264111918754 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 400199 := Nat.prime_eq_prime_of_dvd_pow hq prime_400199 hd
            subst q
            change (5 : ZMod 11779050242756903)^29432982698 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 12897889 := Nat.prime_eq_prime_of_dvd_pow hq prime_12897889 hd
            subst q
            change (5 : ZMod 11779050242756903)^913254118 ≠ 1
            reduce_mod_char
            decide

theorem prime_11927993112483937 : Nat.Prime 11927993112483937 := by
  apply lucas_primality 11927993112483937 (5 : ZMod 11927993112483937)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11927993112483937 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((41 : ℕ)^1 * ((3030486055001 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 11927993112483937)^5963996556241968 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 11927993112483937)^3975997704161312 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (5 : ZMod 11927993112483937)^290926661280096 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3030486055001 := Nat.prime_eq_prime_of_dvd_pow hq prime_3030486055001 hd
          subst q
          change (5 : ZMod 11927993112483937)^3936 ≠ 1
          reduce_mod_char
          decide

theorem prime_12078502137213133 : Nat.Prime 12078502137213133 := by
  apply lucas_primality 12078502137213133 (2 : ZMod 12078502137213133)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12078502137213133 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((113 : ℕ)^1 * ((8317 : ℕ)^1 * ((29077 : ℕ)^1 * ((36833 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 12078502137213133)^6039251068606566 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 12078502137213133)^4026167379071044 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
          subst q
          change (2 : ZMod 12078502137213133)^106889399444364 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 8317 := Nat.prime_eq_prime_of_dvd_pow hq prime_8317 hd
            subst q
            change (2 : ZMod 12078502137213133)^1452266699196 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 29077 := Nat.prime_eq_prime_of_dvd_pow hq prime_29077 hd
              subst q
              change (2 : ZMod 12078502137213133)^415397122716 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 36833 := Nat.prime_eq_prime_of_dvd_pow hq prime_36833 hd
              subst q
              change (2 : ZMod 12078502137213133)^327926102604 ≠ 1
              reduce_mod_char
              decide

theorem prime_12230590464000049 : Nat.Prime 12230590464000049 := by
  apply lucas_primality 12230590464000049 (13 : ZMod 12230590464000049)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12230590464000049 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((4021 : ℕ)^1 * ((9052615483 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 12230590464000049)^6115295232000024 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 12230590464000049)^4076863488000016 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (13 : ZMod 12230590464000049)^1747227209142864 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 4021 := Nat.prime_eq_prime_of_dvd_pow hq prime_4021 hd
            subst q
            change (13 : ZMod 12230590464000049)^3041678802288 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 9052615483 := Nat.prime_eq_prime_of_dvd_pow hq prime_9052615483 hd
            subst q
            change (13 : ZMod 12230590464000049)^1351056 ≠ 1
            reduce_mod_char
            decide

theorem prime_12384271322498941 : Nat.Prime 12384271322498941 := by
  apply lucas_primality 12384271322498941 (7 : ZMod 12384271322498941)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12384271322498941 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((29 : ℕ)^1 * ((203363 : ℕ)^1 * ((34998487 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 12384271322498941)^6192135661249470 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 12384271322498941)^4128090440832980 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 12384271322498941)^2476854264499788 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (7 : ZMod 12384271322498941)^427043838706860 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 203363 := Nat.prime_eq_prime_of_dvd_pow hq prime_203363 hd
              subst q
              change (7 : ZMod 12384271322498941)^60897367380 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 34998487 := Nat.prime_eq_prime_of_dvd_pow hq prime_34998487 hd
              subst q
              change (7 : ZMod 12384271322498941)^353851620 ≠ 1
              reduce_mod_char
              decide

theorem prime_12409557938693317 : Nat.Prime 12409557938693317 := by
  apply lucas_primality 12409557938693317 (2 : ZMod 12409557938693317)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12409557938693317 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((23 : ℕ)^1 * ((1303 : ℕ)^1 * ((16529 : ℕ)^1 * ((695881 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 12409557938693317)^6204778969346658 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 12409557938693317)^4136519312897772 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 12409557938693317)^539545997334492 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1303 := Nat.prime_eq_prime_of_dvd_pow hq prime_1303 hd
            subst q
            change (2 : ZMod 12409557938693317)^9523835716572 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 16529 := Nat.prime_eq_prime_of_dvd_pow hq prime_16529 hd
              subst q
              change (2 : ZMod 12409557938693317)^750774876804 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 695881 := Nat.prime_eq_prime_of_dvd_pow hq prime_695881 hd
              subst q
              change (2 : ZMod 12409557938693317)^17832873636 ≠ 1
              reduce_mod_char
              decide

theorem prime_12539558025308311 : Nat.Prime 12539558025308311 := by
  apply lucas_primality 12539558025308311 (6 : ZMod 12539558025308311)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12539558025308311 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((3061 : ℕ)^1 * ((245419 : ℕ)^1 * ((556403 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 12539558025308311)^6269779012654155 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 12539558025308311)^4179852675102770 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 12539558025308311)^2507911605061662 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3061 := Nat.prime_eq_prime_of_dvd_pow hq prime_3061 hd
            subst q
            change (6 : ZMod 12539558025308311)^4096556035710 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 245419 := Nat.prime_eq_prime_of_dvd_pow hq prime_245419 hd
              subst q
              change (6 : ZMod 12539558025308311)^51094487490 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 556403 := Nat.prime_eq_prime_of_dvd_pow hq prime_556403 hd
              subst q
              change (6 : ZMod 12539558025308311)^22536826770 ≠ 1
              reduce_mod_char
              decide

theorem prime_12696463968316591 : Nat.Prime 12696463968316591 := by
  apply lucas_primality 12696463968316591 (3 : ZMod 12696463968316591)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12696463968316591 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((5496304748189 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 12696463968316591)^6348231984158295 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 12696463968316591)^4232154656105530 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 12696463968316591)^2539292793663318 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (3 : ZMod 12696463968316591)^1813780566902370 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
              subst q
              change (3 : ZMod 12696463968316591)^1154223997119690 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 5496304748189 := Nat.prime_eq_prime_of_dvd_pow hq prime_5496304748189 hd
              subst q
              change (3 : ZMod 12696463968316591)^2310 ≠ 1
              reduce_mod_char
              decide

theorem prime_12855002631049223 : Nat.Prime 12855002631049223 := by
  apply lucas_primality 12855002631049223 (5 : ZMod 12855002631049223)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12855002631049223 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((59 : ℕ)^1 * ((2877463 : ℕ)^1 * ((5408569 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 12855002631049223)^6427501315524611 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 12855002631049223)^1836428947292746 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (5 : ZMod 12855002631049223)^217881400526258 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2877463 := Nat.prime_eq_prime_of_dvd_pow hq prime_2877463 hd
            subst q
            change (5 : ZMod 12855002631049223)^4467477994 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 5408569 := Nat.prime_eq_prime_of_dvd_pow hq prime_5408569 hd
            subst q
            change (5 : ZMod 12855002631049223)^2376784438 ≠ 1
            reduce_mod_char
            decide

theorem prime_12906471581508257 : Nat.Prime 12906471581508257 := by
  apply lucas_primality 12906471581508257 (5 : ZMod 12906471581508257)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12906471581508257 - 1 = (2 : ℕ)^5 * ((59 : ℕ)^1 * ((397 : ℕ)^1 * ((89909 : ℕ)^1 * ((191519 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 12906471581508257)^6453235790754128 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
        subst q
        change (5 : ZMod 12906471581508257)^218753755618784 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 397 := Nat.prime_eq_prime_of_dvd_pow hq prime_397 hd
          subst q
          change (5 : ZMod 12906471581508257)^32510003983648 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 89909 := Nat.prime_eq_prime_of_dvd_pow hq prime_89909 hd
            subst q
            change (5 : ZMod 12906471581508257)^143550385184 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 191519 := Nat.prime_eq_prime_of_dvd_pow hq prime_191519 hd
            subst q
            change (5 : ZMod 12906471581508257)^67390032224 ≠ 1
            reduce_mod_char
            decide

theorem prime_12918664044953581 : Nat.Prime 12918664044953581 := by
  apply lucas_primality 12918664044953581 (2 : ZMod 12918664044953581)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12918664044953581 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((43 : ℕ)^1 * ((5007234125951 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 12918664044953581)^6459332022476790 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 12918664044953581)^4306221348317860 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 12918664044953581)^2583732808990716 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (2 : ZMod 12918664044953581)^300434047557060 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 5007234125951 := Nat.prime_eq_prime_of_dvd_pow hq prime_5007234125951 hd
            subst q
            change (2 : ZMod 12918664044953581)^2580 ≠ 1
            reduce_mod_char
            decide

theorem prime_13015187577015713 : Nat.Prime 13015187577015713 := by
  apply lucas_primality 13015187577015713 (3 : ZMod 13015187577015713)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13015187577015713 - 1 = (2 : ℕ)^5 * ((11 : ℕ)^1 * ((261887 : ℕ)^1 * ((141186713 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 13015187577015713)^6507593788507856 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (3 : ZMod 13015187577015713)^1183198870637792 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 261887 := Nat.prime_eq_prime_of_dvd_pow hq prime_261887 hd
          subst q
          change (3 : ZMod 13015187577015713)^49697722976 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 141186713 := Nat.prime_eq_prime_of_dvd_pow hq prime_141186713 hd
          subst q
          change (3 : ZMod 13015187577015713)^92184224 ≠ 1
          reduce_mod_char
          decide

theorem prime_13177032454057613 : Nat.Prime 13177032454057613 := by
  apply lucas_primality 13177032454057613 (2 : ZMod 13177032454057613)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13177032454057613 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((17 : ℕ)^1 * ((23 : ℕ)^1 * ((139 : ℕ)^1 * ((821 : ℕ)^1 * ((10546901 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 13177032454057613)^6588516227028806 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 13177032454057613)^1882433207722516 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 13177032454057613)^775119556121036 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (2 : ZMod 13177032454057613)^572914454524244 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
              subst q
              change (2 : ZMod 13177032454057613)^94798794633508 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 821 := Nat.prime_eq_prime_of_dvd_pow hq prime_821 hd
                subst q
                change (2 : ZMod 13177032454057613)^16049978628572 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 10546901 := Nat.prime_eq_prime_of_dvd_pow hq prime_10546901 hd
                subst q
                change (2 : ZMod 13177032454057613)^1249374812 ≠ 1
                reduce_mod_char
                decide

theorem prime_13315382391724213 : Nat.Prime 13315382391724213 := by
  apply lucas_primality 13315382391724213 (2 : ZMod 13315382391724213)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13315382391724213 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((281 : ℕ)^1 * ((3948808538471 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 13315382391724213)^6657691195862106 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 13315382391724213)^4438460797241404 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 281 := Nat.prime_eq_prime_of_dvd_pow hq prime_281 hd
          subst q
          change (2 : ZMod 13315382391724213)^47385702461652 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3948808538471 := Nat.prime_eq_prime_of_dvd_pow hq prime_3948808538471 hd
          subst q
          change (2 : ZMod 13315382391724213)^3372 ≠ 1
          reduce_mod_char
          decide

theorem prime_13340550994697819 : Nat.Prime 13340550994697819 := by
  apply lucas_primality 13340550994697819 (2 : ZMod 13340550994697819)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13340550994697819 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((392369146902877 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 13340550994697819)^6670275497348909 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 13340550994697819)^784738293805754 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 392369146902877 := Nat.prime_eq_prime_of_dvd_pow hq prime_392369146902877 hd
        subst q
        change (2 : ZMod 13340550994697819)^34 ≠ 1
        reduce_mod_char
        decide

theorem prime_13505757016490021 : Nat.Prime 13505757016490021 := by
  apply lucas_primality 13505757016490021 (2 : ZMod 13505757016490021)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13505757016490021 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((266221 : ℕ)^1 * ((2536568681 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 13505757016490021)^6752878508245010 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 13505757016490021)^2701151403298004 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 266221 := Nat.prime_eq_prime_of_dvd_pow hq prime_266221 hd
          subst q
          change (2 : ZMod 13505757016490021)^50731373620 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2536568681 := Nat.prime_eq_prime_of_dvd_pow hq prime_2536568681 hd
          subst q
          change (2 : ZMod 13505757016490021)^5324420 ≠ 1
          reduce_mod_char
          decide

theorem prime_13672664422368643 : Nat.Prime 13672664422368643 := by
  apply lucas_primality 13672664422368643 (2 : ZMod 13672664422368643)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13672664422368643 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((4093 : ℕ)^1 * ((64621 : ℕ)^1 * ((319097 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 13672664422368643)^6836332211184321 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 13672664422368643)^4557554807456214 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 4093 := Nat.prime_eq_prime_of_dvd_pow hq prime_4093 hd
          subst q
          change (2 : ZMod 13672664422368643)^3340499492394 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 64621 := Nat.prime_eq_prime_of_dvd_pow hq prime_64621 hd
            subst q
            change (2 : ZMod 13672664422368643)^211582371402 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 319097 := Nat.prime_eq_prime_of_dvd_pow hq prime_319097 hd
            subst q
            change (2 : ZMod 13672664422368643)^42847987986 ≠ 1
            reduce_mod_char
            decide

theorem prime_13841287201000009 : Nat.Prime 13841287201000009 := by
  apply lucas_primality 13841287201000009 (17 : ZMod 13841287201000009)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13841287201000009 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((19 : ℕ)^1 * ((43 : ℕ)^1 * ((673 : ℕ)^1 * ((8737 : ℕ)^1 * ((13339 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 13841287201000009)^6920643600500004 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 13841287201000009)^4613762400333336 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (17 : ZMod 13841287201000009)^728488800052632 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (17 : ZMod 13841287201000009)^321890400023256 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 673 := Nat.prime_eq_prime_of_dvd_pow hq prime_673 hd
              subst q
              change (17 : ZMod 13841287201000009)^20566548589896 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 8737 := Nat.prime_eq_prime_of_dvd_pow hq prime_8737 hd
                subst q
                change (17 : ZMod 13841287201000009)^1584215085384 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 13339 := Nat.prime_eq_prime_of_dvd_pow hq prime_13339 hd
                subst q
                change (17 : ZMod 13841287201000009)^1037655536472 ≠ 1
                reduce_mod_char
                decide

theorem prime_14011639427134463 : Nat.Prime 14011639427134463 := by
  apply lucas_primality 14011639427134463 (5 : ZMod 14011639427134463)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14011639427134463 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((2843 : ℕ)^1 * ((3733 : ℕ)^1 * ((38830697 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 14011639427134463)^7005819713567231 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (5 : ZMod 14011639427134463)^824214083949086 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2843 := Nat.prime_eq_prime_of_dvd_pow hq prime_2843 hd
          subst q
          change (5 : ZMod 14011639427134463)^4928469724634 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3733 := Nat.prime_eq_prime_of_dvd_pow hq prime_3733 hd
            subst q
            change (5 : ZMod 14011639427134463)^3753452833414 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 38830697 := Nat.prime_eq_prime_of_dvd_pow hq prime_38830697 hd
            subst q
            change (5 : ZMod 14011639427134463)^360839246 ≠ 1
            reduce_mod_char
            decide

theorem prime_14092814387121121 : Nat.Prime 14092814387121121 := by
  apply lucas_primality 14092814387121121 (39 : ZMod 14092814387121121)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14092814387121121 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((17 : ℕ)^1 * ((29 : ℕ)^1 * ((181 : ℕ)^1 * ((193 : ℕ)^1 * ((81181 : ℕ)^1)))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (39 : ZMod 14092814387121121)^7046407193560560 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (39 : ZMod 14092814387121121)^4697604795707040 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (39 : ZMod 14092814387121121)^2818562877424224 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (39 : ZMod 14092814387121121)^2013259198160160 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
              subst q
              change (39 : ZMod 14092814387121121)^828989081595360 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
                subst q
                change (39 : ZMod 14092814387121121)^485959116797280 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 181 := Nat.prime_eq_prime_of_dvd_pow hq prime_181 hd
                  subst q
                  change (39 : ZMod 14092814387121121)^77860852967520 ≠ 1
                  reduce_mod_char
                  decide
                · rcases hq.dvd_mul.mp hd with hd | hd
                  · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
                    subst q
                    change (39 : ZMod 14092814387121121)^73019763663840 ≠ 1
                    reduce_mod_char
                    decide
                  · have heq : q = 81181 := Nat.prime_eq_prime_of_dvd_pow hq prime_81181 hd
                    subst q
                    change (39 : ZMod 14092814387121121)^173597447520 ≠ 1
                    reduce_mod_char
                    decide

theorem prime_14183735261958167 : Nat.Prime 14183735261958167 := by
  apply lucas_primality 14183735261958167 (5 : ZMod 14183735261958167)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14183735261958167 - 1 = (2 : ℕ)^1 * ((617 : ℕ)^1 * ((1615723 : ℕ)^1 * ((7113913 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 14183735261958167)^7091867630979083 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 617 := Nat.prime_eq_prime_of_dvd_pow hq prime_617 hd
        subst q
        change (5 : ZMod 14183735261958167)^22988225708198 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1615723 := Nat.prime_eq_prime_of_dvd_pow hq prime_1615723 hd
          subst q
          change (5 : ZMod 14183735261958167)^8778568642 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7113913 := Nat.prime_eq_prime_of_dvd_pow hq prime_7113913 hd
          subst q
          change (5 : ZMod 14183735261958167)^1993802182 ≠ 1
          reduce_mod_char
          decide

theorem prime_14357588953446659 : Nat.Prime 14357588953446659 := by
  apply lucas_primality 14357588953446659 (2 : ZMod 14357588953446659)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14357588953446659 - 1 = (2 : ℕ)^1 * ((73 : ℕ)^1 * ((557 : ℕ)^1 * ((176552334589 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 14357588953446659)^7178794476723329 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
        subst q
        change (2 : ZMod 14357588953446659)^196679300732146 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 557 := Nat.prime_eq_prime_of_dvd_pow hq prime_557 hd
          subst q
          change (2 : ZMod 14357588953446659)^25776640849994 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 176552334589 := Nat.prime_eq_prime_of_dvd_pow hq prime_176552334589 hd
          subst q
          change (2 : ZMod 14357588953446659)^81322 ≠ 1
          reduce_mod_char
          decide

theorem prime_14533214836718671 : Nat.Prime 14533214836718671 := by
  apply lucas_primality 14533214836718671 (7 : ZMod 14533214836718671)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14533214836718671 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((23 : ℕ)^1 * ((24923 : ℕ)^1 * ((845108141 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 14533214836718671)^7266607418359335 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 14533214836718671)^4844404945572890 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 14533214836718671)^2906642967343734 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (7 : ZMod 14533214836718671)^631878905944290 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 24923 := Nat.prime_eq_prime_of_dvd_pow hq prime_24923 hd
              subst q
              change (7 : ZMod 14533214836718671)^583124617290 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 845108141 := Nat.prime_eq_prime_of_dvd_pow hq prime_845108141 hd
              subst q
              change (7 : ZMod 14533214836718671)^17196870 ≠ 1
              reduce_mod_char
              decide

theorem prime_14710627334390693 : Nat.Prime 14710627334390693 := by
  apply lucas_primality 14710627334390693 (2 : ZMod 14710627334390693)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14710627334390693 - 1 = (2 : ℕ)^2 * ((59 : ℕ)^1 * ((2273 : ℕ)^1 * ((27423302539 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 14710627334390693)^7355313667195346 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
        subst q
        change (2 : ZMod 14710627334390693)^249332666684588 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2273 := Nat.prime_eq_prime_of_dvd_pow hq prime_2273 hd
          subst q
          change (2 : ZMod 14710627334390693)^6471899399204 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 27423302539 := Nat.prime_eq_prime_of_dvd_pow hq prime_27423302539 hd
          subst q
          change (2 : ZMod 14710627334390693)^536428 ≠ 1
          reduce_mod_char
          decide

theorem prime_14889840956932163 : Nat.Prime 14889840956932163 := by
  apply lucas_primality 14889840956932163 (2 : ZMod 14889840956932163)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14889840956932163 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^2 * ((44052783896249 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 14889840956932163)^7444920478466081 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 14889840956932163)^1145372381302474 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 44052783896249 := Nat.prime_eq_prime_of_dvd_pow hq prime_44052783896249 hd
        subst q
        change (2 : ZMod 14889840956932163)^338 ≠ 1
        reduce_mod_char
        decide

theorem prime_14941887294069917 : Nat.Prime 14941887294069917 := by
  apply lucas_primality 14941887294069917 (2 : ZMod 14941887294069917)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 14941887294069917 - 1 = (2 : ℕ)^2 * ((31 : ℕ)^1 * ((1789 : ℕ)^1 * ((67355556781 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 14941887294069917)^7470943647034958 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (2 : ZMod 14941887294069917)^481996364324836 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1789 := Nat.prime_eq_prime_of_dvd_pow hq prime_1789 hd
          subst q
          change (2 : ZMod 14941887294069917)^8352089040844 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 67355556781 := Nat.prime_eq_prime_of_dvd_pow hq prime_67355556781 hd
          subst q
          change (2 : ZMod 14941887294069917)^221836 ≠ 1
          reduce_mod_char
          decide

theorem prime_15070870303021829 : Nat.Prime 15070870303021829 := by
  apply lucas_primality 15070870303021829 (2 : ZMod 15070870303021829)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15070870303021829 - 1 = (2 : ℕ)^2 * ((1523 : ℕ)^1 * ((2473878907259 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 15070870303021829)^7535435151510914 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1523 := Nat.prime_eq_prime_of_dvd_pow hq prime_1523 hd
        subst q
        change (2 : ZMod 15070870303021829)^9895515629036 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2473878907259 := Nat.prime_eq_prime_of_dvd_pow hq prime_2473878907259 hd
        subst q
        change (2 : ZMod 15070870303021829)^6092 ≠ 1
        reduce_mod_char
        decide

theorem prime_15191078611731811 : Nat.Prime 15191078611731811 := by
  apply lucas_primality 15191078611731811 (2 : ZMod 15191078611731811)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15191078611731811 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7115963 : ℕ)^1 * ((71159629 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 15191078611731811)^7595539305865905 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 15191078611731811)^5063692870577270 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 15191078611731811)^3038215722346362 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7115963 := Nat.prime_eq_prime_of_dvd_pow hq prime_7115963 hd
            subst q
            change (2 : ZMod 15191078611731811)^2134788870 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 71159629 := Nat.prime_eq_prime_of_dvd_pow hq prime_71159629 hd
            subst q
            change (2 : ZMod 15191078611731811)^213478890 ≠ 1
            reduce_mod_char
            decide

theorem prime_15253730059904069 : Nat.Prime 15253730059904069 := by
  apply lucas_primality 15253730059904069 (2 : ZMod 15253730059904069)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15253730059904069 - 1 = (2 : ℕ)^2 * ((3813432514976017 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 15253730059904069)^7626865029952034 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 3813432514976017 := Nat.prime_eq_prime_of_dvd_pow hq prime_3813432514976017 hd
      subst q
      change (2 : ZMod 15253730059904069)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_15438435003747017 : Nat.Prime 15438435003747017 := by
  apply lucas_primality 15438435003747017 (3 : ZMod 15438435003747017)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15438435003747017 - 1 = (2 : ℕ)^3 * ((31 : ℕ)^1 * ((2389 : ℕ)^1 * ((26057661803 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 15438435003747017)^7719217501873508 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (3 : ZMod 15438435003747017)^498014032378936 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2389 := Nat.prime_eq_prime_of_dvd_pow hq prime_2389 hd
          subst q
          change (3 : ZMod 15438435003747017)^6462300127144 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 26057661803 := Nat.prime_eq_prime_of_dvd_pow hq prime_26057661803 hd
          subst q
          change (3 : ZMod 15438435003747017)^592472 ≠ 1
          reduce_mod_char
          decide

theorem prime_15625000000000021 : Nat.Prime 15625000000000021 := by
  apply lucas_primality 15625000000000021 (2 : ZMod 15625000000000021)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15625000000000021 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((1283 : ℕ)^1 * ((9661 : ℕ)^1 * ((3001387 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 15625000000000021)^7812500000000010 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 15625000000000021)^5208333333333340 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 15625000000000021)^3125000000000004 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (2 : ZMod 15625000000000021)^2232142857142860 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1283 := Nat.prime_eq_prime_of_dvd_pow hq prime_1283 hd
              subst q
              change (2 : ZMod 15625000000000021)^12178487918940 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 9661 := Nat.prime_eq_prime_of_dvd_pow hq prime_9661 hd
                subst q
                change (2 : ZMod 15625000000000021)^1617327398820 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 3001387 := Nat.prime_eq_prime_of_dvd_pow hq prime_3001387 hd
                subst q
                change (2 : ZMod 15625000000000021)^5205926460 ≠ 1
                reduce_mod_char
                decide

theorem prime_15813440003753003 : Nat.Prime 15813440003753003 := by
  apply lucas_primality 15813440003753003 (5 : ZMod 15813440003753003)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 15813440003753003 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((41 : ℕ)^1 * ((97 : ℕ)^1 * ((3061 : ℕ)^1 * ((49961341 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 15813440003753003)^7906720001876501 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (5 : ZMod 15813440003753003)^1216418461827154 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (5 : ZMod 15813440003753003)^385693658628122 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
            subst q
            change (5 : ZMod 15813440003753003)^163025154677866 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 3061 := Nat.prime_eq_prime_of_dvd_pow hq prime_3061 hd
              subst q
              change (5 : ZMod 15813440003753003)^5166102582082 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 49961341 := Nat.prime_eq_prime_of_dvd_pow hq prime_49961341 hd
              subst q
              change (5 : ZMod 15813440003753003)^316513522 ≠ 1
              reduce_mod_char
              decide

theorem prime_16003770060096073 : Nat.Prime 16003770060096073 := by
  apply lucas_primality 16003770060096073 (7 : ZMod 16003770060096073)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16003770060096073 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((97 : ℕ)^1 * ((433 : ℕ)^1 * ((20353 : ℕ)^1 * ((260017 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 16003770060096073)^8001885030048036 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 16003770060096073)^5334590020032024 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
          subst q
          change (7 : ZMod 16003770060096073)^164987320207176 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 433 := Nat.prime_eq_prime_of_dvd_pow hq prime_433 hd
            subst q
            change (7 : ZMod 16003770060096073)^36960207990984 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 20353 := Nat.prime_eq_prime_of_dvd_pow hq prime_20353 hd
              subst q
              change (7 : ZMod 16003770060096073)^786310129224 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 260017 := Nat.prime_eq_prime_of_dvd_pow hq prime_260017 hd
              subst q
              change (7 : ZMod 16003770060096073)^61548937416 ≠ 1
              reduce_mod_char
              decide

theorem prime_16185521409682381 : Nat.Prime 16185521409682381 := by
  apply lucas_primality 16185521409682381 (2 : ZMod 16185521409682381)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16185521409682381 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((19 : ℕ)^1 * ((127 : ℕ)^1 * ((27541 : ℕ)^1 * ((579883 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 16185521409682381)^8092760704841190 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 16185521409682381)^5395173803227460 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 16185521409682381)^3237104281936476 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (2 : ZMod 16185521409682381)^2312217344240340 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
              subst q
              change (2 : ZMod 16185521409682381)^851869547878020 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
                subst q
                change (2 : ZMod 16185521409682381)^127445050469940 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 27541 := Nat.prime_eq_prime_of_dvd_pow hq prime_27541 hd
                  subst q
                  change (2 : ZMod 16185521409682381)^587688225180 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 579883 := Nat.prime_eq_prime_of_dvd_pow hq prime_579883 hd
                  subst q
                  change (2 : ZMod 16185521409682381)^27911701860 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_16196005304479751 : Nat.Prime 16196005304479751 := by
  apply lucas_primality 16196005304479751 (7 : ZMod 16196005304479751)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16196005304479751 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^3 * ((1231 : ℕ)^1 * ((52627149649 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 16196005304479751)^8098002652239875 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 16196005304479751)^3239201060895950 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1231 := Nat.prime_eq_prime_of_dvd_pow hq prime_1231 hd
          subst q
          change (7 : ZMod 16196005304479751)^13156787412250 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 52627149649 := Nat.prime_eq_prime_of_dvd_pow hq prime_52627149649 hd
          subst q
          change (7 : ZMod 16196005304479751)^307750 ≠ 1
          reduce_mod_char
          decide

theorem prime_16390160963076127 : Nat.Prime 16390160963076127 := by
  apply lucas_primality 16390160963076127 (3 : ZMod 16390160963076127)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16390160963076127 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((2030981 : ℕ)^1 * ((1345011841 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 16390160963076127)^8195080481538063 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 16390160963076127)^5463386987692042 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2030981 := Nat.prime_eq_prime_of_dvd_pow hq prime_2030981 hd
          subst q
          change (3 : ZMod 16390160963076127)^8070071046 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1345011841 := Nat.prime_eq_prime_of_dvd_pow hq prime_1345011841 hd
          subst q
          change (3 : ZMod 16390160963076127)^12185886 ≠ 1
          reduce_mod_char
          decide

theorem prime_16586252353140629 : Nat.Prime 16586252353140629 := by
  apply lucas_primality 16586252353140629 (2 : ZMod 16586252353140629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16586252353140629 - 1 = (2 : ℕ)^2 * ((1117 : ℕ)^1 * ((18133 : ℕ)^1 * ((204722437 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 16586252353140629)^8293126176570314 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1117 := Nat.prime_eq_prime_of_dvd_pow hq prime_1117 hd
        subst q
        change (2 : ZMod 16586252353140629)^14848927800484 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 18133 := Nat.prime_eq_prime_of_dvd_pow hq prime_18133 hd
          subst q
          change (2 : ZMod 16586252353140629)^914699848516 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 204722437 := Nat.prime_eq_prime_of_dvd_pow hq prime_204722437 hd
          subst q
          change (2 : ZMod 16586252353140629)^81018244 ≠ 1
          reduce_mod_char
          decide

theorem prime_16784294883374663 : Nat.Prime 16784294883374663 := by
  apply lucas_primality 16784294883374663 (7 : ZMod 16784294883374663)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16784294883374663 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((10111 : ℕ)^1 * ((118571675003 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 16784294883374663)^8392147441687331 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 16784294883374663)^2397756411910666 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 10111 := Nat.prime_eq_prime_of_dvd_pow hq prime_10111 hd
          subst q
          change (7 : ZMod 16784294883374663)^1660003450042 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 118571675003 := Nat.prime_eq_prime_of_dvd_pow hq prime_118571675003 hd
          subst q
          change (7 : ZMod 16784294883374663)^141554 ≠ 1
          reduce_mod_char
          decide

theorem prime_16984304054288777 : Nat.Prime 16984304054288777 := by
  apply lucas_primality 16984304054288777 (3 : ZMod 16984304054288777)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 16984304054288777 - 1 = (2 : ℕ)^3 * ((2609 : ℕ)^1 * ((813736300033 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 16984304054288777)^8492152027144388 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 2609 := Nat.prime_eq_prime_of_dvd_pow hq prime_2609 hd
        subst q
        change (3 : ZMod 16984304054288777)^6509890400264 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 813736300033 := Nat.prime_eq_prime_of_dvd_pow hq prime_813736300033 hd
        subst q
        change (3 : ZMod 16984304054288777)^20872 ≠ 1
        reduce_mod_char
        decide

theorem prime_17186295458566151 : Nat.Prime 17186295458566151 := by
  apply lucas_primality 17186295458566151 (11 : ZMod 17186295458566151)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17186295458566151 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((7 : ℕ)^1 * ((1637 : ℕ)^1 * ((267677 : ℕ)^1 * ((112061 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 17186295458566151)^8593147729283075 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 17186295458566151)^3437259091713230 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (11 : ZMod 17186295458566151)^2455185065509450 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1637 := Nat.prime_eq_prime_of_dvd_pow hq prime_1637 hd
            subst q
            change (11 : ZMod 17186295458566151)^10498653303950 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 267677 := Nat.prime_eq_prime_of_dvd_pow hq prime_267677 hd
              subst q
              change (11 : ZMod 17186295458566151)^64205349950 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 112061 := Nat.prime_eq_prime_of_dvd_pow hq prime_112061 hd
              subst q
              change (11 : ZMod 17186295458566151)^153365537150 ≠ 1
              reduce_mod_char
              decide

theorem prime_17390284781428451 : Nat.Prime 17390284781428451 := by
  apply lucas_primality 17390284781428451 (2 : ZMod 17390284781428451)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17390284781428451 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((29 : ℕ)^1 * ((73 : ℕ)^1 * ((164291778757 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 17390284781428451)^8695142390714225 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 17390284781428451)^3478056956285690 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (2 : ZMod 17390284781428451)^599664992463050 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
            subst q
            change (2 : ZMod 17390284781428451)^238223079197650 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 164291778757 := Nat.prime_eq_prime_of_dvd_pow hq prime_164291778757 hd
            subst q
            change (2 : ZMod 17390284781428451)^105850 ≠ 1
            reduce_mod_char
            decide

theorem prime_17596287801000019 : Nat.Prime 17596287801000019 := by
  apply lucas_primality 17596287801000019 (2 : ZMod 17596287801000019)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17596287801000019 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((233 : ℕ)^1 * ((659 : ℕ)^1 * ((11489 : ℕ)^1 * ((50377 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 17596287801000019)^8798143900500009 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 17596287801000019)^5865429267000006 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 17596287801000019)^1599662527363638 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
            subst q
            change (2 : ZMod 17596287801000019)^75520548502146 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 659 := Nat.prime_eq_prime_of_dvd_pow hq prime_659 hd
              subst q
              change (2 : ZMod 17596287801000019)^26701498939302 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 11489 := Nat.prime_eq_prime_of_dvd_pow hq prime_11489 hd
                subst q
                change (2 : ZMod 17596287801000019)^1531576969362 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 50377 := Nat.prime_eq_prime_of_dvd_pow hq prime_50377 hd
                subst q
                change (2 : ZMod 17596287801000019)^349292093634 ≠ 1
                reduce_mod_char
                decide

theorem prime_17804320388674579 : Nat.Prime 17804320388674579 := by
  apply lucas_primality 17804320388674579 (2 : ZMod 17804320388674579)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 17804320388674579 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^7 * ((11 : ℕ)^1 * ((131 : ℕ)^1 * ((1399 : ℕ)^1 * ((2019133 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 17804320388674579)^8902160194337289 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 17804320388674579)^5934773462891526 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 17804320388674579)^1618574580788598 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
            subst q
            change (2 : ZMod 17804320388674579)^135910842661638 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1399 := Nat.prime_eq_prime_of_dvd_pow hq prime_1399 hd
              subst q
              change (2 : ZMod 17804320388674579)^12726462036222 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 2019133 := Nat.prime_eq_prime_of_dvd_pow hq prime_2019133 hd
              subst q
              change (2 : ZMod 17804320388674579)^8817804666 ≠ 1
              reduce_mod_char
              decide

theorem prime_18014398509482143 : Nat.Prime 18014398509482143 := by
  apply lucas_primality 18014398509482143 (3 : ZMod 18014398509482143)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18014398509482143 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7724869 : ℕ)^1 * ((388666753 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 18014398509482143)^9007199254741071 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 18014398509482143)^6004799503160714 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7724869 := Nat.prime_eq_prime_of_dvd_pow hq prime_7724869 hd
          subst q
          change (3 : ZMod 18014398509482143)^2332000518 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 388666753 := Nat.prime_eq_prime_of_dvd_pow hq prime_388666753 hd
          subst q
          change (3 : ZMod 18014398509482143)^46349214 ≠ 1
          reduce_mod_char
          decide

theorem prime_18081192330181121 : Nat.Prime 18081192330181121 := by
  apply lucas_primality 18081192330181121 (6 : ZMod 18081192330181121)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18081192330181121 - 1 = (2 : ℕ)^9 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((19 : ℕ)^1 * ((31 : ℕ)^1 * ((16417 : ℕ)^1 * ((104347 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 18081192330181121)^9040596165090560 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 18081192330181121)^3616238466036224 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 18081192330181121)^2583027475740160 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (6 : ZMod 18081192330181121)^951641701588480 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
              subst q
              change (6 : ZMod 18081192330181121)^583264268715520 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 16417 := Nat.prime_eq_prime_of_dvd_pow hq prime_16417 hd
                subst q
                change (6 : ZMod 18081192330181121)^1101370063360 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 104347 := Nat.prime_eq_prime_of_dvd_pow hq prime_104347 hd
                subst q
                change (6 : ZMod 18081192330181121)^173279464960 ≠ 1
                reduce_mod_char
                decide

theorem prime_18138911616891677 : Nat.Prime 18138911616891677 := by
  apply lucas_primality 18138911616891677 (2 : ZMod 18138911616891677)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18138911616891677 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((17 : ℕ)^1 * ((83 : ℕ)^1 * ((8209 : ℕ)^1 * ((30115537 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 18138911616891677)^9069455808445838 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 18138911616891677)^1395300893607052 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 18138911616891677)^1066994800993628 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
            subst q
            change (2 : ZMod 18138911616891677)^218541103817972 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 8209 := Nat.prime_eq_prime_of_dvd_pow hq prime_8209 hd
              subst q
              change (2 : ZMod 18138911616891677)^2209637180764 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 30115537 := Nat.prime_eq_prime_of_dvd_pow hq prime_30115537 hd
              subst q
              change (2 : ZMod 18138911616891677)^602310748 ≠ 1
              reduce_mod_char
              decide

theorem prime_18226538222455813 : Nat.Prime 18226538222455813 := by
  apply lucas_primality 18226538222455813 (5 : ZMod 18226538222455813)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18226538222455813 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((196879 : ℕ)^1 * ((7714780069 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 18226538222455813)^9113269111227906 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 18226538222455813)^6075512740818604 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 196879 := Nat.prime_eq_prime_of_dvd_pow hq prime_196879 hd
          subst q
          change (5 : ZMod 18226538222455813)^92577360828 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7714780069 := Nat.prime_eq_prime_of_dvd_pow hq prime_7714780069 hd
          subst q
          change (5 : ZMod 18226538222455813)^2362548 ≠ 1
          reduce_mod_char
          decide

theorem prime_18440755681001561 : Nat.Prime 18440755681001561 := by
  apply lucas_primality 18440755681001561 (3 : ZMod 18440755681001561)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18440755681001561 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((102607 : ℕ)^1 * ((4493054977 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 18440755681001561)^9220377840500780 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 18440755681001561)^3688151136200312 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 102607 := Nat.prime_eq_prime_of_dvd_pow hq prime_102607 hd
          subst q
          change (3 : ZMod 18440755681001561)^179722199080 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4493054977 := Nat.prime_eq_prime_of_dvd_pow hq prime_4493054977 hd
          subst q
          change (3 : ZMod 18440755681001561)^4104280 ≠ 1
          reduce_mod_char
          decide

theorem prime_18657067133265643 : Nat.Prime 18657067133265643 := by
  apply lucas_primality 18657067133265643 (2 : ZMod 18657067133265643)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18657067133265643 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((79 : ℕ)^1 * ((107 : ℕ)^1 * ((389 : ℕ)^1 * ((35024173 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 18657067133265643)^9328533566632821 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 18657067133265643)^6219022377755214 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (2 : ZMod 18657067133265643)^236165406750198 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
            subst q
            change (2 : ZMod 18657067133265643)^174365113395006 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 389 := Nat.prime_eq_prime_of_dvd_pow hq prime_389 hd
              subst q
              change (2 : ZMod 18657067133265643)^47961612167778 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 35024173 := Nat.prime_eq_prime_of_dvd_pow hq prime_35024173 hd
              subst q
              change (2 : ZMod 18657067133265643)^532691154 ≠ 1
              reduce_mod_char
              decide

theorem prime_18715948254710173 : Nat.Prime 18715948254710173 := by
  apply lucas_primality 18715948254710173 (7 : ZMod 18715948254710173)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18715948254710173 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((519887451519727 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 18715948254710173)^9357974127355086 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 18715948254710173)^6238649418236724 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 519887451519727 := Nat.prime_eq_prime_of_dvd_pow hq prime_519887451519727 hd
        subst q
        change (7 : ZMod 18715948254710173)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_18875488922505223 : Nat.Prime 18875488922505223 := by
  apply lucas_primality 18875488922505223 (3 : ZMod 18875488922505223)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 18875488922505223 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((449416402916791 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 18875488922505223)^9437744461252611 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 18875488922505223)^6291829640835074 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 18875488922505223)^2696498417500746 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 449416402916791 := Nat.prime_eq_prime_of_dvd_pow hq prime_449416402916791 hd
          subst q
          change (3 : ZMod 18875488922505223)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_19096037487458579 : Nat.Prime 19096037487458579 := by
  apply lucas_primality 19096037487458579 (2 : ZMod 19096037487458579)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19096037487458579 - 1 = (2 : ℕ)^1 * ((853 : ℕ)^1 * ((6393773 : ℕ)^1 * ((1750681 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 19096037487458579)^9548018743729289 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 853 := Nat.prime_eq_prime_of_dvd_pow hq prime_853 hd
        subst q
        change (2 : ZMod 19096037487458579)^22386913818826 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 6393773 := Nat.prime_eq_prime_of_dvd_pow hq prime_6393773 hd
          subst q
          change (2 : ZMod 19096037487458579)^2986661786 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1750681 := Nat.prime_eq_prime_of_dvd_pow hq prime_1750681 hd
          subst q
          change (2 : ZMod 19096037487458579)^10907776738 ≠ 1
          reduce_mod_char
          decide

theorem prime_19262171867740951 : Nat.Prime 19262171867740951 := by
  apply lucas_primality 19262171867740951 (3 : ZMod 19262171867740951)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19262171867740951 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((29 : ℕ)^1 * ((6971 : ℕ)^1 * ((635215247 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 19262171867740951)^9631085933870475 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 19262171867740951)^6420723955913650 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 19262171867740951)^3852434373548190 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (3 : ZMod 19262171867740951)^664212823025550 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 6971 := Nat.prime_eq_prime_of_dvd_pow hq prime_6971 hd
              subst q
              change (3 : ZMod 19262171867740951)^2763186324450 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 635215247 := Nat.prime_eq_prime_of_dvd_pow hq prime_635215247 hd
              subst q
              change (3 : ZMod 19262171867740951)^30323850 ≠ 1
              reduce_mod_char
              decide

theorem prime_19318729362716239 : Nat.Prime 19318729362716239 := by
  apply lucas_primality 19318729362716239 (6 : ZMod 19318729362716239)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19318729362716239 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((23 : ℕ)^1 * ((1538360356961 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 19318729362716239)^9659364681358119 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 19318729362716239)^6439576454238746 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 19318729362716239)^2759818480388034 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (6 : ZMod 19318729362716239)^1486056104824326 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
              subst q
              change (6 : ZMod 19318729362716239)^839944754900706 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1538360356961 := Nat.prime_eq_prime_of_dvd_pow hq prime_1538360356961 hd
              subst q
              change (6 : ZMod 19318729362716239)^12558 ≠ 1
              reduce_mod_char
              decide

theorem prime_19543581179092909 : Nat.Prime 19543581179092909 := by
  apply lucas_primality 19543581179092909 (6 : ZMod 19543581179092909)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19543581179092909 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((7 : ℕ)^2 * ((19 : ℕ)^1 * ((97 : ℕ)^1 * ((22447 : ℕ)^1 * ((89269 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 19543581179092909)^9771790589546454 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 19543581179092909)^6514527059697636 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 19543581179092909)^2791940168441844 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (6 : ZMod 19543581179092909)^1028609535741732 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
              subst q
              change (6 : ZMod 19543581179092909)^201480218341164 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 22447 := Nat.prime_eq_prime_of_dvd_pow hq prime_22447 hd
                subst q
                change (6 : ZMod 19543581179092909)^870654482964 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 89269 := Nat.prime_eq_prime_of_dvd_pow hq prime_89269 hd
                subst q
                change (6 : ZMod 19543581179092909)^218929092732 ≠ 1
                reduce_mod_char
                decide

theorem prime_19770609664000009 : Nat.Prime 19770609664000009 := by
  apply lucas_primality 19770609664000009 (7 : ZMod 19770609664000009)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19770609664000009 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((241 : ℕ)^1 * ((60259 : ℕ)^1 * ((101113 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 19770609664000009)^9885304832000004 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 19770609664000009)^6590203221333336 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (7 : ZMod 19770609664000009)^1797328151272728 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (7 : ZMod 19770609664000009)^1162977039058824 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 241 := Nat.prime_eq_prime_of_dvd_pow hq prime_241 hd
              subst q
              change (7 : ZMod 19770609664000009)^82035724746888 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 60259 := Nat.prime_eq_prime_of_dvd_pow hq prime_60259 hd
                subst q
                change (7 : ZMod 19770609664000009)^328093889112 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 101113 := Nat.prime_eq_prime_of_dvd_pow hq prime_101113 hd
                subst q
                change (7 : ZMod 19770609664000009)^195529849416 ≠ 1
                reduce_mod_char
                decide

theorem prime_19999831641819137 : Nat.Prime 19999831641819137 := by
  apply lucas_primality 19999831641819137 (3 : ZMod 19999831641819137)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 19999831641819137 - 1 = (2 : ℕ)^11 * ((113 : ℕ)^1 * ((86420732689 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 19999831641819137)^9999915820909568 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
        subst q
        change (3 : ZMod 19999831641819137)^176989660547072 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 86420732689 := Nat.prime_eq_prime_of_dvd_pow hq prime_86420732689 hd
        subst q
        change (3 : ZMod 19999831641819137)^231424 ≠ 1
        reduce_mod_char
        decide

theorem prime_20150531767011361 : Nat.Prime 20150531767011361 := by
  apply lucas_primality 20150531767011361 (17 : ZMod 20150531767011361)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20150531767011361 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((31 : ℕ)^1 * ((53 : ℕ)^1 * ((523 : ℕ)^1 * ((341641 : ℕ)^1)))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 20150531767011361)^10075265883505680 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 20150531767011361)^6716843922337120 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (17 : ZMod 20150531767011361)^4030106353402272 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (17 : ZMod 20150531767011361)^1831866524273760 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
              subst q
              change (17 : ZMod 20150531767011361)^1550040905154720 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
                subst q
                change (17 : ZMod 20150531767011361)^650017153774560 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
                  subst q
                  change (17 : ZMod 20150531767011361)^380198712585120 ≠ 1
                  reduce_mod_char
                  decide
                · rcases hq.dvd_mul.mp hd with hd | hd
                  · have heq : q = 523 := Nat.prime_eq_prime_of_dvd_pow hq prime_523 hd
                    subst q
                    change (17 : ZMod 20150531767011361)^38528741428320 ≠ 1
                    reduce_mod_char
                    decide
                  · have heq : q = 341641 := Nat.prime_eq_prime_of_dvd_pow hq prime_341641 hd
                    subst q
                    change (17 : ZMod 20150531767011361)^58981596960 ≠ 1
                    reduce_mod_char
                    decide

theorem prime_20231264034275911 : Nat.Prime 20231264034275911 := by
  apply lucas_primality 20231264034275911 (3 : ZMod 20231264034275911)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20231264034275911 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((8758122958561 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 20231264034275911)^10115632017137955 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 20231264034275911)^6743754678091970 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 20231264034275911)^4046252806855182 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (3 : ZMod 20231264034275911)^2890180576325130 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
              subst q
              change (3 : ZMod 20231264034275911)^1839205821297810 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 8758122958561 := Nat.prime_eq_prime_of_dvd_pow hq prime_8758122958561 hd
              subst q
              change (3 : ZMod 20231264034275911)^2310 ≠ 1
              reduce_mod_char
              decide

theorem prime_20464923860814911 : Nat.Prime 20464923860814911 := by
  apply lucas_primality 20464923860814911 (7 : ZMod 20464923860814911)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20464923860814911 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((44389 : ℕ)^1 * ((46103592919 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 20464923860814911)^10232461930407455 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 20464923860814911)^4092984772162982 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 44389 := Nat.prime_eq_prime_of_dvd_pow hq prime_44389 hd
          subst q
          change (7 : ZMod 20464923860814911)^461035929190 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 46103592919 := Nat.prime_eq_prime_of_dvd_pow hq prime_46103592919 hd
          subst q
          change (7 : ZMod 20464923860814911)^443890 ≠ 1
          reduce_mod_char
          decide

theorem prime_20700828238974979 : Nat.Prime 20700828238974979 := by
  apply lucas_primality 20700828238974979 (2 : ZMod 20700828238974979)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20700828238974979 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((491 : ℕ)^1 * ((413338689329 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 20700828238974979)^10350414119487489 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 20700828238974979)^6900276079658326 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 20700828238974979)^1217695778763234 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 491 := Nat.prime_eq_prime_of_dvd_pow hq prime_491 hd
            subst q
            change (2 : ZMod 20700828238974979)^42160546311558 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 413338689329 := Nat.prime_eq_prime_of_dvd_pow hq prime_413338689329 hd
            subst q
            change (2 : ZMod 20700828238974979)^50082 ≠ 1
            reduce_mod_char
            decide

theorem prime_20938994384765651 : Nat.Prime 20938994384765651 := by
  apply lucas_primality 20938994384765651 (2 : ZMod 20938994384765651)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20938994384765651 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((29 : ℕ)^1 * ((273929 : ℕ)^1 * ((52716893 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 20938994384765651)^10469497192382825 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 20938994384765651)^4187798876953130 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (2 : ZMod 20938994384765651)^722034289129850 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 273929 := Nat.prime_eq_prime_of_dvd_pow hq prime_273929 hd
            subst q
            change (2 : ZMod 20938994384765651)^76439494850 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 52716893 := Nat.prime_eq_prime_of_dvd_pow hq prime_52716893 hd
            subst q
            change (2 : ZMod 20938994384765651)^397197050 ≠ 1
            reduce_mod_char
            decide

theorem prime_21179439613043807 : Nat.Prime 21179439613043807 := by
  apply lucas_primality 21179439613043807 (5 : ZMod 21179439613043807)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21179439613043807 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((31 : ℕ)^1 * ((163 : ℕ)^1 * ((11839 : ℕ)^1 * ((7696483 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 21179439613043807)^10589719806521903 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (5 : ZMod 21179439613043807)^920845200567122 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (5 : ZMod 21179439613043807)^683207729453026 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
            subst q
            change (5 : ZMod 21179439613043807)^129935212349962 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 11839 := Nat.prime_eq_prime_of_dvd_pow hq prime_11839 hd
              subst q
              change (5 : ZMod 21179439613043807)^1788955115554 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 7696483 := Nat.prime_eq_prime_of_dvd_pow hq prime_7696483 hd
              subst q
              change (5 : ZMod 21179439613043807)^2751833482 ≠ 1
              reduce_mod_char
              decide

theorem prime_21422181337891507 : Nat.Prime 21422181337891507 := by
  apply lucas_primality 21422181337891507 (2 : ZMod 21422181337891507)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21422181337891507 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((17 : ℕ)^1 * ((3557 : ℕ)^1 * ((19681509293 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 21422181337891507)^10711090668945753 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 21422181337891507)^7140727112630502 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 21422181337891507)^1260128313993618 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3557 := Nat.prime_eq_prime_of_dvd_pow hq prime_3557 hd
            subst q
            change (2 : ZMod 21422181337891507)^6022541843658 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 19681509293 := Nat.prime_eq_prime_of_dvd_pow hq prime_19681509293 hd
            subst q
            change (2 : ZMod 21422181337891507)^1088442 ≠ 1
            reduce_mod_char
            decide

theorem prime_21667237072994321 : Nat.Prime 21667237072994321 := by
  apply lucas_primality 21667237072994321 (6 : ZMod 21667237072994321)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21667237072994321 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((17 : ℕ)^2 * ((937164233261 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 21667237072994321)^10833618536497160 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 21667237072994321)^4333447414598864 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (6 : ZMod 21667237072994321)^1274543357234960 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 937164233261 := Nat.prime_eq_prime_of_dvd_pow hq prime_937164233261 hd
          subst q
          change (6 : ZMod 21667237072994321)^23120 ≠ 1
          reduce_mod_char
          decide

theorem prime_21914624432020337 : Nat.Prime 21914624432020337 := by
  apply lucas_primality 21914624432020337 (3 : ZMod 21914624432020337)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21914624432020337 - 1 = (2 : ℕ)^4 * ((5059 : ℕ)^1 * ((270738095869 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 21914624432020337)^10957312216010168 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5059 := Nat.prime_eq_prime_of_dvd_pow hq prime_5059 hd
        subst q
        change (3 : ZMod 21914624432020337)^4331809533904 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 270738095869 := Nat.prime_eq_prime_of_dvd_pow hq prime_270738095869 hd
        subst q
        change (3 : ZMod 21914624432020337)^80944 ≠ 1
        reduce_mod_char
        decide

theorem prime_22164361129000033 : Nat.Prime 22164361129000033 := by
  apply lucas_primality 22164361129000033 (7 : ZMod 22164361129000033)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22164361129000033 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((8761 : ℕ)^1 * ((26353014697 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 22164361129000033)^11082180564500016 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 22164361129000033)^7388120376333344 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 8761 := Nat.prime_eq_prime_of_dvd_pow hq prime_8761 hd
          subst q
          change (7 : ZMod 22164361129000033)^2529889410912 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 26353014697 := Nat.prime_eq_prime_of_dvd_pow hq prime_26353014697 hd
          subst q
          change (7 : ZMod 22164361129000033)^841056 ≠ 1
          reduce_mod_char
          decide

theorem prime_22416464978706683 : Nat.Prime 22416464978706683 := by
  apply lucas_primality 22416464978706683 (5 : ZMod 22416464978706683)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22416464978706683 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((17 : ℕ)^1 * ((8293 : ℕ)^1 * ((10453 : ℕ)^1 * ((585049 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 22416464978706683)^11208232489353341 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (5 : ZMod 22416464978706683)^1724343459900514 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (5 : ZMod 22416464978706683)^1318615586982746 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 8293 := Nat.prime_eq_prime_of_dvd_pow hq prime_8293 hd
            subst q
            change (5 : ZMod 22416464978706683)^2703058601074 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 10453 := Nat.prime_eq_prime_of_dvd_pow hq prime_10453 hd
              subst q
              change (5 : ZMod 22416464978706683)^2144500619794 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 585049 := Nat.prime_eq_prime_of_dvd_pow hq prime_585049 hd
              subst q
              change (5 : ZMod 22416464978706683)^38315534218 ≠ 1
              reduce_mod_char
              decide

theorem prime_22439395680147059 : Nat.Prime 22439395680147059 := by
  apply lucas_primality 22439395680147059 (2 : ZMod 22439395680147059)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22439395680147059 - 1 = (2 : ℕ)^1 * ((139 : ℕ)^1 * ((354017 : ℕ)^1 * ((228003883 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 22439395680147059)^11219697840073529 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
        subst q
        change (2 : ZMod 22439395680147059)^161434501296022 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 354017 := Nat.prime_eq_prime_of_dvd_pow hq prime_354017 hd
          subst q
          change (2 : ZMod 22439395680147059)^63385079474 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 228003883 := Nat.prime_eq_prime_of_dvd_pow hq prime_228003883 hd
          subst q
          change (2 : ZMod 22439395680147059)^98416726 ≠ 1
          reduce_mod_char
          decide

theorem prime_22670953897037827 : Nat.Prime 22670953897037827 := by
  apply lucas_primality 22670953897037827 (2 : ZMod 22670953897037827)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22670953897037827 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((3778492316172971 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 22670953897037827)^11335476948518913 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 22670953897037827)^7556984632345942 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3778492316172971 := Nat.prime_eq_prime_of_dvd_pow hq prime_3778492316172971 hd
        subst q
        change (2 : ZMod 22670953897037827)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_22927845901397083 : Nat.Prime 22927845901397083 := by
  apply lucas_primality 22927845901397083 (3 : ZMod 22927845901397083)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 22927845901397083 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((23 : ℕ)^1 * ((59 : ℕ)^1 * ((859 : ℕ)^1 * ((172538251 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 22927845901397083)^11463922950698541 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 22927845901397083)^7642615300465694 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (3 : ZMod 22927845901397083)^1206728731652478 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (3 : ZMod 22927845901397083)^996862865278134 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
              subst q
              change (3 : ZMod 22927845901397083)^388607557650798 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 859 := Nat.prime_eq_prime_of_dvd_pow hq prime_859 hd
                subst q
                change (3 : ZMod 22927845901397083)^26691322353198 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 172538251 := Nat.prime_eq_prime_of_dvd_pow hq prime_172538251 hd
                subst q
                change (3 : ZMod 22927845901397083)^132885582 ≠ 1
                reduce_mod_char
                decide

theorem prime_23187159111076427 : Nat.Prime 23187159111076427 := by
  apply lucas_primality 23187159111076427 (2 : ZMod 23187159111076427)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23187159111076427 - 1 = (2 : ℕ)^1 * ((5476813 : ℕ)^1 * ((2116847801 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 23187159111076427)^11593579555538213 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5476813 := Nat.prime_eq_prime_of_dvd_pow hq prime_5476813 hd
        subst q
        change (2 : ZMod 23187159111076427)^4233695602 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2116847801 := Nat.prime_eq_prime_of_dvd_pow hq prime_2116847801 hd
        subst q
        change (2 : ZMod 23187159111076427)^10953626 ≠ 1
        reduce_mod_char
        decide

theorem prime_23311641601684211 : Nat.Prime 23311641601684211 := by
  apply lucas_primality 23311641601684211 (2 : ZMod 23311641601684211)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23311641601684211 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((2331164160168421 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 23311641601684211)^11655820800842105 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 23311641601684211)^4662328320336842 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2331164160168421 := Nat.prime_eq_prime_of_dvd_pow hq prime_2331164160168421 hd
        subst q
        change (2 : ZMod 23311641601684211)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_23448911747640661 : Nat.Prime 23448911747640661 := by
  apply lucas_primality 23448911747640661 (2 : ZMod 23448911747640661)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23448911747640661 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((43423910643779 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 23448911747640661)^11724455873820330 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 23448911747640661)^7816303915880220 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 23448911747640661)^4689782349528132 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 43423910643779 := Nat.prime_eq_prime_of_dvd_pow hq prime_43423910643779 hd
          subst q
          change (2 : ZMod 23448911747640661)^540 ≠ 1
          reduce_mod_char
          decide

theorem prime_23713122135310393 : Nat.Prime 23713122135310393 := by
  apply lucas_primality 23713122135310393 (5 : ZMod 23713122135310393)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23713122135310393 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((146117 : ℕ)^1 * ((6762024649 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 23713122135310393)^11856561067655196 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 23713122135310393)^7904374045103464 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 146117 := Nat.prime_eq_prime_of_dvd_pow hq prime_146117 hd
          subst q
          change (5 : ZMod 23713122135310393)^162288591576 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 6762024649 := Nat.prime_eq_prime_of_dvd_pow hq prime_6762024649 hd
          subst q
          change (5 : ZMod 23713122135310393)^3506808 ≠ 1
          reduce_mod_char
          decide

theorem prime_23979808701347437 : Nat.Prime 23979808701347437 := by
  apply lucas_primality 23979808701347437 (22 : ZMod 23979808701347437)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 23979808701347437 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((61 : ℕ)^1 * ((1567 : ℕ)^1 * ((3433 : ℕ)^1 * ((96661 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (22 : ZMod 23979808701347437)^11989904350673718 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (22 : ZMod 23979808701347437)^7993269567115812 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (22 : ZMod 23979808701347437)^3425686957335348 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
            subst q
            change (22 : ZMod 23979808701347437)^393111618054876 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1567 := Nat.prime_eq_prime_of_dvd_pow hq prime_1567 hd
              subst q
              change (22 : ZMod 23979808701347437)^15303004914708 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 3433 := Nat.prime_eq_prime_of_dvd_pow hq prime_3433 hd
                subst q
                change (22 : ZMod 23979808701347437)^6985088465292 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 96661 := Nat.prime_eq_prime_of_dvd_pow hq prime_96661 hd
                subst q
                change (22 : ZMod 23979808701347437)^248081529276 ≠ 1
                reduce_mod_char
                decide

theorem prime_24248989976440403 : Nat.Prime 24248989976440403 := by
  apply lucas_primality 24248989976440403 (2 : ZMod 24248989976440403)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24248989976440403 - 1 = (2 : ℕ)^1 * ((673 : ℕ)^1 * ((157867 : ℕ)^1 * ((114118811 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 24248989976440403)^12124494988220201 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 673 := Nat.prime_eq_prime_of_dvd_pow hq prime_673 hd
        subst q
        change (2 : ZMod 24248989976440403)^36031188672274 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 157867 := Nat.prime_eq_prime_of_dvd_pow hq prime_157867 hd
          subst q
          change (2 : ZMod 24248989976440403)^153603919606 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 114118811 := Nat.prime_eq_prime_of_dvd_pow hq prime_114118811 hd
          subst q
          change (2 : ZMod 24248989976440403)^212488982 ≠ 1
          reduce_mod_char
          decide

theorem prime_24416123090352547 : Nat.Prime 24416123090352547 := by
  apply lucas_primality 24416123090352547 (2 : ZMod 24416123090352547)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24416123090352547 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((29 : ℕ)^1 * ((20046078070897 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 24416123090352547)^12208061545176273 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 24416123090352547)^8138707696784182 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 24416123090352547)^3488017584336078 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (2 : ZMod 24416123090352547)^841935278977674 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 20046078070897 := Nat.prime_eq_prime_of_dvd_pow hq prime_20046078070897 hd
            subst q
            change (2 : ZMod 24416123090352547)^1218 ≠ 1
            reduce_mod_char
            decide

theorem prime_24520684595090767 : Nat.Prime 24520684595090767 := by
  apply lucas_primality 24520684595090767 (3 : ZMod 24520684595090767)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24520684595090767 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((127 : ℕ)^1 * ((449 : ℕ)^1 * ((71668989107 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 24520684595090767)^12260342297545383 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 24520684595090767)^8173561531696922 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
          subst q
          change (3 : ZMod 24520684595090767)^193076256654258 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 449 := Nat.prime_eq_prime_of_dvd_pow hq prime_449 hd
            subst q
            change (3 : ZMod 24520684595090767)^54611769699534 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 71668989107 := Nat.prime_eq_prime_of_dvd_pow hq prime_71668989107 hd
            subst q
            change (3 : ZMod 24520684595090767)^342138 ≠ 1
            reduce_mod_char
            decide

theorem prime_24794911296000101 : Nat.Prime 24794911296000101 := by
  apply lucas_primality 24794911296000101 (2 : ZMod 24794911296000101)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 24794911296000101 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((1489 : ℕ)^1 * ((528313 : ℕ)^1 * ((315193 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 24794911296000101)^12397455648000050 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 24794911296000101)^4958982259200020 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1489 := Nat.prime_eq_prime_of_dvd_pow hq prime_1489 hd
          subst q
          change (2 : ZMod 24794911296000101)^16652055940900 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 528313 := Nat.prime_eq_prime_of_dvd_pow hq prime_528313 hd
            subst q
            change (2 : ZMod 24794911296000101)^46932237700 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 315193 := Nat.prime_eq_prime_of_dvd_pow hq prime_315193 hd
            subst q
            change (2 : ZMod 24794911296000101)^78665805700 ≠ 1
            reduce_mod_char
            decide

theorem prime_25071688922457263 : Nat.Prime 25071688922457263 := by
  apply lucas_primality 25071688922457263 (5 : ZMod 25071688922457263)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 25071688922457263 - 1 = (2 : ℕ)^1 * ((179 : ℕ)^1 * ((28579 : ℕ)^1 * ((2450493391 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 25071688922457263)^12535844461228631 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 179 := Nat.prime_eq_prime_of_dvd_pow hq prime_179 hd
        subst q
        change (5 : ZMod 25071688922457263)^140065301242778 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 28579 := Nat.prime_eq_prime_of_dvd_pow hq prime_28579 hd
          subst q
          change (5 : ZMod 25071688922457263)^877276633978 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2450493391 := Nat.prime_eq_prime_of_dvd_pow hq prime_2450493391 hd
          subst q
          change (5 : ZMod 25071688922457263)^10231282 ≠ 1
          reduce_mod_char
          decide

theorem prime_25351036422727753 : Nat.Prime 25351036422727753 := by
  apply lucas_primality 25351036422727753 (5 : ZMod 25351036422727753)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 25351036422727753 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((19 : ℕ)^1 * ((43 : ℕ)^1 * ((1033 : ℕ)^1 * ((4451 : ℕ)^1 * ((8521 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 25351036422727753)^12675518211363876 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 25351036422727753)^8450345474242584 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 25351036422727753)^2304639674793432 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (5 : ZMod 25351036422727753)^1334265074880408 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
              subst q
              change (5 : ZMod 25351036422727753)^589558986575064 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 1033 := Nat.prime_eq_prime_of_dvd_pow hq prime_1033 hd
                subst q
                change (5 : ZMod 25351036422727753)^24541177563144 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 4451 := Nat.prime_eq_prime_of_dvd_pow hq prime_4451 hd
                  subst q
                  change (5 : ZMod 25351036422727753)^5695582211352 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 8521 := Nat.prime_eq_prime_of_dvd_pow hq prime_8521 hd
                  subst q
                  change (5 : ZMod 25351036422727753)^2975124565512 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_25632972850442059 : Nat.Prime 25632972850442059 := by
  apply lucas_primality 25632972850442059 (3 : ZMod 25632972850442059)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 25632972850442059 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((61 : ℕ)^1 * ((193 : ℕ)^1 * ((120959317697 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 25632972850442059)^12816486425221029 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 25632972850442059)^8544324283480686 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (3 : ZMod 25632972850442059)^420212669679378 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
            subst q
            change (3 : ZMod 25632972850442059)^132813330831306 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 120959317697 := Nat.prime_eq_prime_of_dvd_pow hq prime_120959317697 hd
            subst q
            change (3 : ZMod 25632972850442059)^211914 ≠ 1
            reduce_mod_char
            decide

theorem prime_25917517364985863 : Nat.Prime 25917517364985863 := by
  apply lucas_primality 25917517364985863 (5 : ZMod 25917517364985863)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 25917517364985863 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^2 * ((11 : ℕ)^1 * ((351179 : ℕ)^1 * ((68461451 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 25917517364985863)^12958758682492931 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 25917517364985863)^3702502480712266 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 25917517364985863)^2356137942271442 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 351179 := Nat.prime_eq_prime_of_dvd_pow hq prime_351179 hd
            subst q
            change (5 : ZMod 25917517364985863)^73801444178 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 68461451 := Nat.prime_eq_prime_of_dvd_pow hq prime_68461451 hd
            subst q
            change (5 : ZMod 25917517364985863)^378570962 ≠ 1
            reduce_mod_char
            decide

theorem prime_26204689231890683 : Nat.Prime 26204689231890683 := by
  apply lucas_primality 26204689231890683 (2 : ZMod 26204689231890683)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26204689231890683 - 1 = (2 : ℕ)^1 * ((79 : ℕ)^1 * ((165852463492979 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 26204689231890683)^13102344615945341 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
        subst q
        change (2 : ZMod 26204689231890683)^331704926985958 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 165852463492979 := Nat.prime_eq_prime_of_dvd_pow hq prime_165852463492979 hd
        subst q
        change (2 : ZMod 26204689231890683)^158 ≠ 1
        reduce_mod_char
        decide

theorem prime_26492054245386923 : Nat.Prime 26492054245386923 := by
  apply lucas_primality 26492054245386923 (2 : ZMod 26492054245386923)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26492054245386923 - 1 = (2 : ℕ)^1 * ((727 : ℕ)^1 * ((2099 : ℕ)^1 * ((31657 : ℕ)^1 * ((274201 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 26492054245386923)^13246027122693461 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 727 := Nat.prime_eq_prime_of_dvd_pow hq prime_727 hd
        subst q
        change (2 : ZMod 26492054245386923)^36440239677286 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2099 := Nat.prime_eq_prime_of_dvd_pow hq prime_2099 hd
          subst q
          change (2 : ZMod 26492054245386923)^12621274056878 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 31657 := Nat.prime_eq_prime_of_dvd_pow hq prime_31657 hd
            subst q
            change (2 : ZMod 26492054245386923)^836846645146 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 274201 := Nat.prime_eq_prime_of_dvd_pow hq prime_274201 hd
            subst q
            change (2 : ZMod 26492054245386923)^96615454522 ≠ 1
            reduce_mod_char
            decide

theorem prime_26494507823224937 : Nat.Prime 26494507823224937 := by
  apply lucas_primality 26494507823224937 (5 : ZMod 26494507823224937)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26494507823224937 - 1 = (2 : ℕ)^3 * ((11 : ℕ)^1 * ((53 : ℕ)^1 * ((11213 : ℕ)^1 * ((506612023 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 26494507823224937)^13247253911612468 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 26494507823224937)^2408591620293176 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (5 : ZMod 26494507823224937)^499896374023112 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11213 := Nat.prime_eq_prime_of_dvd_pow hq prime_11213 hd
            subst q
            change (5 : ZMod 26494507823224937)^2362838475272 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 506612023 := Nat.prime_eq_prime_of_dvd_pow hq prime_506612023 hd
            subst q
            change (5 : ZMod 26494507823224937)^52297432 ≠ 1
            reduce_mod_char
            decide

theorem prime_26786992617986357 : Nat.Prime 26786992617986357 := by
  apply lucas_primality 26786992617986357 (2 : ZMod 26786992617986357)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 26786992617986357 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((19 : ℕ)^1 * ((31 : ℕ)^1 * ((127 : ℕ)^1 * ((337 : ℕ)^1 * ((883 : ℕ)^1 * ((42979 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 26786992617986357)^13393496308993178 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 26786992617986357)^3826713231140908 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 26786992617986357)^1409841716736124 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (2 : ZMod 26786992617986357)^864096536064076 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
              subst q
              change (2 : ZMod 26786992617986357)^210921201716428 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 337 := Nat.prime_eq_prime_of_dvd_pow hq prime_337 hd
                subst q
                change (2 : ZMod 26786992617986357)^79486624979188 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 883 := Nat.prime_eq_prime_of_dvd_pow hq prime_883 hd
                  subst q
                  change (2 : ZMod 26786992617986357)^30336344980732 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 42979 := Nat.prime_eq_prime_of_dvd_pow hq prime_42979 hd
                  subst q
                  change (2 : ZMod 26786992617986357)^623257698364 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_27082163202494479 : Nat.Prime 27082163202494479 := by
  apply lucas_primality 27082163202494479 (6 : ZMod 27082163202494479)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 27082163202494479 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((159097 : ℕ)^1 * ((2182361833 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 27082163202494479)^13541081601247239 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 27082163202494479)^9027387734164826 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (6 : ZMod 27082163202494479)^2083243323268806 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 159097 := Nat.prime_eq_prime_of_dvd_pow hq prime_159097 hd
            subst q
            change (6 : ZMod 27082163202494479)^170224222974 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2182361833 := Nat.prime_eq_prime_of_dvd_pow hq prime_2182361833 hd
            subst q
            change (6 : ZMod 27082163202494479)^12409566 ≠ 1
            reduce_mod_char
            decide

theorem prime_27380039270784257 : Nat.Prime 27380039270784257 := by
  apply lucas_primality 27380039270784257 (3 : ZMod 27380039270784257)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 27380039270784257 - 1 = (2 : ℕ)^8 * ((7 : ℕ)^1 * ((9613 : ℕ)^1 * ((1589414311 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 27380039270784257)^13690019635392128 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 27380039270784257)^3911434181540608 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 9613 := Nat.prime_eq_prime_of_dvd_pow hq prime_9613 hd
          subst q
          change (3 : ZMod 27380039270784257)^2848230445312 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1589414311 := Nat.prime_eq_prime_of_dvd_pow hq prime_1589414311 hd
          subst q
          change (3 : ZMod 27380039270784257)^17226496 ≠ 1
          reduce_mod_char
          decide

theorem prime_27680640625000067 : Nat.Prime 27680640625000067 := by
  apply lucas_primality 27680640625000067 (2 : ZMod 27680640625000067)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 27680640625000067 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((1258210937500003 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 27680640625000067)^13840320312500033 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 27680640625000067)^2516421875000006 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1258210937500003 := Nat.prime_eq_prime_of_dvd_pow hq prime_1258210937500003 hd
        subst q
        change (2 : ZMod 27680640625000067)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_27983987175790813 : Nat.Prime 27983987175790813 := by
  apply lucas_primality 27983987175790813 (2 : ZMod 27983987175790813)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 27983987175790813 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((37 : ℕ)^1 * ((63026998143673 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 27983987175790813)^13991993587895406 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 27983987175790813)^9327995725263604 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (2 : ZMod 27983987175790813)^756323977724076 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 63026998143673 := Nat.prime_eq_prime_of_dvd_pow hq prime_63026998143673 hd
          subst q
          change (2 : ZMod 27983987175790813)^444 ≠ 1
          reduce_mod_char
          decide

theorem prime_28290098942705681 : Nat.Prime 28290098942705681 := by
  apply lucas_primality 28290098942705681 (15 : ZMod 28290098942705681)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 28290098942705681 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((89 : ℕ)^1 * ((3973328503189 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (15 : ZMod 28290098942705681)^14145049471352840 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (15 : ZMod 28290098942705681)^5658019788541136 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (15 : ZMod 28290098942705681)^317866280255120 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3973328503189 := Nat.prime_eq_prime_of_dvd_pow hq prime_3973328503189 hd
          subst q
          change (15 : ZMod 28290098942705681)^7120 ≠ 1
          reduce_mod_char
          decide

theorem prime_28598996054590147 : Nat.Prime 28598996054590147 := by
  apply lucas_primality 28598996054590147 (2 : ZMod 28598996054590147)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 28598996054590147 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((1588833114143897 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 28598996054590147)^14299498027295073 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 28598996054590147)^9532998684863382 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1588833114143897 := Nat.prime_eq_prime_of_dvd_pow hq prime_1588833114143897 hd
        subst q
        change (2 : ZMod 28598996054590147)^18 ≠ 1
        reduce_mod_char
        decide

end LegendreK6.Pratt
