import LegendreK6.Pratt.Block025

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LegendreK6.Pratt

theorem prime_1880547699518858219 : Nat.Prime 1880547699518858219 := by
  apply lucas_primality 1880547699518858219 (2 : ZMod 1880547699518858219)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1880547699518858219 - 1 = (2 : ℕ)^1 * ((233297 : ℕ)^1 * ((4030372656997 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1880547699518858219)^940273849759429109 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 233297 := Nat.prime_eq_prime_of_dvd_pow hq prime_233297 hd
        subst q
        change (2 : ZMod 1880547699518858219)^8060745313994 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4030372656997 := Nat.prime_eq_prime_of_dvd_pow hq prime_4030372656997 hd
        subst q
        change (2 : ZMod 1880547699518858219)^466594 ≠ 1
        reduce_mod_char
        decide

theorem prime_1890726553363677193 : Nat.Prime 1890726553363677193 := by
  apply lucas_primality 1890726553363677193 (5 : ZMod 1890726553363677193)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1890726553363677193 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^5 * ((17 : ℕ)^1 * ((19 : ℕ)^1 * ((449 : ℕ)^1 * ((2593 : ℕ)^1 * ((2586313 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1890726553363677193)^945363276681838596 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1890726553363677193)^630242184454559064 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (5 : ZMod 1890726553363677193)^111219209021392776 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (5 : ZMod 1890726553363677193)^99511923861246168 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 449 := Nat.prime_eq_prime_of_dvd_pow hq prime_449 hd
              subst q
              change (5 : ZMod 1890726553363677193)^4210972279206408 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 2593 := Nat.prime_eq_prime_of_dvd_pow hq prime_2593 hd
                subst q
                change (5 : ZMod 1890726553363677193)^729165658836744 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 2586313 := Nat.prime_eq_prime_of_dvd_pow hq prime_2586313 hd
                subst q
                change (5 : ZMod 1890726553363677193)^731050941384 ≠ 1
                reduce_mod_char
                decide

theorem prime_1900951278477510613 : Nat.Prime 1900951278477510613 := by
  apply lucas_primality 1900951278477510613 (5 : ZMod 1900951278477510613)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1900951278477510613 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((158412606539792551 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1900951278477510613)^950475639238755306 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1900951278477510613)^633650426159170204 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 158412606539792551 := Nat.prime_eq_prime_of_dvd_pow hq prime_158412606539792551 hd
        subst q
        change (5 : ZMod 1900951278477510613)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_1911222040087567939 : Nat.Prime 1911222040087567939 := by
  apply lucas_primality 1911222040087567939 (2 : ZMod 1911222040087567939)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1911222040087567939 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((318537006681261323 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1911222040087567939)^955611020043783969 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1911222040087567939)^637074013362522646 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 318537006681261323 := Nat.prime_eq_prime_of_dvd_pow hq prime_318537006681261323 hd
        subst q
        change (2 : ZMod 1911222040087567939)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_1921539003867015653 : Nat.Prime 1921539003867015653 := by
  apply lucas_primality 1921539003867015653 (2 : ZMod 1921539003867015653)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1921539003867015653 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^2 * ((19 : ℕ)^1 * ((6343 : ℕ)^1 * ((65257 : ℕ)^1 * ((1246573 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1921539003867015653)^960769501933507826 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 1921539003867015653)^274505571981002236 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (2 : ZMod 1921539003867015653)^101133631782474508 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 6343 := Nat.prime_eq_prime_of_dvd_pow hq prime_6343 hd
            subst q
            change (2 : ZMod 1921539003867015653)^302938515507964 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 65257 := Nat.prime_eq_prime_of_dvd_pow hq prime_65257 hd
              subst q
              change (2 : ZMod 1921539003867015653)^29445714695236 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1246573 := Nat.prime_eq_prime_of_dvd_pow hq prime_1246573 hd
              subst q
              change (2 : ZMod 1921539003867015653)^1541457262324 ≠ 1
              reduce_mod_char
              decide

theorem prime_1931902335935778889 : Nat.Prime 1931902335935778889 := by
  apply lucas_primality 1931902335935778889 (13 : ZMod 1931902335935778889)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1931902335935778889 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((63299 : ℕ)^1 * ((38535689761 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 1931902335935778889)^965951167967889444 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 1931902335935778889)^643967445311926296 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (13 : ZMod 1931902335935778889)^175627485085070808 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 63299 := Nat.prime_eq_prime_of_dvd_pow hq prime_63299 hd
            subst q
            change (13 : ZMod 1931902335935778889)^30520266290712 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 38535689761 := Nat.prime_eq_prime_of_dvd_pow hq prime_38535689761 hd
            subst q
            change (13 : ZMod 1931902335935778889)^50132808 ≠ 1
            reduce_mod_char
            decide

theorem prime_1942312202861343823 : Nat.Prime 1942312202861343823 := by
  apply lucas_primality 1942312202861343823 (5 : ZMod 1942312202861343823)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1942312202861343823 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((29 : ℕ)^1 * ((2267 : ℕ)^1 * ((96851 : ℕ)^1 * ((5649001 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1942312202861343823)^971156101430671911 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1942312202861343823)^647437400953781274 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (5 : ZMod 1942312202861343823)^66976282857287718 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2267 := Nat.prime_eq_prime_of_dvd_pow hq prime_2267 hd
            subst q
            change (5 : ZMod 1942312202861343823)^856776445902666 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 96851 := Nat.prime_eq_prime_of_dvd_pow hq prime_96851 hd
              subst q
              change (5 : ZMod 1942312202861343823)^20054642728122 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 5649001 := Nat.prime_eq_prime_of_dvd_pow hq prime_5649001 hd
              subst q
              change (5 : ZMod 1942312202861343823)^343832865822 ≠ 1
              reduce_mod_char
              decide

theorem prime_1952768771659561069 : Nat.Prime 1952768771659561069 := by
  apply lucas_primality 1952768771659561069 (2 : ZMod 1952768771659561069)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1952768771659561069 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((18081192330181121 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1952768771659561069)^976384385829780534 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1952768771659561069)^650922923886520356 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 18081192330181121 := Nat.prime_eq_prime_of_dvd_pow hq prime_18081192330181121 hd
        subst q
        change (2 : ZMod 1952768771659561069)^108 ≠ 1
        reduce_mod_char
        decide

theorem prime_1963272209795449339 : Nat.Prime 1963272209795449339 := by
  apply lucas_primality 1963272209795449339 (13 : ZMod 1963272209795449339)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1963272209795449339 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1063 : ℕ)^1 * ((3631 : ℕ)^1 * ((893567 : ℕ)^1 * ((94873 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 1963272209795449339)^981636104897724669 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 1963272209795449339)^654424069931816446 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1063 := Nat.prime_eq_prime_of_dvd_pow hq prime_1063 hd
          subst q
          change (13 : ZMod 1963272209795449339)^1846916472055926 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3631 := Nat.prime_eq_prime_of_dvd_pow hq prime_3631 hd
            subst q
            change (13 : ZMod 1963272209795449339)^540697386338598 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 893567 := Nat.prime_eq_prime_of_dvd_pow hq prime_893567 hd
              subst q
              change (13 : ZMod 1963272209795449339)^2197118078214 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 94873 := Nat.prime_eq_prime_of_dvd_pow hq prime_94873 hd
              subst q
              change (13 : ZMod 1963272209795449339)^20693687453706 ≠ 1
              reduce_mod_char
              decide

theorem prime_1973822685184000031 : Nat.Prime 1973822685184000031 := by
  apply lucas_primality 1973822685184000031 (17 : ZMod 1973822685184000031)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1973822685184000031 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((257 : ℕ)^1 * ((2217491 : ℕ)^1 * ((346348369 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 1973822685184000031)^986911342592000015 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (17 : ZMod 1973822685184000031)^394764537036800006 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 257 := Nat.prime_eq_prime_of_dvd_pow hq prime_257 hd
          subst q
          change (17 : ZMod 1973822685184000031)^7680243911221790 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2217491 := Nat.prime_eq_prime_of_dvd_pow hq prime_2217491 hd
            subst q
            change (17 : ZMod 1973822685184000031)^890115308330 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 346348369 := Nat.prime_eq_prime_of_dvd_pow hq prime_346348369 hd
            subst q
            change (17 : ZMod 1973822685184000031)^5698951870 ≠ 1
            reduce_mod_char
            decide

theorem prime_1984420366190982743 : Nat.Prime 1984420366190982743 := by
  apply lucas_primality 1984420366190982743 (5 : ZMod 1984420366190982743)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1984420366190982743 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((90200925735953761 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1984420366190982743)^992210183095491371 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 1984420366190982743)^180401851471907522 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 90200925735953761 := Nat.prime_eq_prime_of_dvd_pow hq prime_90200925735953761 hd
        subst q
        change (5 : ZMod 1984420366190982743)^22 ≠ 1
        reduce_mod_char
        decide

theorem prime_1995065421633751133 : Nat.Prime 1995065421633751133 := by
  apply lucas_primality 1995065421633751133 (2 : ZMod 1995065421633751133)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1995065421633751133 - 1 = (2 : ℕ)^2 * ((5119 : ℕ)^1 * ((97434333934057 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1995065421633751133)^997532710816875566 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5119 := Nat.prime_eq_prime_of_dvd_pow hq prime_5119 hd
        subst q
        change (2 : ZMod 1995065421633751133)^389737335736228 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 97434333934057 := Nat.prime_eq_prime_of_dvd_pow hq prime_97434333934057 hd
        subst q
        change (2 : ZMod 1995065421633751133)^20476 ≠ 1
        reduce_mod_char
        decide

theorem prime_2005758020782049867 : Nat.Prime 2005758020782049867 := by
  apply lucas_primality 2005758020782049867 (2 : ZMod 2005758020782049867)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2005758020782049867 - 1 = (2 : ℕ)^1 * ((1987 : ℕ)^1 * ((504720186407159 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2005758020782049867)^1002879010391024933 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1987 := Nat.prime_eq_prime_of_dvd_pow hq prime_1987 hd
        subst q
        change (2 : ZMod 2005758020782049867)^1009440372814318 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 504720186407159 := Nat.prime_eq_prime_of_dvd_pow hq prime_504720186407159 hd
        subst q
        change (2 : ZMod 2005758020782049867)^3974 ≠ 1
        reduce_mod_char
        decide

theorem prime_2016498333358821379 : Nat.Prime 2016498333358821379 := by
  apply lucas_primality 2016498333358821379 (7 : ZMod 2016498333358821379)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2016498333358821379 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((83 : ℕ)^1 * ((953 : ℕ)^1 * ((463291 : ℕ)^1 * ((833737 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2016498333358821379)^1008249166679410689 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 2016498333358821379)^672166111119607126 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (7 : ZMod 2016498333358821379)^183318030305347398 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
            subst q
            change (7 : ZMod 2016498333358821379)^24295160642877366 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 953 := Nat.prime_eq_prime_of_dvd_pow hq prime_953 hd
              subst q
              change (7 : ZMod 2016498333358821379)^2115947883902226 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 463291 := Nat.prime_eq_prime_of_dvd_pow hq prime_463291 hd
                subst q
                change (7 : ZMod 2016498333358821379)^4352552355558 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 833737 := Nat.prime_eq_prime_of_dvd_pow hq prime_833737 hd
                subst q
                change (7 : ZMod 2016498333358821379)^2418626417394 ≠ 1
                reduce_mod_char
                decide

theorem prime_2027286529541015657 : Nat.Prime 2027286529541015657 := by
  apply lucas_primality 2027286529541015657 (3 : ZMod 2027286529541015657)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2027286529541015657 - 1 = (2 : ℕ)^3 * ((71 : ℕ)^1 * ((3569166425248267 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2027286529541015657)^1013643264770507828 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
        subst q
        change (3 : ZMod 2027286529541015657)^28553331401986136 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3569166425248267 := Nat.prime_eq_prime_of_dvd_pow hq prime_3569166425248267 hd
        subst q
        change (3 : ZMod 2027286529541015657)^568 ≠ 1
        reduce_mod_char
        decide

theorem prime_2038122779960397539 : Nat.Prime 2038122779960397539 := by
  apply lucas_primality 2038122779960397539 (2 : ZMod 2038122779960397539)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2038122779960397539 - 1 = (2 : ℕ)^1 * ((259637017 : ℕ)^1 * ((3924946457 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2038122779960397539)^1019061389980198769 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 259637017 := Nat.prime_eq_prime_of_dvd_pow hq prime_259637017 hd
        subst q
        change (2 : ZMod 2038122779960397539)^7849892914 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3924946457 := Nat.prime_eq_prime_of_dvd_pow hq prime_3924946457 hd
        subst q
        change (2 : ZMod 2038122779960397539)^519274034 ≠ 1
        reduce_mod_char
        decide

theorem prime_2049007255704356777 : Nat.Prime 2049007255704356777 := by
  apply lucas_primality 2049007255704356777 (3 : ZMod 2049007255704356777)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2049007255704356777 - 1 = (2 : ℕ)^3 * ((60050971 : ℕ)^1 * ((4265141807 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2049007255704356777)^1024503627852178388 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 60050971 := Nat.prime_eq_prime_of_dvd_pow hq prime_60050971 hd
        subst q
        change (3 : ZMod 2049007255704356777)^34121134456 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4265141807 := Nat.prime_eq_prime_of_dvd_pow hq prime_4265141807 hd
        subst q
        change (3 : ZMod 2049007255704356777)^480407768 ≠ 1
        reduce_mod_char
        decide

theorem prime_2059940128316719183 : Nat.Prime 2059940128316719183 := by
  apply lucas_primality 2059940128316719183 (6 : ZMod 2059940128316719183)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2059940128316719183 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((2221 : ℕ)^1 * ((154580528914657 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 2059940128316719183)^1029970064158359591 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 2059940128316719183)^686646709438906394 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2221 := Nat.prime_eq_prime_of_dvd_pow hq prime_2221 hd
          subst q
          change (6 : ZMod 2059940128316719183)^927483173487942 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 154580528914657 := Nat.prime_eq_prime_of_dvd_pow hq prime_154580528914657 hd
          subst q
          change (6 : ZMod 2059940128316719183)^13326 ≠ 1
          reduce_mod_char
          decide

theorem prime_2070921569798556731 : Nat.Prime 2070921569798556731 := by
  apply lucas_primality 2070921569798556731 (2 : ZMod 2070921569798556731)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2070921569798556731 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((9421 : ℕ)^1 * ((21981971869213 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2070921569798556731)^1035460784899278365 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 2070921569798556731)^414184313959711346 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 9421 := Nat.prime_eq_prime_of_dvd_pow hq prime_9421 hd
          subst q
          change (2 : ZMod 2070921569798556731)^219819718692130 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 21981971869213 := Nat.prime_eq_prime_of_dvd_pow hq prime_21981971869213 hd
          subst q
          change (2 : ZMod 2070921569798556731)^94210 ≠ 1
          reduce_mod_char
          decide

theorem prime_2081951752609000037 : Nat.Prime 2081951752609000037 := by
  apply lucas_primality 2081951752609000037 (2 : ZMod 2081951752609000037)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2081951752609000037 - 1 = (2 : ℕ)^2 * ((181 : ℕ)^1 * ((2875623967691989 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2081951752609000037)^1040975876304500018 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 181 := Nat.prime_eq_prime_of_dvd_pow hq prime_181 hd
        subst q
        change (2 : ZMod 2081951752609000037)^11502495870767956 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2875623967691989 := Nat.prime_eq_prime_of_dvd_pow hq prime_2875623967691989 hd
        subst q
        change (2 : ZMod 2081951752609000037)^724 ≠ 1
        reduce_mod_char
        decide

theorem prime_2093030849666050363 : Nat.Prime 2093030849666050363 := by
  apply lucas_primality 2093030849666050363 (2 : ZMod 2093030849666050363)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2093030849666050363 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((17 : ℕ)^1 * ((18325033 : ℕ)^1 * ((41473141 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2093030849666050363)^1046515424833025181 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2093030849666050363)^697676949888683454 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 2093030849666050363)^123119461745061786 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 18325033 := Nat.prime_eq_prime_of_dvd_pow hq prime_18325033 hd
            subst q
            change (2 : ZMod 2093030849666050363)^114217030314 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 41473141 := Nat.prime_eq_prime_of_dvd_pow hq prime_41473141 hd
            subst q
            change (2 : ZMod 2093030849666050363)^50467140882 ≠ 1
            reduce_mod_char
            decide

theorem prime_2104159034347393031 : Nat.Prime 2104159034347393031 := by
  apply lucas_primality 2104159034347393031 (7 : ZMod 2104159034347393031)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2104159034347393031 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^2 * ((1273739 : ℕ)^1 * ((3371335973 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2104159034347393031)^1052079517173696515 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 2104159034347393031)^420831806869478606 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 2104159034347393031)^300594147763913290 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1273739 := Nat.prime_eq_prime_of_dvd_pow hq prime_1273739 hd
            subst q
            change (7 : ZMod 2104159034347393031)^1651954626770 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3371335973 := Nat.prime_eq_prime_of_dvd_pow hq prime_3371335973 hd
            subst q
            change (7 : ZMod 2104159034347393031)^624132110 ≠ 1
            reduce_mod_char
            decide

theorem prime_2115336480491211797 : Nat.Prime 2115336480491211797 := by
  apply lucas_primality 2115336480491211797 (2 : ZMod 2115336480491211797)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2115336480491211797 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((181 : ℕ)^1 * ((547 : ℕ)^1 * ((182899 : ℕ)^1 * ((320923 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2115336480491211797)^1057668240245605898 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 2115336480491211797)^302190925784458828 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 2115336480491211797)^162718190807016292 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 181 := Nat.prime_eq_prime_of_dvd_pow hq prime_181 hd
            subst q
            change (2 : ZMod 2115336480491211797)^11686941881166916 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 547 := Nat.prime_eq_prime_of_dvd_pow hq prime_547 hd
              subst q
              change (2 : ZMod 2115336480491211797)^3867159927771868 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 182899 := Nat.prime_eq_prime_of_dvd_pow hq prime_182899 hd
                subst q
                change (2 : ZMod 2115336480491211797)^11565598939804 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 320923 := Nat.prime_eq_prime_of_dvd_pow hq prime_320923 hd
                subst q
                change (2 : ZMod 2115336480491211797)^6591414390652 ≠ 1
                reduce_mod_char
                decide

theorem prime_2126563362397002839 : Nat.Prime 2126563362397002839 := by
  apply lucas_primality 2126563362397002839 (7 : ZMod 2126563362397002839)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2126563362397002839 - 1 = (2 : ℕ)^1 * ((137 : ℕ)^1 * ((7761180154733587 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2126563362397002839)^1063281681198501419 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
        subst q
        change (7 : ZMod 2126563362397002839)^15522360309467174 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7761180154733587 := Nat.prime_eq_prime_of_dvd_pow hq prime_7761180154733587 hd
        subst q
        change (7 : ZMod 2126563362397002839)^274 ≠ 1
        reduce_mod_char
        decide

theorem prime_2137839854826390697 : Nat.Prime 2137839854826390697 := by
  apply lucas_primality 2137839854826390697 (5 : ZMod 2137839854826390697)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2137839854826390697 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((29692220205922093 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2137839854826390697)^1068919927413195348 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 2137839854826390697)^712613284942130232 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 29692220205922093 := Nat.prime_eq_prime_of_dvd_pow hq prime_29692220205922093 hd
        subst q
        change (5 : ZMod 2137839854826390697)^72 ≠ 1
        reduce_mod_char
        decide

theorem prime_2149166133003943987 : Nat.Prime 2149166133003943987 := by
  apply lucas_primality 2149166133003943987 (2 : ZMod 2149166133003943987)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2149166133003943987 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((358194355500657331 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2149166133003943987)^1074583066501971993 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2149166133003943987)^716388711001314662 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 358194355500657331 := Nat.prime_eq_prime_of_dvd_pow hq prime_358194355500657331 hd
        subst q
        change (2 : ZMod 2149166133003943987)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_2160542372617992619 : Nat.Prime 2160542372617992619 := by
  apply lucas_primality 2160542372617992619 (2 : ZMod 2160542372617992619)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2160542372617992619 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((120030131812110701 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2160542372617992619)^1080271186308996309 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2160542372617992619)^720180790872664206 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 120030131812110701 := Nat.prime_eq_prime_of_dvd_pow hq prime_120030131812110701 hd
        subst q
        change (2 : ZMod 2160542372617992619)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_2171968749821445227 : Nat.Prime 2171968749821445227 := by
  apply lucas_primality 2171968749821445227 (2 : ZMod 2171968749821445227)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2171968749821445227 - 1 = (2 : ℕ)^1 * ((83 : ℕ)^1 * ((868051 : ℕ)^1 * ((15073018861 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2171968749821445227)^1085984374910722613 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
        subst q
        change (2 : ZMod 2171968749821445227)^26168298190619822 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 868051 := Nat.prime_eq_prime_of_dvd_pow hq prime_868051 hd
          subst q
          change (2 : ZMod 2171968749821445227)^2502121130926 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 15073018861 := Nat.prime_eq_prime_of_dvd_pow hq prime_15073018861 hd
          subst q
          change (2 : ZMod 2171968749821445227)^144096466 ≠ 1
          reduce_mod_char
          decide

theorem prime_2183445441232607173 : Nat.Prime 2183445441232607173 := by
  apply lucas_primality 2183445441232607173 (2 : ZMod 2183445441232607173)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2183445441232607173 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((587 : ℕ)^1 * ((36107 : ℕ)^1 * ((8584827859 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2183445441232607173)^1091722720616303586 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2183445441232607173)^727815147077535724 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 587 := Nat.prime_eq_prime_of_dvd_pow hq prime_587 hd
          subst q
          change (2 : ZMod 2183445441232607173)^3719668554058956 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 36107 := Nat.prime_eq_prime_of_dvd_pow hq prime_36107 hd
            subst q
            change (2 : ZMod 2183445441232607173)^60471527438796 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 8584827859 := Nat.prime_eq_prime_of_dvd_pow hq prime_8584827859 hd
            subst q
            change (2 : ZMod 2183445441232607173)^254337708 ≠ 1
            reduce_mod_char
            decide

theorem prime_2194972623936000023 : Nat.Prime 2194972623936000023 := by
  apply lucas_primality 2194972623936000023 (5 : ZMod 2194972623936000023)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2194972623936000023 - 1 = (2 : ℕ)^1 * ((71 : ℕ)^1 * ((97 : ℕ)^1 * ((32503 : ℕ)^1 * ((50593 : ℕ)^1 * ((96907 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2194972623936000023)^1097486311968000011 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
        subst q
        change (5 : ZMod 2194972623936000023)^30915107379380282 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
          subst q
          change (5 : ZMod 2194972623936000023)^22628583751917526 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 32503 := Nat.prime_eq_prime_of_dvd_pow hq prime_32503 hd
            subst q
            change (5 : ZMod 2194972623936000023)^67531385531674 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 50593 := Nat.prime_eq_prime_of_dvd_pow hq prime_50593 hd
              subst q
              change (5 : ZMod 2194972623936000023)^43384907476054 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 96907 := Nat.prime_eq_prime_of_dvd_pow hq prime_96907 hd
              subst q
              change (5 : ZMod 2194972623936000023)^22650300018946 ≠ 1
              reduce_mod_char
              decide

theorem prime_2206550475483180889 : Nat.Prime 2206550475483180889 := by
  apply lucas_primality 2206550475483180889 (7 : ZMod 2206550475483180889)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2206550475483180889 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((660791 : ℕ)^1 * ((139135677007 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2206550475483180889)^1103275237741590444 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 2206550475483180889)^735516825161060296 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 660791 := Nat.prime_eq_prime_of_dvd_pow hq prime_660791 hd
          subst q
          change (7 : ZMod 2206550475483180889)^3339256248168 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 139135677007 := Nat.prime_eq_prime_of_dvd_pow hq prime_139135677007 hd
          subst q
          change (7 : ZMod 2206550475483180889)^15858984 ≠ 1
          reduce_mod_char
          decide

theorem prime_2218179173893562951 : Nat.Prime 2218179173893562951 := by
  apply lucas_primality 2218179173893562951 (11 : ZMod 2218179173893562951)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2218179173893562951 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((7 : ℕ)^1 * ((1283 : ℕ)^1 * ((4939715341039 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 2218179173893562951)^1109089586946781475 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 2218179173893562951)^443635834778712590 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (11 : ZMod 2218179173893562951)^316882739127651850 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1283 := Nat.prime_eq_prime_of_dvd_pow hq prime_1283 hd
            subst q
            change (11 : ZMod 2218179173893562951)^1728900369363650 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 4939715341039 := Nat.prime_eq_prime_of_dvd_pow hq prime_4939715341039 hd
            subst q
            change (11 : ZMod 2218179173893562951)^449050 ≠ 1
            reduce_mod_char
            decide

theorem prime_2229858897655236863 : Nat.Prime 2229858897655236863 := by
  apply lucas_primality 2229858897655236863 (5 : ZMod 2229858897655236863)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2229858897655236863 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((47 : ℕ)^1 * ((83 : ℕ)^1 * ((3221 : ℕ)^1 * ((12676012873 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2229858897655236863)^1114929448827618431 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 2229858897655236863)^318551271093605266 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (5 : ZMod 2229858897655236863)^47443806333090146 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
            subst q
            change (5 : ZMod 2229858897655236863)^26865769851267914 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 3221 := Nat.prime_eq_prime_of_dvd_pow hq prime_3221 hd
              subst q
              change (5 : ZMod 2229858897655236863)^692287767046022 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 12676012873 := Nat.prime_eq_prime_of_dvd_pow hq prime_12676012873 hd
              subst q
              change (5 : ZMod 2229858897655236863)^175911694 ≠ 1
              reduce_mod_char
              decide

theorem prime_2241589825725792277 : Nat.Prime 2241589825725792277 := by
  apply lucas_primality 2241589825725792277 (2 : ZMod 2241589825725792277)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2241589825725792277 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((9241 : ℕ)^1 * ((2887738682329 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2241589825725792277)^1120794912862896138 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2241589825725792277)^747196608575264092 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 2241589825725792277)^320227117960827468 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 9241 := Nat.prime_eq_prime_of_dvd_pow hq prime_9241 hd
            subst q
            change (2 : ZMod 2241589825725792277)^242570049315636 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2887738682329 := Nat.prime_eq_prime_of_dvd_pow hq prime_2887738682329 hd
            subst q
            change (2 : ZMod 2241589825725792277)^776244 ≠ 1
            reduce_mod_char
            decide

theorem prime_2253372137533140643 : Nat.Prime 2253372137533140643 := by
  apply lucas_primality 2253372137533140643 (5 : ZMod 2253372137533140643)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2253372137533140643 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((41729113658021123 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2253372137533140643)^1126686068766570321 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 2253372137533140643)^751124045844380214 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 41729113658021123 := Nat.prime_eq_prime_of_dvd_pow hq prime_41729113658021123 hd
        subst q
        change (5 : ZMod 2253372137533140643)^54 ≠ 1
        reduce_mod_char
        decide

theorem prime_2265206012976338591 : Nat.Prime 2265206012976338591 := by
  apply lucas_primality 2265206012976338591 (11 : ZMod 2265206012976338591)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2265206012976338591 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((226520601297633859 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 2265206012976338591)^1132603006488169295 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 2265206012976338591)^453041202595267718 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 226520601297633859 := Nat.prime_eq_prime_of_dvd_pow hq prime_226520601297633859 hd
        subst q
        change (11 : ZMod 2265206012976338591)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_2277091632426411539 : Nat.Prime 2277091632426411539 := by
  apply lucas_primality 2277091632426411539 (2 : ZMod 2277091632426411539)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2277091632426411539 - 1 = (2 : ℕ)^1 * ((29 : ℕ)^1 * ((39260200559076061 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2277091632426411539)^1138545816213205769 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (2 : ZMod 2277091632426411539)^78520401118152122 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 39260200559076061 := Nat.prime_eq_prime_of_dvd_pow hq prime_39260200559076061 hd
        subst q
        change (2 : ZMod 2277091632426411539)^58 ≠ 1
        reduce_mod_char
        decide

theorem prime_2289029176727179297 : Nat.Prime 2289029176727179297 := by
  apply lucas_primality 2289029176727179297 (5 : ZMod 2289029176727179297)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2289029176727179297 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((91297043 : ℕ)^1 * ((261170057 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2289029176727179297)^1144514588363589648 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 2289029176727179297)^763009725575726432 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 91297043 := Nat.prime_eq_prime_of_dvd_pow hq prime_91297043 hd
          subst q
          change (5 : ZMod 2289029176727179297)^25072325472 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 261170057 := Nat.prime_eq_prime_of_dvd_pow hq prime_261170057 hd
          subst q
          change (5 : ZMod 2289029176727179297)^8764516128 ≠ 1
          reduce_mod_char
          decide

theorem prime_2301018827196080653 : Nat.Prime 2301018827196080653 := by
  apply lucas_primality 2301018827196080653 (2 : ZMod 2301018827196080653)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2301018827196080653 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((13967 : ℕ)^1 * ((13728901620463 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2301018827196080653)^1150509413598040326 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2301018827196080653)^767006275732026884 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13967 := Nat.prime_eq_prime_of_dvd_pow hq prime_13967 hd
          subst q
          change (2 : ZMod 2301018827196080653)^164746819445556 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13728901620463 := Nat.prime_eq_prime_of_dvd_pow hq prime_13728901620463 hd
          subst q
          change (2 : ZMod 2301018827196080653)^167604 ≠ 1
          reduce_mod_char
          decide

theorem prime_2313060765625000051 : Nat.Prime 2313060765625000051 := by
  apply lucas_primality 2313060765625000051 (3 : ZMod 2313060765625000051)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2313060765625000051 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((11 : ℕ)^1 * ((9581753 : ℕ)^1 * ((146304649 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2313060765625000051)^1156530382812500025 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 2313060765625000051)^771020255208333350 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 2313060765625000051)^462612153125000010 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (3 : ZMod 2313060765625000051)^210278251420454550 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 9581753 := Nat.prime_eq_prime_of_dvd_pow hq prime_9581753 hd
              subst q
              change (3 : ZMod 2313060765625000051)^241402670850 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 146304649 := Nat.prime_eq_prime_of_dvd_pow hq prime_146304649 hd
              subst q
              change (3 : ZMod 2313060765625000051)^15809892450 ≠ 1
              reduce_mod_char
              decide

theorem prime_2325155174281094413 : Nat.Prime 2325155174281094413 := by
  apply lucas_primality 2325155174281094413 (2 : ZMod 2325155174281094413)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2325155174281094413 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((37 : ℕ)^1 * ((47 : ℕ)^1 * ((111422042087459 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2325155174281094413)^1162577587140547206 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2325155174281094413)^775051724760364804 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (2 : ZMod 2325155174281094413)^62842031737326876 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
            subst q
            change (2 : ZMod 2325155174281094413)^49471386686831796 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 111422042087459 := Nat.prime_eq_prime_of_dvd_pow hq prime_111422042087459 hd
            subst q
            change (2 : ZMod 2325155174281094413)^20868 ≠ 1
            reduce_mod_char
            decide

theorem prime_2337302235907620913 : Nat.Prime 2337302235907620913 := by
  apply lucas_primality 2337302235907620913 (10 : ZMod 2337302235907620913)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2337302235907620913 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((11164003 : ℕ)^1 * ((623096989 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 2337302235907620913)^1168651117953810456 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 2337302235907620913)^779100745302540304 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (10 : ZMod 2337302235907620913)^333900319415374416 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11164003 := Nat.prime_eq_prime_of_dvd_pow hq prime_11164003 hd
            subst q
            change (10 : ZMod 2337302235907620913)^209360588304 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 623096989 := Nat.prime_eq_prime_of_dvd_pow hq prime_623096989 hd
            subst q
            change (10 : ZMod 2337302235907620913)^3751105008 ≠ 1
            reduce_mod_char
            decide

theorem prime_2349502133724764939 : Nat.Prime 2349502133724764939 := by
  apply lucas_primality 2349502133724764939 (2 : ZMod 2349502133724764939)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2349502133724764939 - 1 = (2 : ℕ)^1 * ((61 : ℕ)^1 * ((149 : ℕ)^1 * ((773 : ℕ)^1 * ((167205381377 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2349502133724764939)^1174751066862382469 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
        subst q
        change (2 : ZMod 2349502133724764939)^38516428421717458 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
          subst q
          change (2 : ZMod 2349502133724764939)^15768470696139362 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 773 := Nat.prime_eq_prime_of_dvd_pow hq prime_773 hd
            subst q
            change (2 : ZMod 2349502133724764939)^3039459422671106 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 167205381377 := Nat.prime_eq_prime_of_dvd_pow hq prime_167205381377 hd
            subst q
            change (2 : ZMod 2349502133724764939)^14051594 ≠ 1
            reduce_mod_char
            decide

theorem prime_2361755051430469729 : Nat.Prime 2361755051430469729 := by
  apply lucas_primality 2361755051430469729 (13 : ZMod 2361755051430469729)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2361755051430469729 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((11 : ℕ)^2 * ((1801 : ℕ)^1 * ((112892356033 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 2361755051430469729)^1180877525715234864 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 2361755051430469729)^787251683810156576 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (13 : ZMod 2361755051430469729)^214705004675497248 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1801 := Nat.prime_eq_prime_of_dvd_pow hq prime_1801 hd
            subst q
            change (13 : ZMod 2361755051430469729)^1311357607679328 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 112892356033 := Nat.prime_eq_prime_of_dvd_pow hq prime_112892356033 hd
            subst q
            change (13 : ZMod 2361755051430469729)^20920416 ≠ 1
            reduce_mod_char
            decide

theorem prime_2374061173201265707 : Nat.Prime 2374061173201265707 := by
  apply lucas_primality 2374061173201265707 (2 : ZMod 2374061173201265707)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2374061173201265707 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((100957 : ℕ)^1 * ((79613 : ℕ)^1 * ((1823293 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2374061173201265707)^1187030586600632853 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2374061173201265707)^791353724400421902 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 100957 := Nat.prime_eq_prime_of_dvd_pow hq prime_100957 hd
          subst q
          change (2 : ZMod 2374061173201265707)^23515567748658 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 79613 := Nat.prime_eq_prime_of_dvd_pow hq prime_79613 hd
            subst q
            change (2 : ZMod 2374061173201265707)^29820019006962 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1823293 := Nat.prime_eq_prime_of_dvd_pow hq prime_1823293 hd
            subst q
            change (2 : ZMod 2374061173201265707)^1302073321842 ≠ 1
            reduce_mod_char
            decide

theorem prime_2386420683693101063 : Nat.Prime 2386420683693101063 := by
  apply lucas_primality 2386420683693101063 (5 : ZMod 2386420683693101063)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2386420683693101063 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((131 : ℕ)^1 * ((241 : ℕ)^1 * ((5399215110823 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2386420683693101063)^1193210341846550531 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 2386420683693101063)^340917240527585866 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
          subst q
          change (5 : ZMod 2386420683693101063)^18216951783916802 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 241 := Nat.prime_eq_prime_of_dvd_pow hq prime_241 hd
            subst q
            change (5 : ZMod 2386420683693101063)^9902160513249382 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 5399215110823 := Nat.prime_eq_prime_of_dvd_pow hq prime_5399215110823 hd
            subst q
            change (5 : ZMod 2386420683693101063)^441994 ≠ 1
            reduce_mod_char
            decide

theorem prime_2398833768042173467 : Nat.Prime 2398833768042173467 := by
  apply lucas_primality 2398833768042173467 (5 : ZMod 2398833768042173467)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2398833768042173467 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((107 : ℕ)^1 * ((1907 : ℕ)^1 * ((653120293013 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2398833768042173467)^1199416884021086733 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 2398833768042173467)^799611256014057822 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
          subst q
          change (5 : ZMod 2398833768042173467)^22419007177964238 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1907 := Nat.prime_eq_prime_of_dvd_pow hq prime_1907 hd
            subst q
            change (5 : ZMod 2398833768042173467)^1257909684343038 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 653120293013 := Nat.prime_eq_prime_of_dvd_pow hq prime_653120293013 hd
            subst q
            change (5 : ZMod 2398833768042173467)^3672882 ≠ 1
            reduce_mod_char
            decide

theorem prime_2411300611865761373 : Nat.Prime 2411300611865761373 := by
  apply lucas_primality 2411300611865761373 (2 : ZMod 2411300611865761373)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2411300611865761373 - 1 = (2 : ℕ)^2 * ((179 : ℕ)^1 * ((3367738284728717 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2411300611865761373)^1205650305932880686 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 179 := Nat.prime_eq_prime_of_dvd_pow hq prime_179 hd
        subst q
        change (2 : ZMod 2411300611865761373)^13470953138914868 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3367738284728717 := Nat.prime_eq_prime_of_dvd_pow hq prime_3367738284728717 hd
        subst q
        change (2 : ZMod 2411300611865761373)^716 ≠ 1
        reduce_mod_char
        decide

theorem prime_2423821401263057053 : Nat.Prime 2423821401263057053 := by
  apply lucas_primality 2423821401263057053 (2 : ZMod 2423821401263057053)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2423821401263057053 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((53 : ℕ)^1 * ((37643 : ℕ)^1 * ((109519 : ℕ)^1 * ((924421 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2423821401263057053)^1211910700631528526 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2423821401263057053)^807940467087685684 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (2 : ZMod 2423821401263057053)^45732479269114284 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 37643 := Nat.prime_eq_prime_of_dvd_pow hq prime_37643 hd
            subst q
            change (2 : ZMod 2423821401263057053)^64389697985364 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 109519 := Nat.prime_eq_prime_of_dvd_pow hq prime_109519 hd
              subst q
              change (2 : ZMod 2423821401263057053)^22131515091108 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 924421 := Nat.prime_eq_prime_of_dvd_pow hq prime_924421 hd
              subst q
              change (2 : ZMod 2423821401263057053)^2621988684012 ≠ 1
              reduce_mod_char
              decide

theorem prime_2436396322816000021 : Nat.Prime 2436396322816000021 := by
  apply lucas_primality 2436396322816000021 (6 : ZMod 2436396322816000021)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2436396322816000021 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((929 : ℕ)^1 * ((667129 : ℕ)^1 * ((9359941 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 2436396322816000021)^1218198161408000010 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 2436396322816000021)^812132107605333340 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 2436396322816000021)^487279264563200004 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (6 : ZMod 2436396322816000021)^348056617545142860 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 929 := Nat.prime_eq_prime_of_dvd_pow hq prime_929 hd
              subst q
              change (6 : ZMod 2436396322816000021)^2622600993343380 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 667129 := Nat.prime_eq_prime_of_dvd_pow hq prime_667129 hd
                subst q
                change (6 : ZMod 2436396322816000021)^3652061779380 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 9359941 := Nat.prime_eq_prime_of_dvd_pow hq prime_9359941 hd
                subst q
                change (6 : ZMod 2436396322816000021)^260300393220 ≠ 1
                reduce_mod_char
                decide

theorem prime_2449025563590110963 : Nat.Prime 2449025563590110963 := by
  apply lucas_primality 2449025563590110963 (2 : ZMod 2449025563590110963)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2449025563590110963 - 1 = (2 : ℕ)^1 * ((37 : ℕ)^1 * ((673961 : ℕ)^1 * ((49105126333 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2449025563590110963)^1224512781795055481 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (2 : ZMod 2449025563590110963)^66189880097030026 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 673961 := Nat.prime_eq_prime_of_dvd_pow hq prime_673961 hd
          subst q
          change (2 : ZMod 2449025563590110963)^3633779348642 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 49105126333 := Nat.prime_eq_prime_of_dvd_pow hq prime_49105126333 hd
          subst q
          change (2 : ZMod 2449025563590110963)^49873114 ≠ 1
          reduce_mod_char
          decide

theorem prime_2461709311135326829 : Nat.Prime 2461709311135326829 := by
  apply lucas_primality 2461709311135326829 (6 : ZMod 2461709311135326829)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2461709311135326829 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((47 : ℕ)^1 * ((2333 : ℕ)^1 * ((623622349073 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 2461709311135326829)^1230854655567663414 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 2461709311135326829)^820569770378442276 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (6 : ZMod 2461709311135326829)^52376793853943124 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2333 := Nat.prime_eq_prime_of_dvd_pow hq prime_2333 hd
            subst q
            change (6 : ZMod 2461709311135326829)^1055169014631516 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 623622349073 := Nat.prime_eq_prime_of_dvd_pow hq prime_623622349073 hd
            subst q
            change (6 : ZMod 2461709311135326829)^3947436 ≠ 1
            reduce_mod_char
            decide

theorem prime_2474447753486836021 : Nat.Prime 2474447753486836021 := by
  apply lucas_primality 2474447753486836021 (2 : ZMod 2474447753486836021)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2474447753486836021 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((3023 : ℕ)^1 * ((34871 : ℕ)^1 * ((391223099 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2474447753486836021)^1237223876743418010 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2474447753486836021)^824815917828945340 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 2474447753486836021)^494889550697367204 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3023 := Nat.prime_eq_prime_of_dvd_pow hq prime_3023 hd
            subst q
            change (2 : ZMod 2474447753486836021)^818540441113740 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 34871 := Nat.prime_eq_prime_of_dvd_pow hq prime_34871 hd
              subst q
              change (2 : ZMod 2474447753486836021)^70960045696620 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 391223099 := Nat.prime_eq_prime_of_dvd_pow hq prime_391223099 hd
              subst q
              change (2 : ZMod 2474447753486836021)^6324901980 ≠ 1
              reduce_mod_char
              decide

theorem prime_2487241079165915143 : Nat.Prime 2487241079165915143 := by
  apply lucas_primality 2487241079165915143 (5 : ZMod 2487241079165915143)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2487241079165915143 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((2267 : ℕ)^1 * ((104723 : ℕ)^1 * ((249445111 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2487241079165915143)^1243620539582957571 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 2487241079165915143)^829080359721971714 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 2487241079165915143)^355320154166559306 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2267 := Nat.prime_eq_prime_of_dvd_pow hq prime_2267 hd
            subst q
            change (5 : ZMod 2487241079165915143)^1097150895088626 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 104723 := Nat.prime_eq_prime_of_dvd_pow hq prime_104723 hd
              subst q
              change (5 : ZMod 2487241079165915143)^23750666798754 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 249445111 := Nat.prime_eq_prime_of_dvd_pow hq prime_249445111 hd
              subst q
              change (5 : ZMod 2487241079165915143)^9971095722 ≠ 1
              reduce_mod_char
              decide

theorem prime_2500089477180765647 : Nat.Prime 2500089477180765647 := by
  apply lucas_primality 2500089477180765647 (7 : ZMod 2500089477180765647)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2500089477180765647 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((2441 : ℕ)^1 * ((46554867177773 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2500089477180765647)^1250044738590382823 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (7 : ZMod 2500089477180765647)^227280861561887786 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2441 := Nat.prime_eq_prime_of_dvd_pow hq prime_2441 hd
          subst q
          change (7 : ZMod 2500089477180765647)^1024207077911006 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 46554867177773 := Nat.prime_eq_prime_of_dvd_pow hq prime_46554867177773 hd
          subst q
          change (7 : ZMod 2500089477180765647)^53702 ≠ 1
          reduce_mod_char
          decide

theorem prime_2512993137027351623 : Nat.Prime 2512993137027351623 := by
  apply lucas_primality 2512993137027351623 (7 : ZMod 2512993137027351623)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2512993137027351623 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((179499509787667973 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2512993137027351623)^1256496568513675811 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 2512993137027351623)^358999019575335946 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 179499509787667973 := Nat.prime_eq_prime_of_dvd_pow hq prime_179499509787667973 hd
        subst q
        change (7 : ZMod 2512993137027351623)^14 ≠ 1
        reduce_mod_char
        decide

theorem prime_2525952248690238413 : Nat.Prime 2525952248690238413 := by
  apply lucas_primality 2525952248690238413 (2 : ZMod 2525952248690238413)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2525952248690238413 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((50273359 : ℕ)^1 * ((67171591 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2525952248690238413)^1262976124345119206 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 2525952248690238413)^229632022608203492 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 2525952248690238413)^148585426393543436 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 50273359 := Nat.prime_eq_prime_of_dvd_pow hq prime_50273359 hd
            subst q
            change (2 : ZMod 2525952248690238413)^50244350068 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 67171591 := Nat.prime_eq_prime_of_dvd_pow hq prime_67171591 hd
            subst q
            change (2 : ZMod 2525952248690238413)^37604472532 ≠ 1
            reduce_mod_char
            decide

theorem prime_2538967002643431487 : Nat.Prime 2538967002643431487 := by
  apply lucas_primality 2538967002643431487 (3 : ZMod 2538967002643431487)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2538967002643431487 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((20150531767011361 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2538967002643431487)^1269483501321715743 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 2538967002643431487)^846322334214477162 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 2538967002643431487)^362709571806204498 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 20150531767011361 := Nat.prime_eq_prime_of_dvd_pow hq prime_20150531767011361 hd
          subst q
          change (3 : ZMod 2538967002643431487)^126 ≠ 1
          reduce_mod_char
          decide

theorem prime_2552037589851216559 : Nat.Prime 2552037589851216559 := by
  apply lucas_primality 2552037589851216559 (6 : ZMod 2552037589851216559)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2552037589851216559 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((113 : ℕ)^1 * ((347 : ℕ)^1 * ((119202813493 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 2552037589851216559)^1276018794925608279 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 2552037589851216559)^850679196617072186 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 2552037589851216559)^364576798550173794 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (6 : ZMod 2552037589851216559)^196310583834708966 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
              subst q
              change (6 : ZMod 2552037589851216559)^22584403450010766 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 347 := Nat.prime_eq_prime_of_dvd_pow hq prime_347 hd
                subst q
                change (6 : ZMod 2552037589851216559)^7354575186891114 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 119202813493 := Nat.prime_eq_prime_of_dvd_pow hq prime_119202813493 hd
                subst q
                change (6 : ZMod 2552037589851216559)^21409206 ≠ 1
                reduce_mod_char
                decide

theorem prime_2565164201769000047 : Nat.Prime 2565164201769000047 := by
  apply lucas_primality 2565164201769000047 (5 : ZMod 2565164201769000047)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2565164201769000047 - 1 = (2 : ℕ)^1 * ((661 : ℕ)^1 * ((757 : ℕ)^1 * ((2563231525199 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2565164201769000047)^1282582100884500023 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 661 := Nat.prime_eq_prime_of_dvd_pow hq prime_661 hd
        subst q
        change (5 : ZMod 2565164201769000047)^3880732529151286 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 757 := Nat.prime_eq_prime_of_dvd_pow hq prime_757 hd
          subst q
          change (5 : ZMod 2565164201769000047)^3388592076313078 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2563231525199 := Nat.prime_eq_prime_of_dvd_pow hq prime_2563231525199 hd
          subst q
          change (5 : ZMod 2565164201769000047)^1000754 ≠ 1
          reduce_mod_char
          decide

theorem prime_2578347030344150543 : Nat.Prime 2578347030344150543 := by
  apply lucas_primality 2578347030344150543 (5 : ZMod 2578347030344150543)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2578347030344150543 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^2 * ((27893 : ℕ)^1 * ((159925716523 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2578347030344150543)^1289173515172075271 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (5 : ZMod 2578347030344150543)^151667472373185326 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 27893 := Nat.prime_eq_prime_of_dvd_pow hq prime_27893 hd
          subst q
          change (5 : ZMod 2578347030344150543)^92437064150294 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 159925716523 := Nat.prime_eq_prime_of_dvd_pow hq prime_159925716523 hd
          subst q
          change (5 : ZMod 2578347030344150543)^16122154 ≠ 1
          reduce_mod_char
          decide

theorem prime_2591586268016840711 : Nat.Prime 2591586268016840711 := by
  apply lucas_primality 2591586268016840711 (11 : ZMod 2591586268016840711)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2591586268016840711 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((9433 : ℕ)^1 * ((27059 : ℕ)^1 * ((13186009 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 2591586268016840711)^1295793134008420355 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 2591586268016840711)^518317253603368142 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (11 : ZMod 2591586268016840711)^370226609716691530 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (11 : ZMod 2591586268016840711)^235598751637894610 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 9433 := Nat.prime_eq_prime_of_dvd_pow hq prime_9433 hd
              subst q
              change (11 : ZMod 2591586268016840711)^274736167498870 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 27059 := Nat.prime_eq_prime_of_dvd_pow hq prime_27059 hd
                subst q
                change (11 : ZMod 2591586268016840711)^95775389630690 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 13186009 := Nat.prime_eq_prime_of_dvd_pow hq prime_13186009 hd
                subst q
                change (11 : ZMod 2591586268016840711)^196540611190 ≠ 1
                reduce_mod_char
                decide

theorem prime_2604882107720890091 : Nat.Prime 2604882107720890091 := by
  apply lucas_primality 2604882107720890091 (6 : ZMod 2604882107720890091)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2604882107720890091 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((137593 : ℕ)^1 * ((1367101 : ℕ)^1 * ((1384813 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 2604882107720890091)^1302441053860445045 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 2604882107720890091)^520976421544178018 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 137593 := Nat.prime_eq_prime_of_dvd_pow hq prime_137593 hd
          subst q
          change (6 : ZMod 2604882107720890091)^18931792371130 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1367101 := Nat.prime_eq_prime_of_dvd_pow hq prime_1367101 hd
            subst q
            change (6 : ZMod 2604882107720890091)^1905405751090 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1384813 := Nat.prime_eq_prime_of_dvd_pow hq prime_1384813 hd
            subst q
            change (6 : ZMod 2604882107720890091)^1881035278930 ≠ 1
            reduce_mod_char
            decide

theorem prime_2618234742884608579 : Nat.Prime 2618234742884608579 := by
  apply lucas_primality 2618234742884608579 (2 : ZMod 2618234742884608579)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2618234742884608579 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((68281403 : ℕ)^1 * ((6390795121 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2618234742884608579)^1309117371442304289 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2618234742884608579)^872744914294869526 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 68281403 := Nat.prime_eq_prime_of_dvd_pow hq prime_68281403 hd
          subst q
          change (2 : ZMod 2618234742884608579)^38344770726 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 6390795121 := Nat.prime_eq_prime_of_dvd_pow hq prime_6390795121 hd
          subst q
          change (2 : ZMod 2618234742884608579)^409688418 ≠ 1
          reduce_mod_char
          decide

theorem prime_2631644367431640643 : Nat.Prime 2631644367431640643 := by
  apply lucas_primality 2631644367431640643 (2 : ZMod 2631644367431640643)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2631644367431640643 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5237 : ℕ)^1 * ((27917216890837 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2631644367431640643)^1315822183715820321 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2631644367431640643)^877214789143880214 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5237 := Nat.prime_eq_prime_of_dvd_pow hq prime_5237 hd
          subst q
          change (2 : ZMod 2631644367431640643)^502509904035066 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 27917216890837 := Nat.prime_eq_prime_of_dvd_pow hq prime_27917216890837 hd
          subst q
          change (2 : ZMod 2631644367431640643)^94266 ≠ 1
          reduce_mod_char
          decide

theorem prime_2645111175781810249 : Nat.Prime 2645111175781810249 := by
  apply lucas_primality 2645111175781810249 (7 : ZMod 2645111175781810249)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2645111175781810249 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((73 : ℕ)^1 * ((113 : ℕ)^1 * ((4453588946441 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2645111175781810249)^1322555587890905124 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 2645111175781810249)^881703725260603416 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
          subst q
          change (7 : ZMod 2645111175781810249)^36234399668243976 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
            subst q
            change (7 : ZMod 2645111175781810249)^23408063502493896 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 4453588946441 := Nat.prime_eq_prime_of_dvd_pow hq prime_4453588946441 hd
            subst q
            change (7 : ZMod 2645111175781810249)^593928 ≠ 1
            reduce_mod_char
            decide

theorem prime_2658635362851966343 : Nat.Prime 2658635362851966343 := by
  apply lucas_primality 2658635362851966343 (5 : ZMod 2658635362851966343)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2658635362851966343 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((13 : ℕ)^1 * ((9173 : ℕ)^1 * ((1238601284731 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2658635362851966343)^1329317681425983171 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 2658635362851966343)^886211787617322114 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (5 : ZMod 2658635362851966343)^204510412527074334 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 9173 := Nat.prime_eq_prime_of_dvd_pow hq prime_9173 hd
            subst q
            change (5 : ZMod 2658635362851966343)^289832700627054 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1238601284731 := Nat.prime_eq_prime_of_dvd_pow hq prime_1238601284731 hd
            subst q
            change (5 : ZMod 2658635362851966343)^2146482 ≠ 1
            reduce_mod_char
            decide

theorem prime_2672217124056829549 : Nat.Prime 2672217124056829549 := by
  apply lucas_primality 2672217124056829549 (2 : ZMod 2672217124056829549)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2672217124056829549 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((190833787 : ℕ)^1 * ((388968089 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2672217124056829549)^1336108562028414774 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2672217124056829549)^890739041352276516 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 190833787 := Nat.prime_eq_prime_of_dvd_pow hq prime_190833787 hd
          subst q
          change (2 : ZMod 2672217124056829549)^14002851204 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 388968089 := Nat.prime_eq_prime_of_dvd_pow hq prime_388968089 hd
          subst q
          change (2 : ZMod 2672217124056829549)^6870016332 ≠ 1
          reduce_mod_char
          decide

theorem prime_2685856655309838931 : Nat.Prime 2685856655309838931 := by
  apply lucas_primality 2685856655309838931 (2 : ZMod 2685856655309838931)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2685856655309838931 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((2685077 : ℕ)^1 * ((653784553 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2685856655309838931)^1342928327654919465 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2685856655309838931)^895285551769946310 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 2685856655309838931)^537171331061967786 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (2 : ZMod 2685856655309838931)^157991567959402290 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 2685077 := Nat.prime_eq_prime_of_dvd_pow hq prime_2685077 hd
              subst q
              change (2 : ZMod 2685856655309838931)^1000290366090 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 653784553 := Nat.prime_eq_prime_of_dvd_pow hq prime_653784553 hd
              subst q
              change (2 : ZMod 2685856655309838931)^4108167810 ≠ 1
              reduce_mod_char
              decide

theorem prime_2699554153024000009 : Nat.Prime 2699554153024000009 := by
  apply lucas_primality 2699554153024000009 (7 : ZMod 2699554153024000009)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2699554153024000009 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((17 : ℕ)^2 * ((73 : ℕ)^1 * ((279553 : ℕ)^1 * ((577939 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2699554153024000009)^1349777076512000004 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 2699554153024000009)^899851384341333336 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (7 : ZMod 2699554153024000009)^245414013911272728 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (7 : ZMod 2699554153024000009)^158797303119058824 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
              subst q
              change (7 : ZMod 2699554153024000009)^36980193877041096 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 279553 := Nat.prime_eq_prime_of_dvd_pow hq prime_279553 hd
                subst q
                change (7 : ZMod 2699554153024000009)^9656681033736 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 577939 := Nat.prime_eq_prime_of_dvd_pow hq prime_577939 hd
                subst q
                change (7 : ZMod 2699554153024000009)^4671001875672 ≠ 1
                reduce_mod_char
                decide

theorem prime_2713309814112733123 : Nat.Prime 2713309814112733123 := by
  apply lucas_primality 2713309814112733123 (2 : ZMod 2713309814112733123)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2713309814112733123 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((71 : ℕ)^1 * ((909895980587771 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2713309814112733123)^1356654907056366561 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2713309814112733123)^904436604704244374 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 2713309814112733123)^387615687730390446 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
            subst q
            change (2 : ZMod 2713309814112733123)^38215631184686382 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 909895980587771 := Nat.prime_eq_prime_of_dvd_pow hq prime_909895980587771 hd
            subst q
            change (2 : ZMod 2713309814112733123)^2982 ≠ 1
            reduce_mod_char
            decide

theorem prime_2727123835990722629 : Nat.Prime 2727123835990722629 := by
  apply lucas_primality 2727123835990722629 (2 : ZMod 2727123835990722629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2727123835990722629 - 1 = (2 : ℕ)^2 * ((29 : ℕ)^1 * ((997 : ℕ)^1 * ((23580429529889 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2727123835990722629)^1363561917995361314 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (2 : ZMod 2727123835990722629)^94038752965197332 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 997 := Nat.prime_eq_prime_of_dvd_pow hq prime_997 hd
          subst q
          change (2 : ZMod 2727123835990722629)^2735329825467124 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 23580429529889 := Nat.prime_eq_prime_of_dvd_pow hq prime_23580429529889 hd
          subst q
          change (2 : ZMod 2727123835990722629)^115652 ≠ 1
          reduce_mod_char
          decide

theorem prime_2740996416574767227 : Nat.Prime 2740996416574767227 := by
  apply lucas_primality 2740996416574767227 (2 : ZMod 2740996416574767227)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2740996416574767227 - 1 = (2 : ℕ)^1 * ((1091077159 : ℕ)^1 * ((1256096507 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2740996416574767227)^1370498208287383613 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1091077159 := Nat.prime_eq_prime_of_dvd_pow hq prime_1091077159 hd
        subst q
        change (2 : ZMod 2740996416574767227)^2512193014 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1256096507 := Nat.prime_eq_prime_of_dvd_pow hq prime_1256096507 hd
        subst q
        change (2 : ZMod 2740996416574767227)^2182154318 ≠ 1
        reduce_mod_char
        decide

theorem prime_2754927754284630031 : Nat.Prime 2754927754284630031 := by
  apply lucas_primality 2754927754284630031 (3 : ZMod 2754927754284630031)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2754927754284630031 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((23 : ℕ)^1 * ((3992648919253087 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2754927754284630031)^1377463877142315015 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 2754927754284630031)^918309251428210010 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 2754927754284630031)^550985550856926006 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (3 : ZMod 2754927754284630031)^119779467577592610 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3992648919253087 := Nat.prime_eq_prime_of_dvd_pow hq prime_3992648919253087 hd
            subst q
            change (3 : ZMod 2754927754284630031)^690 ≠ 1
            reduce_mod_char
            decide

theorem prime_2768918048043890627 : Nat.Prime 2768918048043890627 := by
  apply lucas_primality 2768918048043890627 (2 : ZMod 2768918048043890627)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2768918048043890627 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((702113 : ℕ)^1 * ((151680495877 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2768918048043890627)^1384459024021945313 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 2768918048043890627)^212993696003376202 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 702113 := Nat.prime_eq_prime_of_dvd_pow hq prime_702113 hd
          subst q
          change (2 : ZMod 2768918048043890627)^3943692892802 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 151680495877 := Nat.prime_eq_prime_of_dvd_pow hq prime_151680495877 hd
          subst q
          change (2 : ZMod 2768918048043890627)^18254938 ≠ 1
          reduce_mod_char
          decide

theorem prime_2782967497280796739 : Nat.Prime 2782967497280796739 := by
  apply lucas_primality 2782967497280796739 (2 : ZMod 2782967497280796739)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2782967497280796739 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((43 : ℕ)^1 * ((980608702354051 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2782967497280796739)^1391483748640398369 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2782967497280796739)^927655832426932246 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 2782967497280796739)^252997045207345158 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (2 : ZMod 2782967497280796739)^64720174355367366 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 980608702354051 := Nat.prime_eq_prime_of_dvd_pow hq prime_980608702354051 hd
            subst q
            change (2 : ZMod 2782967497280796739)^2838 ≠ 1
            reduce_mod_char
            decide

theorem prime_2797076301929117287 : Nat.Prime 2797076301929117287 := by
  apply lucas_primality 2797076301929117287 (3 : ZMod 2797076301929117287)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2797076301929117287 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((35859952588834837 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2797076301929117287)^1398538150964558643 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 2797076301929117287)^932358767309705762 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 2797076301929117287)^215159715533009022 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 35859952588834837 := Nat.prime_eq_prime_of_dvd_pow hq prime_35859952588834837 hd
          subst q
          change (3 : ZMod 2797076301929117287)^78 ≠ 1
          reduce_mod_char
          decide

theorem prime_2811244662428995589 : Nat.Prime 2811244662428995589 := by
  apply lucas_primality 2811244662428995589 (3 : ZMod 2811244662428995589)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2811244662428995589 - 1 = (2 : ℕ)^2 * ((17 : ℕ)^1 * ((41341833271014641 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2811244662428995589)^1405622331214497794 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (3 : ZMod 2811244662428995589)^165367333084058564 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 41341833271014641 := Nat.prime_eq_prime_of_dvd_pow hq prime_41341833271014641 hd
        subst q
        change (3 : ZMod 2811244662428995589)^68 ≠ 1
        reduce_mod_char
        decide

theorem prime_2825472779727804389 : Nat.Prime 2825472779727804389 := by
  apply lucas_primality 2825472779727804389 (3 : ZMod 2825472779727804389)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2825472779727804389 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((31 : ℕ)^1 * ((709 : ℕ)^1 * ((877 : ℕ)^1 * ((1999 : ℕ)^1 * ((201451 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2825472779727804389)^1412736389863902194 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 2825472779727804389)^403638968532543484 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 2825472779727804389)^217344059979061876 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (3 : ZMod 2825472779727804389)^91144283217025948 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 709 := Nat.prime_eq_prime_of_dvd_pow hq prime_709 hd
              subst q
              change (3 : ZMod 2825472779727804389)^3985152016541332 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 877 := Nat.prime_eq_prime_of_dvd_pow hq prime_877 hd
                subst q
                change (3 : ZMod 2825472779727804389)^3221747753395444 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 1999 := Nat.prime_eq_prime_of_dvd_pow hq prime_1999 hd
                  subst q
                  change (3 : ZMod 2825472779727804389)^1413443111419612 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 201451 := Nat.prime_eq_prime_of_dvd_pow hq prime_201451 hd
                  subst q
                  change (3 : ZMod 2825472779727804389)^14025608111788 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_2839760855281000019 : Nat.Prime 2839760855281000019 := by
  apply lucas_primality 2839760855281000019 (2 : ZMod 2839760855281000019)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2839760855281000019 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((7617353 : ℕ)^1 * ((9810566587 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2839760855281000019)^1419880427640500009 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 2839760855281000019)^149461097646368422 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7617353 := Nat.prime_eq_prime_of_dvd_pow hq prime_7617353 hd
          subst q
          change (2 : ZMod 2839760855281000019)^372801530306 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 9810566587 := Nat.prime_eq_prime_of_dvd_pow hq prime_9810566587 hd
          subst q
          change (2 : ZMod 2839760855281000019)^289459414 ≠ 1
          reduce_mod_char
          decide

theorem prime_2854109091052978643 : Nat.Prime 2854109091052978643 := by
  apply lucas_primality 2854109091052978643 (2 : ZMod 2854109091052978643)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2854109091052978643 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((61 : ℕ)^1 * ((89 : ℕ)^1 * ((109 : ℕ)^1 * ((613 : ℕ)^1 * ((302614969 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2854109091052978643)^1427054545526489321 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 2854109091052978643)^219546853157921434 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (2 : ZMod 2854109091052978643)^46788673623819322 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
            subst q
            change (2 : ZMod 2854109091052978643)^32068641472505378 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
              subst q
              change (2 : ZMod 2854109091052978643)^26184487073880538 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 613 := Nat.prime_eq_prime_of_dvd_pow hq prime_613 hd
                subst q
                change (2 : ZMod 2854109091052978643)^4655969153430634 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 302614969 := Nat.prime_eq_prime_of_dvd_pow hq prime_302614969 hd
                subst q
                change (2 : ZMod 2854109091052978643)^9431486818 ≠ 1
                reduce_mod_char
                decide

theorem prime_2868517689517932587 : Nat.Prime 2868517689517932587 := by
  apply lucas_primality 2868517689517932587 (2 : ZMod 2868517689517932587)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2868517689517932587 - 1 = (2 : ℕ)^1 * ((831055721 : ℕ)^1 * ((1725827533 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2868517689517932587)^1434258844758966293 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 831055721 := Nat.prime_eq_prime_of_dvd_pow hq prime_831055721 hd
        subst q
        change (2 : ZMod 2868517689517932587)^3451655066 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1725827533 := Nat.prime_eq_prime_of_dvd_pow hq prime_1725827533 hd
        subst q
        change (2 : ZMod 2868517689517932587)^1662111442 ≠ 1
        reduce_mod_char
        decide

theorem prime_2882986853660707369 : Nat.Prime 2882986853660707369 := by
  apply lucas_primality 2882986853660707369 (23 : ZMod 2882986853660707369)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2882986853660707369 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((127 : ℕ)^1 * ((631 : ℕ)^1 * ((1498988634911 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (23 : ZMod 2882986853660707369)^1441493426830353684 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (23 : ZMod 2882986853660707369)^960995617886902456 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
          subst q
          change (23 : ZMod 2882986853660707369)^22700683887092184 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 631 := Nat.prime_eq_prime_of_dvd_pow hq prime_631 hd
            subst q
            change (23 : ZMod 2882986853660707369)^4568917359208728 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1498988634911 := Nat.prime_eq_prime_of_dvd_pow hq prime_1498988634911 hd
            subst q
            change (23 : ZMod 2882986853660707369)^1923288 ≠ 1
            reduce_mod_char
            decide

theorem prime_2897516786977659481 : Nat.Prime 2897516786977659481 := by
  apply lucas_primality 2897516786977659481 (7 : ZMod 2897516786977659481)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2897516786977659481 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((1036039 : ℕ)^1 * ((23306046611 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2897516786977659481)^1448758393488829740 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 2897516786977659481)^965838928992553160 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 2897516786977659481)^579503357395531896 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1036039 := Nat.prime_eq_prime_of_dvd_pow hq prime_1036039 hd
            subst q
            change (7 : ZMod 2897516786977659481)^2796725593320 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 23306046611 := Nat.prime_eq_prime_of_dvd_pow hq prime_23306046611 hd
            subst q
            change (7 : ZMod 2897516786977659481)^124324680 ≠ 1
            reduce_mod_char
            decide

theorem prime_2912107693477515629 : Nat.Prime 2912107693477515629 := by
  apply lucas_primality 2912107693477515629 (2 : ZMod 2912107693477515629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2912107693477515629 - 1 = (2 : ℕ)^2 * ((1597 : ℕ)^1 * ((14391649 : ℕ)^1 * ((31676119 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2912107693477515629)^1456053846738757814 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1597 := Nat.prime_eq_prime_of_dvd_pow hq prime_1597 hd
        subst q
        change (2 : ZMod 2912107693477515629)^1823486345320924 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 14391649 := Nat.prime_eq_prime_of_dvd_pow hq prime_14391649 hd
          subst q
          change (2 : ZMod 2912107693477515629)^202347048172 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 31676119 := Nat.prime_eq_prime_of_dvd_pow hq prime_31676119 hd
          subst q
          change (2 : ZMod 2912107693477515629)^91933853812 ≠ 1
          reduce_mod_char
          decide

theorem prime_2926759777682231299 : Nat.Prime 2926759777682231299 := by
  apply lucas_primality 2926759777682231299 (2 : ZMod 2926759777682231299)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2926759777682231299 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((130211 : ℕ)^1 * ((143249 : ℕ)^1 * ((26151497 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2926759777682231299)^1463379888841115649 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2926759777682231299)^975586592560743766 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 130211 := Nat.prime_eq_prime_of_dvd_pow hq prime_130211 hd
          subst q
          change (2 : ZMod 2926759777682231299)^22477054762518 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 143249 := Nat.prime_eq_prime_of_dvd_pow hq prime_143249 hd
            subst q
            change (2 : ZMod 2926759777682231299)^20431275455202 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 26151497 := Nat.prime_eq_prime_of_dvd_pow hq prime_26151497 hd
            subst q
            change (2 : ZMod 2926759777682231299)^111915573234 ≠ 1
            reduce_mod_char
            decide

theorem prime_2941473244627851191 : Nat.Prime 2941473244627851191 := by
  apply lucas_primality 2941473244627851191 (11 : ZMod 2941473244627851191)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2941473244627851191 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((6991 : ℕ)^1 * ((42075142964209 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 2941473244627851191)^1470736622313925595 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 2941473244627851191)^588294648925570238 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 6991 := Nat.prime_eq_prime_of_dvd_pow hq prime_6991 hd
          subst q
          change (11 : ZMod 2941473244627851191)^420751429642090 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 42075142964209 := Nat.prime_eq_prime_of_dvd_pow hq prime_42075142964209 hd
          subst q
          change (11 : ZMod 2941473244627851191)^69910 ≠ 1
          reduce_mod_char
          decide

theorem prime_2956248299865369721 : Nat.Prime 2956248299865369721 := by
  apply lucas_primality 2956248299865369721 (29 : ZMod 2956248299865369721)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2956248299865369721 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((19 : ℕ)^1 * ((941 : ℕ)^1 * ((1377895995239 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (29 : ZMod 2956248299865369721)^1478124149932684860 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (29 : ZMod 2956248299865369721)^985416099955123240 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (29 : ZMod 2956248299865369721)^591249659973073944 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (29 : ZMod 2956248299865369721)^155592015782387880 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 941 := Nat.prime_eq_prime_of_dvd_pow hq prime_941 hd
              subst q
              change (29 : ZMod 2956248299865369721)^3141602869144920 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1377895995239 := Nat.prime_eq_prime_of_dvd_pow hq prime_1377895995239 hd
              subst q
              change (29 : ZMod 2956248299865369721)^2145480 ≠ 1
              reduce_mod_char
              decide

theorem prime_2971085149461592829 : Nat.Prime 2971085149461592829 := by
  apply lucas_primality 2971085149461592829 (2 : ZMod 2971085149461592829)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2971085149461592829 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((43 : ℕ)^1 * ((33349 : ℕ)^1 * ((51343 : ℕ)^1 * ((1441201 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2971085149461592829)^1485542574730796414 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 2971085149461592829)^424440735637370404 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (2 : ZMod 2971085149461592829)^69095003475850996 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 33349 := Nat.prime_eq_prime_of_dvd_pow hq prime_33349 hd
            subst q
            change (2 : ZMod 2971085149461592829)^89090681863372 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 51343 := Nat.prime_eq_prime_of_dvd_pow hq prime_51343 hd
              subst q
              change (2 : ZMod 2971085149461592829)^57867385027396 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1441201 := Nat.prime_eq_prime_of_dvd_pow hq prime_1441201 hd
              subst q
              change (2 : ZMod 2971085149461592829)^2061534199228 ≠ 1
              reduce_mod_char
              decide

theorem prime_2985984000000000007 : Nat.Prime 2985984000000000007 := by
  apply lucas_primality 2985984000000000007 (6 : ZMod 2985984000000000007)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2985984000000000007 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((135794977 : ℕ)^1 * ((523545559 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 2985984000000000007)^1492992000000000003 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 2985984000000000007)^995328000000000002 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 2985984000000000007)^426569142857142858 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 135794977 := Nat.prime_eq_prime_of_dvd_pow hq prime_135794977 hd
            subst q
            change (6 : ZMod 2985984000000000007)^21988913478 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 523545559 := Nat.prime_eq_prime_of_dvd_pow hq prime_523545559 hd
            subst q
            change (6 : ZMod 2985984000000000007)^5703389034 ≠ 1
            reduce_mod_char
            decide

theorem prime_3000945058581607237 : Nat.Prime 3000945058581607237 := by
  apply lucas_primality 3000945058581607237 (5 : ZMod 3000945058581607237)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3000945058581607237 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((11 : ℕ)^1 * ((313 : ℕ)^1 * ((8070440987569 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3000945058581607237)^1500472529290803618 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 3000945058581607237)^1000315019527202412 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 3000945058581607237)^272813187143782476 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 313 := Nat.prime_eq_prime_of_dvd_pow hq prime_313 hd
            subst q
            change (5 : ZMod 3000945058581607237)^9587683893231972 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 8070440987569 := Nat.prime_eq_prime_of_dvd_pow hq prime_8070440987569 hd
            subst q
            change (5 : ZMod 3000945058581607237)^371844 ≠ 1
            reduce_mod_char
            decide

theorem prime_3015968532825830509 : Nat.Prime 3015968532825830509 := by
  apply lucas_primality 3015968532825830509 (13 : ZMod 3015968532825830509)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3015968532825830509 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((3833 : ℕ)^1 * ((874109 : ℕ)^1 * ((25004599 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 3015968532825830509)^1507984266412915254 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 3015968532825830509)^1005322844275276836 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 3833 := Nat.prime_eq_prime_of_dvd_pow hq prime_3833 hd
          subst q
          change (13 : ZMod 3015968532825830509)^786842820982476 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 874109 := Nat.prime_eq_prime_of_dvd_pow hq prime_874109 hd
            subst q
            change (13 : ZMod 3015968532825830509)^3450334606812 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 25004599 := Nat.prime_eq_prime_of_dvd_pow hq prime_25004599 hd
            subst q
            change (13 : ZMod 3015968532825830509)^120616552692 ≠ 1
            reduce_mod_char
            decide

theorem prime_3031054630871350331 : Nat.Prime 3031054630871350331 := by
  apply lucas_primality 3031054630871350331 (2 : ZMod 3031054630871350331)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3031054630871350331 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((17 : ℕ)^1 * ((277 : ℕ)^1 * ((8513 : ℕ)^1 * ((581619673 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3031054630871350331)^1515527315435675165 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 3031054630871350331)^606210926174270066 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 3031054630871350331)^233158048528565410 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (2 : ZMod 3031054630871350331)^178297331227726490 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 277 := Nat.prime_eq_prime_of_dvd_pow hq prime_277 hd
              subst q
              change (2 : ZMod 3031054630871350331)^10942435490510290 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 8513 := Nat.prime_eq_prime_of_dvd_pow hq prime_8513 hd
                subst q
                change (2 : ZMod 3031054630871350331)^356050115220410 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 581619673 := Nat.prime_eq_prime_of_dvd_pow hq prime_581619673 hd
                subst q
                change (2 : ZMod 3031054630871350331)^5211403210 ≠ 1
                reduce_mod_char
                decide

theorem prime_3046203561376976911 : Nat.Prime 3046203561376976911 := by
  apply lucas_primality 3046203561376976911 (3 : ZMod 3046203561376976911)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3046203561376976911 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((131 : ℕ)^1 * ((8517751758457 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3046203561376976911)^1523101780688488455 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3046203561376976911)^1015401187125658970 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 3046203561376976911)^609240712275395382 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (3 : ZMod 3046203561376976911)^435171937339568130 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
              subst q
              change (3 : ZMod 3046203561376976911)^234323350875152070 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
                subst q
                change (3 : ZMod 3046203561376976911)^23253462300587610 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 8517751758457 := Nat.prime_eq_prime_of_dvd_pow hq prime_8517751758457 hd
                subst q
                change (3 : ZMod 3046203561376976911)^357630 ≠ 1
                reduce_mod_char
                decide

theorem prime_3061415533522515649 : Nat.Prime 3061415533522515649 := by
  apply lucas_primality 3061415533522515649 (11 : ZMod 3061415533522515649)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3061415533522515649 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^1 * ((863 : ℕ)^1 * ((37117 : ℕ)^1 * ((497779939 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 3061415533522515649)^1530707766761257824 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 3061415533522515649)^1020471844507505216 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 863 := Nat.prime_eq_prime_of_dvd_pow hq prime_863 hd
          subst q
          change (11 : ZMod 3061415533522515649)^3547410815205696 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 37117 := Nat.prime_eq_prime_of_dvd_pow hq prime_37117 hd
            subst q
            change (11 : ZMod 3061415533522515649)^82480144772544 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 497779939 := Nat.prime_eq_prime_of_dvd_pow hq prime_497779939 hd
            subst q
            change (11 : ZMod 3061415533522515649)^6150138432 ≠ 1
            reduce_mod_char
            decide

theorem prime_3076690757009633891 : Nat.Prime 3076690757009633891 := by
  apply lucas_primality 3076690757009633891 (6 : ZMod 3076690757009633891)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3076690757009633891 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((317 : ℕ)^1 * ((443 : ℕ)^1 * ((3082771 : ℕ)^1 * ((101527 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 3076690757009633891)^1538345378504816945 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 3076690757009633891)^615338151401926778 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 3076690757009633891)^439527251001376270 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 317 := Nat.prime_eq_prime_of_dvd_pow hq prime_317 hd
            subst q
            change (6 : ZMod 3076690757009633891)^9705649075740170 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 443 := Nat.prime_eq_prime_of_dvd_pow hq prime_443 hd
              subst q
              change (6 : ZMod 3076690757009633891)^6945125862324230 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 3082771 := Nat.prime_eq_prime_of_dvd_pow hq prime_3082771 hd
                subst q
                change (6 : ZMod 3076690757009633891)^998027669590 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 101527 := Nat.prime_eq_prime_of_dvd_pow hq prime_101527 hd
                subst q
                change (6 : ZMod 3076690757009633891)^30304163001070 ≠ 1
                reduce_mod_char
                decide

theorem prime_3092029442062728077 : Nat.Prime 3092029442062728077 := by
  apply lucas_primality 3092029442062728077 (2 : ZMod 3092029442062728077)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3092029442062728077 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((13 : ℕ)^2 * ((19 : ℕ)^1 * ((79 : ℕ)^1 * ((139 : ℕ)^1 * ((8599 : ℕ)^1 * ((364213 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3092029442062728077)^1546014721031364038 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 3092029442062728077)^441718491723246868 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 3092029442062728077)^237848418620209852 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (2 : ZMod 3092029442062728077)^162738391687512004 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
              subst q
              change (2 : ZMod 3092029442062728077)^39139613190667444 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
                subst q
                change (2 : ZMod 3092029442062728077)^22244816129947684 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 8599 := Nat.prime_eq_prime_of_dvd_pow hq prime_8599 hd
                  subst q
                  change (2 : ZMod 3092029442062728077)^359580118858324 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 364213 := Nat.prime_eq_prime_of_dvd_pow hq prime_364213 hd
                  subst q
                  change (2 : ZMod 3092029442062728077)^8489618553052 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_3107431799429791753 : Nat.Prime 3107431799429791753 := by
  apply lucas_primality 3107431799429791753 (7 : ZMod 3107431799429791753)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3107431799429791753 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((107 : ℕ)^1 * ((2273 : ℕ)^1 * ((177454041931 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 3107431799429791753)^1553715899714895876 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 3107431799429791753)^1035810599809930584 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
          subst q
          change (7 : ZMod 3107431799429791753)^29041418686259736 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2273 := Nat.prime_eq_prime_of_dvd_pow hq prime_2273 hd
            subst q
            change (7 : ZMod 3107431799429791753)^1367105939036424 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 177454041931 := Nat.prime_eq_prime_of_dvd_pow hq prime_177454041931 hd
            subst q
            change (7 : ZMod 3107431799429791753)^17511192 ≠ 1
            reduce_mod_char
            decide

theorem prime_3122898040383284263 : Nat.Prime 3122898040383284263 := by
  apply lucas_primality 3122898040383284263 (5 : ZMod 3122898040383284263)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3122898040383284263 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((3011 : ℕ)^1 * ((924387773761 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3122898040383284263)^1561449020191642131 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 3122898040383284263)^1040966013461094754 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 3122898040383284263)^283899821853025842 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (5 : ZMod 3122898040383284263)^183699884728428486 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 3011 := Nat.prime_eq_prime_of_dvd_pow hq prime_3011 hd
              subst q
              change (5 : ZMod 3122898040383284263)^1037163082159842 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 924387773761 := Nat.prime_eq_prime_of_dvd_pow hq prime_924387773761 hd
              subst q
              change (5 : ZMod 3122898040383284263)^3378342 ≠ 1
              reduce_mod_char
              decide

theorem prime_3138428376721000079 : Nat.Prime 3138428376721000079 := by
  apply lucas_primality 3138428376721000079 (13 : ZMod 3138428376721000079)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3138428376721000079 - 1 = (2 : ℕ)^1 * ((74989597 : ℕ)^1 * ((20925758387 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 3138428376721000079)^1569214188360500039 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 74989597 := Nat.prime_eq_prime_of_dvd_pow hq prime_74989597 hd
        subst q
        change (13 : ZMod 3138428376721000079)^41851516774 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 20925758387 := Nat.prime_eq_prime_of_dvd_pow hq prime_20925758387 hd
        subst q
        change (13 : ZMod 3138428376721000079)^149979194 ≠ 1
        reduce_mod_char
        decide

theorem prime_3154023020766938767 : Nat.Prime 3154023020766938767 := by
  apply lucas_primality 3154023020766938767 (3 : ZMod 3154023020766938767)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3154023020766938767 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((89 : ℕ)^1 * ((22560001 : ℕ)^1 * ((261808949 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3154023020766938767)^1577011510383469383 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3154023020766938767)^1051341006922312922 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (3 : ZMod 3154023020766938767)^35438460907493694 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 22560001 := Nat.prime_eq_prime_of_dvd_pow hq prime_22560001 hd
            subst q
            change (3 : ZMod 3154023020766938767)^139805978766 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 261808949 := Nat.prime_eq_prime_of_dvd_pow hq prime_261808949 hd
            subst q
            change (3 : ZMod 3154023020766938767)^12047040534 ≠ 1
            reduce_mod_char
            decide

theorem prime_3169682185372176413 : Nat.Prime 3169682185372176413 := by
  apply lucas_primality 3169682185372176413 (2 : ZMod 3169682185372176413)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3169682185372176413 - 1 = (2 : ℕ)^2 * ((2130013 : ℕ)^1 * ((372026154931 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3169682185372176413)^1584841092686088206 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 2130013 := Nat.prime_eq_prime_of_dvd_pow hq prime_2130013 hd
        subst q
        change (2 : ZMod 3169682185372176413)^1488104619724 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 372026154931 := Nat.prime_eq_prime_of_dvd_pow hq prime_372026154931 hd
        subst q
        change (2 : ZMod 3169682185372176413)^8520052 ≠ 1
        reduce_mod_char
        decide

theorem prime_3185406083915736463 : Nat.Prime 3185406083915736463 := by
  apply lucas_primality 3185406083915736463 (5 : ZMod 3185406083915736463)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3185406083915736463 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((281 : ℕ)^1 * ((390373 : ℕ)^1 * ((1613266843 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3185406083915736463)^1592703041957868231 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 3185406083915736463)^1061802027971912154 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 281 := Nat.prime_eq_prime_of_dvd_pow hq prime_281 hd
          subst q
          change (5 : ZMod 3185406083915736463)^11335964711443902 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 390373 := Nat.prime_eq_prime_of_dvd_pow hq prime_390373 hd
            subst q
            change (5 : ZMod 3185406083915736463)^8159903691894 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1613266843 := Nat.prime_eq_prime_of_dvd_pow hq prime_1613266843 hd
            subst q
            change (5 : ZMod 3185406083915736463)^1974506634 ≠ 1
            reduce_mod_char
            decide

theorem prime_3201194930305462379 : Nat.Prime 3201194930305462379 := by
  apply lucas_primality 3201194930305462379 (2 : ZMod 3201194930305462379)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3201194930305462379 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((94152792067807717 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3201194930305462379)^1600597465152731189 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 3201194930305462379)^188305584135615434 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 94152792067807717 := Nat.prime_eq_prime_of_dvd_pow hq prime_94152792067807717 hd
        subst q
        change (2 : ZMod 3201194930305462379)^34 ≠ 1
        reduce_mod_char
        decide

theorem prime_3217048938978890671 : Nat.Prime 3217048938978890671 := by
  apply lucas_primality 3217048938978890671 (3 : ZMod 3217048938978890671)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3217048938978890671 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((7683409 : ℕ)^1 * ((4652230307 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3217048938978890671)^1608524469489445335 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3217048938978890671)^1072349646326296890 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 3217048938978890671)^643409787795778134 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7683409 := Nat.prime_eq_prime_of_dvd_pow hq prime_7683409 hd
            subst q
            change (3 : ZMod 3217048938978890671)^418700727630 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 4652230307 := Nat.prime_eq_prime_of_dvd_pow hq prime_4652230307 hd
            subst q
            change (3 : ZMod 3217048938978890671)^691506810 ≠ 1
            reduce_mod_char
            decide

theorem prime_3232968324904124419 : Nat.Prime 3232968324904124419 := by
  apply lucas_primality 3232968324904124419 (2 : ZMod 3232968324904124419)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3232968324904124419 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((353 : ℕ)^1 * ((156619 : ℕ)^1 * ((9746104129 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3232968324904124419)^1616484162452062209 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3232968324904124419)^1077656108301374806 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 353 := Nat.prime_eq_prime_of_dvd_pow hq prime_353 hd
          subst q
          change (2 : ZMod 3232968324904124419)^9158550495479106 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 156619 := Nat.prime_eq_prime_of_dvd_pow hq prime_156619 hd
            subst q
            change (2 : ZMod 3232968324904124419)^20642248545222 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 9746104129 := Nat.prime_eq_prime_of_dvd_pow hq prime_9746104129 hd
            subst q
            change (2 : ZMod 3232968324904124419)^331719042 ≠ 1
            reduce_mod_char
            decide

theorem prime_3248953303580707973 : Nat.Prime 3248953303580707973 := by
  apply lucas_primality 3248953303580707973 (2 : ZMod 3248953303580707973)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3248953303580707973 - 1 = (2 : ℕ)^2 * ((61 : ℕ)^1 * ((13315382391724213 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3248953303580707973)^1624476651790353986 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
        subst q
        change (2 : ZMod 3248953303580707973)^53261529566896852 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13315382391724213 := Nat.prime_eq_prime_of_dvd_pow hq prime_13315382391724213 hd
        subst q
        change (2 : ZMod 3248953303580707973)^244 ≠ 1
        reduce_mod_char
        decide

theorem prime_3265004091040501861 : Nat.Prime 3265004091040501861 := by
  apply lucas_primality 3265004091040501861 (6 : ZMod 3265004091040501861)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3265004091040501861 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((18138911616891677 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 3265004091040501861)^1632502045520250930 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 3265004091040501861)^1088334697013500620 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 3265004091040501861)^653000818208100372 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 18138911616891677 := Nat.prime_eq_prime_of_dvd_pow hq prime_18138911616891677 hd
          subst q
          change (6 : ZMod 3265004091040501861)^180 ≠ 1
          reduce_mod_char
          decide

theorem prime_3281120903848558703 : Nat.Prime 3281120903848558703 := by
  apply lucas_primality 3281120903848558703 (5 : ZMod 3281120903848558703)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3281120903848558703 - 1 = (2 : ℕ)^1 * ((797957 : ℕ)^1 * ((2055950949643 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3281120903848558703)^1640560451924279351 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 797957 := Nat.prime_eq_prime_of_dvd_pow hq prime_797957 hd
        subst q
        change (5 : ZMod 3281120903848558703)^4111901899286 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2055950949643 := Nat.prime_eq_prime_of_dvd_pow hq prime_2055950949643 hd
        subst q
        change (5 : ZMod 3281120903848558703)^1595914 ≠ 1
        reduce_mod_char
        decide

theorem prime_3297303959104000099 : Nat.Prime 3297303959104000099 := by
  apply lucas_primality 3297303959104000099 (3 : ZMod 3297303959104000099)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3297303959104000099 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((37993 : ℕ)^1 * ((438318908707 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3297303959104000099)^1648651979552000049 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3297303959104000099)^1099101319701333366 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 3297303959104000099)^299754905373090918 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 37993 := Nat.prime_eq_prime_of_dvd_pow hq prime_37993 hd
            subst q
            change (3 : ZMod 3297303959104000099)^86787143923986 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 438318908707 := Nat.prime_eq_prime_of_dvd_pow hq prime_438318908707 hd
            subst q
            change (3 : ZMod 3297303959104000099)^7522614 ≠ 1
            reduce_mod_char
            decide

theorem prime_3313553474440893331 : Nat.Prime 3313553474440893331 := by
  apply lucas_primality 3313553474440893331 (2 : ZMod 3313553474440893331)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3313553474440893331 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((3181 : ℕ)^1 * ((150617 : ℕ)^1 * ((76844681 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3313553474440893331)^1656776737220446665 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3313553474440893331)^1104517824813631110 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 3313553474440893331)^662710694888178666 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3181 := Nat.prime_eq_prime_of_dvd_pow hq prime_3181 hd
            subst q
            change (2 : ZMod 3313553474440893331)^1041670378635930 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 150617 := Nat.prime_eq_prime_of_dvd_pow hq prime_150617 hd
              subst q
              change (2 : ZMod 3313553474440893331)^21999863723490 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 76844681 := Nat.prime_eq_prime_of_dvd_pow hq prime_76844681 hd
              subst q
              change (2 : ZMod 3313553474440893331)^43120140930 ≠ 1
              reduce_mod_char
              decide

theorem prime_3329869668029130307 : Nat.Prime 3329869668029130307 := by
  apply lucas_primality 3329869668029130307 (2 : ZMod 3329869668029130307)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3329869668029130307 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((43 : ℕ)^1 * ((12906471581508257 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3329869668029130307)^1664934834014565153 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3329869668029130307)^1109956556009710102 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (2 : ZMod 3329869668029130307)^77438829489049542 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 12906471581508257 := Nat.prime_eq_prime_of_dvd_pow hq prime_12906471581508257 hd
          subst q
          change (2 : ZMod 3329869668029130307)^258 ≠ 1
          reduce_mod_char
          decide

theorem prime_3346252758575305609 : Nat.Prime 3346252758575305609 := by
  apply lucas_primality 3346252758575305609 (22 : ZMod 3346252758575305609)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3346252758575305609 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((67 : ℕ)^1 * ((150329 : ℕ)^1 * ((13842990769 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (22 : ZMod 3346252758575305609)^1673126379287652804 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (22 : ZMod 3346252758575305609)^1115417586191768536 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
          subst q
          change (22 : ZMod 3346252758575305609)^49944071023512024 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 150329 := Nat.prime_eq_prime_of_dvd_pow hq prime_150329 hd
            subst q
            change (22 : ZMod 3346252758575305609)^22259529156552 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 13842990769 := Nat.prime_eq_prime_of_dvd_pow hq prime_13842990769 hd
            subst q
            change (22 : ZMod 3346252758575305609)^241729032 ≠ 1
            reduce_mod_char
            decide

theorem prime_3362702965323595783 : Nat.Prime 3362702965323595783 := by
  apply lucas_primality 3362702965323595783 (13 : ZMod 3362702965323595783)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3362702965323595783 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((631 : ℕ)^1 * ((60727 : ℕ)^1 * ((2089430983 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 3362702965323595783)^1681351482661797891 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 3362702965323595783)^1120900988441198594 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (13 : ZMod 3362702965323595783)^480386137903370826 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 631 := Nat.prime_eq_prime_of_dvd_pow hq prime_631 hd
            subst q
            change (13 : ZMod 3362702965323595783)^5329164762794922 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 60727 := Nat.prime_eq_prime_of_dvd_pow hq prime_60727 hd
              subst q
              change (13 : ZMod 3362702965323595783)^55374099911466 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 2089430983 := Nat.prime_eq_prime_of_dvd_pow hq prime_2089430983 hd
              subst q
              change (13 : ZMod 3362702965323595783)^1609386954 ≠ 1
              reduce_mod_char
              decide

theorem prime_3379220508056640631 : Nat.Prime 3379220508056640631 := by
  apply lucas_primality 3379220508056640631 (3 : ZMod 3379220508056640631)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3379220508056640631 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((40339441 : ℕ)^1 * ((2792321381 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3379220508056640631)^1689610254028320315 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3379220508056640631)^1126406836018880210 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 3379220508056640631)^675844101611328126 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 40339441 := Nat.prime_eq_prime_of_dvd_pow hq prime_40339441 hd
            subst q
            change (3 : ZMod 3379220508056640631)^83769641430 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2792321381 := Nat.prime_eq_prime_of_dvd_pow hq prime_2792321381 hd
            subst q
            change (3 : ZMod 3379220508056640631)^1210183230 ≠ 1
            reduce_mod_char
            decide

theorem prime_3395805607096423153 : Nat.Prime 3395805607096423153 := by
  apply lucas_primality 3395805607096423153 (5 : ZMod 3395805607096423153)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3395805607096423153 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((6449 : ℕ)^1 * ((10970065149301 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3395805607096423153)^1697902803548211576 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 3395805607096423153)^1131935202365474384 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 6449 := Nat.prime_eq_prime_of_dvd_pow hq prime_6449 hd
          subst q
          change (5 : ZMod 3395805607096423153)^526563127166448 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 10970065149301 := Nat.prime_eq_prime_of_dvd_pow hq prime_10970065149301 hd
          subst q
          change (5 : ZMod 3395805607096423153)^309552 ≠ 1
          reduce_mod_char
          decide

theorem prime_3412458483305150933 : Nat.Prime 3412458483305150933 := by
  apply lucas_primality 3412458483305150933 (2 : ZMod 3412458483305150933)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3412458483305150933 - 1 = (2 : ℕ)^2 * ((67 : ℕ)^1 * ((2633 : ℕ)^1 * ((79817 : ℕ)^1 * ((60587959 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3412458483305150933)^1706229241652575466 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
        subst q
        change (2 : ZMod 3412458483305150933)^50932216168733596 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2633 := Nat.prime_eq_prime_of_dvd_pow hq prime_2633 hd
          subst q
          change (2 : ZMod 3412458483305150933)^1296034365098804 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 79817 := Nat.prime_eq_prime_of_dvd_pow hq prime_79817 hd
            subst q
            change (2 : ZMod 3412458483305150933)^42753529740596 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 60587959 := Nat.prime_eq_prime_of_dvd_pow hq prime_60587959 hd
            subst q
            change (2 : ZMod 3412458483305150933)^56322387148 ≠ 1
            reduce_mod_char
            decide

theorem prime_3429179358086139907 : Nat.Prime 3429179358086139907 := by
  apply lucas_primality 3429179358086139907 (2 : ZMod 3429179358086139907)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3429179358086139907 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((571529893014356651 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3429179358086139907)^1714589679043069953 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3429179358086139907)^1143059786028713302 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 571529893014356651 := Nat.prime_eq_prime_of_dvd_pow hq prime_571529893014356651 hd
        subst q
        change (2 : ZMod 3429179358086139907)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_3445968453384696131 : Nat.Prime 3445968453384696131 := by
  apply lucas_primality 3445968453384696131 (2 : ZMod 3445968453384696131)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3445968453384696131 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((1249 : ℕ)^1 * ((72053 : ℕ)^1 * ((3829100729 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3445968453384696131)^1722984226692348065 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 3445968453384696131)^689193690676939226 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1249 := Nat.prime_eq_prime_of_dvd_pow hq prime_1249 hd
          subst q
          change (2 : ZMod 3445968453384696131)^2758981948266370 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 72053 := Nat.prime_eq_prime_of_dvd_pow hq prime_72053 hd
            subst q
            change (2 : ZMod 3445968453384696131)^47825468105210 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3829100729 := Nat.prime_eq_prime_of_dvd_pow hq prime_3829100729 hd
            subst q
            change (2 : ZMod 3445968453384696131)^899941970 ≠ 1
            reduce_mod_char
            decide

theorem prime_3462825991689000073 : Nat.Prime 3462825991689000073 := by
  apply lucas_primality 3462825991689000073 (5 : ZMod 3462825991689000073)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3462825991689000073 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((953 : ℕ)^1 * ((50466742329617 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3462825991689000073)^1731412995844500036 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 3462825991689000073)^1154275330563000024 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 953 := Nat.prime_eq_prime_of_dvd_pow hq prime_953 hd
          subst q
          change (5 : ZMod 3462825991689000073)^3633605447732424 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 50466742329617 := Nat.prime_eq_prime_of_dvd_pow hq prime_50466742329617 hd
          subst q
          change (5 : ZMod 3462825991689000073)^68616 ≠ 1
          reduce_mod_char
          decide

theorem prime_3479752196030990897 : Nat.Prime 3479752196030990897 := by
  apply lucas_primality 3479752196030990897 (3 : ZMod 3479752196030990897)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3479752196030990897 - 1 = (2 : ℕ)^4 * ((79 : ℕ)^1 * ((5199049 : ℕ)^1 * ((529513861 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3479752196030990897)^1739876098015495448 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
        subst q
        change (3 : ZMod 3479752196030990897)^44047496152291024 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5199049 := Nat.prime_eq_prime_of_dvd_pow hq prime_5199049 hd
          subst q
          change (3 : ZMod 3479752196030990897)^669305520304 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 529513861 := Nat.prime_eq_prime_of_dvd_pow hq prime_529513861 hd
          subst q
          change (3 : ZMod 3479752196030990897)^6571597936 ≠ 1
          reduce_mod_char
          decide

theorem prime_3496747289987252227 : Nat.Prime 3496747289987252227 := by
  apply lucas_primality 3496747289987252227 (2 : ZMod 3496747289987252227)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3496747289987252227 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((6977 : ℕ)^1 * ((995377 : ℕ)^1 * ((83918299 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3496747289987252227)^1748373644993626113 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3496747289987252227)^1165582429995750742 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 6977 := Nat.prime_eq_prime_of_dvd_pow hq prime_6977 hd
          subst q
          change (2 : ZMod 3496747289987252227)^501182068222338 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 995377 := Nat.prime_eq_prime_of_dvd_pow hq prime_995377 hd
            subst q
            change (2 : ZMod 3496747289987252227)^3512987832738 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 83918299 := Nat.prime_eq_prime_of_dvd_pow hq prime_83918299 hd
            subst q
            change (2 : ZMod 3496747289987252227)^41668471974 ≠ 1
            reduce_mod_char
            decide

theorem prime_3513811497679897597 : Nat.Prime 3513811497679897597 := by
  apply lucas_primality 3513811497679897597 (6 : ZMod 3513811497679897597)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3513811497679897597 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((31 : ℕ)^1 * ((37 : ℕ)^1 * ((1051 : ℕ)^1 * ((2341 : ℕ)^1 * ((126691 : ℕ)^1)))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 3513811497679897597)^1756905748839948798 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 3513811497679897597)^1171270499226632532 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 3513811497679897597)^501973071097128228 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (6 : ZMod 3513811497679897597)^270293192129222892 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
              subst q
              change (6 : ZMod 3513811497679897597)^113348757989674116 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
                subst q
                change (6 : ZMod 3513811497679897597)^94967878315672908 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 1051 := Nat.prime_eq_prime_of_dvd_pow hq prime_1051 hd
                  subst q
                  change (6 : ZMod 3513811497679897597)^3343303042511796 ≠ 1
                  reduce_mod_char
                  decide
                · rcases hq.dvd_mul.mp hd with hd | hd
                  · have heq : q = 2341 := Nat.prime_eq_prime_of_dvd_pow hq prime_2341 hd
                    subst q
                    change (6 : ZMod 3513811497679897597)^1500987397556556 ≠ 1
                    reduce_mod_char
                    decide
                  · have heq : q = 126691 := Nat.prime_eq_prime_of_dvd_pow hq prime_126691 hd
                    subst q
                    change (6 : ZMod 3513811497679897597)^27735288991956 ≠ 1
                    reduce_mod_char
                    decide

theorem prime_3530945043777457289 : Nat.Prime 3530945043777457289 := by
  apply lucas_primality 3530945043777457289 (3 : ZMod 3530945043777457289)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3530945043777457289 - 1 = (2 : ℕ)^3 * ((499 : ℕ)^1 * ((74713 : ℕ)^1 * ((11838706403 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3530945043777457289)^1765472521888728644 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 499 := Nat.prime_eq_prime_of_dvd_pow hq prime_499 hd
        subst q
        change (3 : ZMod 3530945043777457289)^7076042171898712 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 74713 := Nat.prime_eq_prime_of_dvd_pow hq prime_74713 hd
          subst q
          change (3 : ZMod 3530945043777457289)^47260115960776 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11838706403 := Nat.prime_eq_prime_of_dvd_pow hq prime_11838706403 hd
          subst q
          change (3 : ZMod 3530945043777457289)^298254296 ≠ 1
          reduce_mod_char
          decide

theorem prime_3548148153495765637 : Nat.Prime 3548148153495765637 := by
  apply lucas_primality 3548148153495765637 (2 : ZMod 3548148153495765637)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3548148153495765637 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((4871 : ℕ)^1 * ((7568531 : ℕ)^1 * ((8020303 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3548148153495765637)^1774074076747882818 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3548148153495765637)^1182716051165255212 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 4871 := Nat.prime_eq_prime_of_dvd_pow hq prime_4871 hd
          subst q
          change (2 : ZMod 3548148153495765637)^728422942618716 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7568531 := Nat.prime_eq_prime_of_dvd_pow hq prime_7568531 hd
            subst q
            change (2 : ZMod 3548148153495765637)^468802750956 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 8020303 := Nat.prime_eq_prime_of_dvd_pow hq prime_8020303 hd
            subst q
            change (2 : ZMod 3548148153495765637)^442395774012 ≠ 1
            reduce_mod_char
            decide

theorem prime_3565421052598849567 : Nat.Prime 3565421052598849567 := by
  apply lucas_primality 3565421052598849567 (5 : ZMod 3565421052598849567)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3565421052598849567 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((130829 : ℕ)^1 * ((4542088085209 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3565421052598849567)^1782710526299424783 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 3565421052598849567)^1188473684199616522 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 130829 := Nat.prime_eq_prime_of_dvd_pow hq prime_130829 hd
          subst q
          change (5 : ZMod 3565421052598849567)^27252528511254 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4542088085209 := Nat.prime_eq_prime_of_dvd_pow hq prime_4542088085209 hd
          subst q
          change (5 : ZMod 3565421052598849567)^784974 ≠ 1
          reduce_mod_char
          decide

theorem prime_3582763967399816887 : Nat.Prime 3582763967399816887 := by
  apply lucas_primality 3582763967399816887 (5 : ZMod 3582763967399816887)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3582763967399816887 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((31 : ℕ)^1 * ((19262171867740951 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3582763967399816887)^1791381983699908443 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 3582763967399816887)^1194254655799938962 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (5 : ZMod 3582763967399816887)^115573031206445706 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 19262171867740951 := Nat.prime_eq_prime_of_dvd_pow hq prime_19262171867740951 hd
          subst q
          change (5 : ZMod 3582763967399816887)^186 ≠ 1
          reduce_mod_char
          decide

theorem prime_3600177124761745993 : Nat.Prime 3600177124761745993 := by
  apply lucas_primality 3600177124761745993 (5 : ZMod 3600177124761745993)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3600177124761745993 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^3 * ((163 : ℕ)^1 * ((85147 : ℕ)^1 * ((1200917467 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3600177124761745993)^1800088562380872996 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 3600177124761745993)^1200059041587248664 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
          subst q
          change (5 : ZMod 3600177124761745993)^22086976225532184 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 85147 := Nat.prime_eq_prime_of_dvd_pow hq prime_85147 hd
            subst q
            change (5 : ZMod 3600177124761745993)^42281902178136 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1200917467 := Nat.prime_eq_prime_of_dvd_pow hq prime_1200917467 hd
            subst q
            change (5 : ZMod 3600177124761745993)^2997855576 ≠ 1
            reduce_mod_char
            decide

theorem prime_3617660752098576583 : Nat.Prime 3617660752098576583 := by
  apply lucas_primality 3617660752098576583 (3 : ZMod 3617660752098576583)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3617660752098576583 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((17 : ℕ)^1 * ((2557 : ℕ)^1 * ((1981521999859 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3617660752098576583)^1808830376049288291 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3617660752098576583)^1205886917366192194 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 3617660752098576583)^516808678871225226 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (3 : ZMod 3617660752098576583)^212803573652857446 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 2557 := Nat.prime_eq_prime_of_dvd_pow hq prime_2557 hd
              subst q
              change (3 : ZMod 3617660752098576583)^1414806707899326 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1981521999859 := Nat.prime_eq_prime_of_dvd_pow hq prime_1981521999859 hd
              subst q
              change (3 : ZMod 3617660752098576583)^1825698 ≠ 1
              reduce_mod_char
              decide

theorem prime_3635215077376000009 : Nat.Prime 3635215077376000009 := by
  apply lucas_primality 3635215077376000009 (13 : ZMod 3635215077376000009)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3635215077376000009 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((23297 : ℕ)^1 * ((1472467 : ℕ)^1 * ((133801 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 3635215077376000009)^1817607538688000004 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 3635215077376000009)^1211738359125333336 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (13 : ZMod 3635215077376000009)^330474097943272728 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23297 := Nat.prime_eq_prime_of_dvd_pow hq prime_23297 hd
            subst q
            change (13 : ZMod 3635215077376000009)^156037905197064 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1472467 := Nat.prime_eq_prime_of_dvd_pow hq prime_1472467 hd
              subst q
              change (13 : ZMod 3635215077376000009)^2468792222424 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 133801 := Nat.prime_eq_prime_of_dvd_pow hq prime_133801 hd
              subst q
              change (13 : ZMod 3635215077376000009)^27168818449608 ≠ 1
              reduce_mod_char
              decide

theorem prime_3652840329112351453 : Nat.Prime 3652840329112351453 := by
  apply lucas_primality 3652840329112351453 (2 : ZMod 3652840329112351453)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3652840329112351453 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((161879 : ℕ)^1 * ((1880437615499 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3652840329112351453)^1826420164556175726 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3652840329112351453)^1217613443037450484 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 161879 := Nat.prime_eq_prime_of_dvd_pow hq prime_161879 hd
          subst q
          change (2 : ZMod 3652840329112351453)^22565251385988 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1880437615499 := Nat.prime_eq_prime_of_dvd_pow hq prime_1880437615499 hd
          subst q
          change (2 : ZMod 3652840329112351453)^1942548 ≠ 1
          reduce_mod_char
          decide

theorem prime_3670536736379502191 : Nat.Prime 3670536736379502191 := by
  apply lucas_primality 3670536736379502191 (11 : ZMod 3670536736379502191)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3670536736379502191 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((23 : ℕ)^1 * ((41 : ℕ)^1 * ((389240375013733 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 3670536736379502191)^1835268368189751095 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 3670536736379502191)^734107347275900438 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (11 : ZMod 3670536736379502191)^159588553755630530 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (11 : ZMod 3670536736379502191)^89525286253158590 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 389240375013733 := Nat.prime_eq_prime_of_dvd_pow hq prime_389240375013733 hd
            subst q
            change (11 : ZMod 3670536736379502191)^9430 ≠ 1
            reduce_mod_char
            decide

theorem prime_3688304528803752677 : Nat.Prime 3688304528803752677 := by
  apply lucas_primality 3688304528803752677 (2 : ZMod 3688304528803752677)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3688304528803752677 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((109 : ℕ)^1 * ((1093 : ℕ)^1 * ((386263 : ℕ)^1 * ((220189 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3688304528803752677)^1844152264401876338 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 3688304528803752677)^526900646971964668 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 3688304528803752677)^283715732984904052 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
            subst q
            change (2 : ZMod 3688304528803752677)^33837656227557364 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1093 := Nat.prime_eq_prime_of_dvd_pow hq prime_1093 hd
              subst q
              change (2 : ZMod 3688304528803752677)^3374478068438932 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 386263 := Nat.prime_eq_prime_of_dvd_pow hq prime_386263 hd
                subst q
                change (2 : ZMod 3688304528803752677)^9548687109052 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 220189 := Nat.prime_eq_prime_of_dvd_pow hq prime_220189 hd
                subst q
                change (2 : ZMod 3688304528803752677)^16750630271284 ≠ 1
                reduce_mod_char
                decide

theorem prime_3706143936566726713 : Nat.Prime 3706143936566726713 := by
  apply lucas_primality 3706143936566726713 (5 : ZMod 3706143936566726713)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3706143936566726713 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((116953 : ℕ)^1 * ((1320382239221 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3706143936566726713)^1853071968283363356 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 3706143936566726713)^1235381312188908904 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 116953 := Nat.prime_eq_prime_of_dvd_pow hq prime_116953 hd
          subst q
          change (5 : ZMod 3706143936566726713)^31689173741304 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1320382239221 := Nat.prime_eq_prime_of_dvd_pow hq prime_1320382239221 hd
          subst q
          change (5 : ZMod 3706143936566726713)^2806872 ≠ 1
          reduce_mod_char
          decide

theorem prime_3724055190406265629 : Nat.Prime 3724055190406265629 := by
  apply lucas_primality 3724055190406265629 (7 : ZMod 3724055190406265629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3724055190406265629 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((6247 : ℕ)^1 * ((49677914604427 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 3724055190406265629)^1862027595203132814 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 3724055190406265629)^1241351730135421876 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 6247 := Nat.prime_eq_prime_of_dvd_pow hq prime_6247 hd
          subst q
          change (7 : ZMod 3724055190406265629)^596134975253124 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 49677914604427 := Nat.prime_eq_prime_of_dvd_pow hq prime_49677914604427 hd
          subst q
          change (7 : ZMod 3724055190406265629)^74964 ≠ 1
          reduce_mod_char
          decide

theorem prime_3742038521617324099 : Nat.Prime 3742038521617324099 := by
  apply lucas_primality 3742038521617324099 (2 : ZMod 3742038521617324099)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3742038521617324099 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1175951729 : ℕ)^1 * ((530356027 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3742038521617324099)^1871019260808662049 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3742038521617324099)^1247346173872441366 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1175951729 := Nat.prime_eq_prime_of_dvd_pow hq prime_1175951729 hd
          subst q
          change (2 : ZMod 3742038521617324099)^3182136162 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 530356027 := Nat.prime_eq_prime_of_dvd_pow hq prime_530356027 hd
          subst q
          change (2 : ZMod 3742038521617324099)^7055710374 ≠ 1
          reduce_mod_char
          decide

theorem prime_3760094162052865771 : Nat.Prime 3760094162052865771 := by
  apply lucas_primality 3760094162052865771 (2 : ZMod 3760094162052865771)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3760094162052865771 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((813613 : ℕ)^1 * ((22007035649 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3760094162052865771)^1880047081026432885 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3760094162052865771)^1253364720684288590 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 3760094162052865771)^752018832410573154 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (2 : ZMod 3760094162052865771)^537156308864695110 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 813613 := Nat.prime_eq_prime_of_dvd_pow hq prime_813613 hd
              subst q
              change (2 : ZMod 3760094162052865771)^4621477486290 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 22007035649 := Nat.prime_eq_prime_of_dvd_pow hq prime_22007035649 hd
              subst q
              change (2 : ZMod 3760094162052865771)^170858730 ≠ 1
              reduce_mod_char
              decide

theorem prime_3778222344124760093 : Nat.Prime 3778222344124760093 := by
  apply lucas_primality 3778222344124760093 (2 : ZMod 3778222344124760093)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3778222344124760093 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^2 * ((29 : ℕ)^1 * ((151 : ℕ)^1 * ((1782654604397 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3778222344124760093)^1889111172062380046 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 3778222344124760093)^343474758556796372 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (2 : ZMod 3778222344124760093)^130283529107750348 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
            subst q
            change (2 : ZMod 3778222344124760093)^25021340027316292 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1782654604397 := Nat.prime_eq_prime_of_dvd_pow hq prime_1782654604397 hd
            subst q
            change (2 : ZMod 3778222344124760093)^2119436 ≠ 1
            reduce_mod_char
            decide

theorem prime_3796423300804680059 : Nat.Prime 3796423300804680059 := by
  apply lucas_primality 3796423300804680059 (2 : ZMod 3796423300804680059)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3796423300804680059 - 1 = (2 : ℕ)^1 * ((4835179 : ℕ)^1 * ((392583532151 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3796423300804680059)^1898211650402340029 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 4835179 := Nat.prime_eq_prime_of_dvd_pow hq prime_4835179 hd
        subst q
        change (2 : ZMod 3796423300804680059)^785167064302 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 392583532151 := Nat.prime_eq_prime_of_dvd_pow hq prime_392583532151 hd
        subst q
        change (2 : ZMod 3796423300804680059)^9670358 ≠ 1
        reduce_mod_char
        decide

theorem prime_3814697265625000031 : Nat.Prime 3814697265625000031 := by
  apply lucas_primality 3814697265625000031 (7 : ZMod 3814697265625000031)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3814697265625000031 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((22439395680147059 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 3814697265625000031)^1907348632812500015 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 3814697265625000031)^762939453125000006 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (7 : ZMod 3814697265625000031)^224393956801470590 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 22439395680147059 := Nat.prime_eq_prime_of_dvd_pow hq prime_22439395680147059 hd
          subst q
          change (7 : ZMod 3814697265625000031)^170 ≠ 1
          reduce_mod_char
          decide

theorem prime_3833044472679695027 : Nat.Prime 3833044472679695027 := by
  apply lucas_primality 3833044472679695027 (2 : ZMod 3833044472679695027)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3833044472679695027 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((17 : ℕ)^1 * ((8672046318279853 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3833044472679695027)^1916522236339847513 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 3833044472679695027)^294849574821515002 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 3833044472679695027)^225473204275276178 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 8672046318279853 := Nat.prime_eq_prime_of_dvd_pow hq prime_8672046318279853 hd
          subst q
          change (2 : ZMod 3833044472679695027)^442 ≠ 1
          reduce_mod_char
          decide

theorem prime_3851465156625240149 : Nat.Prime 3851465156625240149 := by
  apply lucas_primality 3851465156625240149 (2 : ZMod 3851465156625240149)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3851465156625240149 - 1 = (2 : ℕ)^2 * ((651697 : ℕ)^1 * ((1477475405221 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3851465156625240149)^1925732578312620074 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 651697 := Nat.prime_eq_prime_of_dvd_pow hq prime_651697 hd
        subst q
        change (2 : ZMod 3851465156625240149)^5909901620884 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1477475405221 := Nat.prime_eq_prime_of_dvd_pow hq prime_1477475405221 hd
        subst q
        change (2 : ZMod 3851465156625240149)^2606788 ≠ 1
        reduce_mod_char
        decide

theorem prime_3869959552681510777 : Nat.Prime 3869959552681510777 := by
  apply lucas_primality 3869959552681510777 (7 : ZMod 3869959552681510777)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3869959552681510777 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((97 : ℕ)^1 * ((1662353759742917 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 3869959552681510777)^1934979776340755388 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 3869959552681510777)^1289986517560503592 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
          subst q
          change (7 : ZMod 3869959552681510777)^39896490233830008 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1662353759742917 := Nat.prime_eq_prime_of_dvd_pow hq prime_1662353759742917 hd
          subst q
          change (7 : ZMod 3869959552681510777)^2328 ≠ 1
          reduce_mod_char
          decide

theorem prime_3888527896632684121 : Nat.Prime 3888527896632684121 := by
  apply lucas_primality 3888527896632684121 (17 : ZMod 3888527896632684121)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3888527896632684121 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((73 : ℕ)^1 * ((103 : ℕ)^1 * ((227 : ℕ)^1 * ((18985324777 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 3888527896632684121)^1944263948316342060 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 3888527896632684121)^1296175965544228040 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (17 : ZMod 3888527896632684121)^777705579326536824 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
            subst q
            change (17 : ZMod 3888527896632684121)^53267505433324440 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
              subst q
              change (17 : ZMod 3888527896632684121)^37752698025560040 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 227 := Nat.prime_eq_prime_of_dvd_pow hq prime_227 hd
                subst q
                change (17 : ZMod 3888527896632684121)^17130078839791560 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 18985324777 := Nat.prime_eq_prime_of_dvd_pow hq prime_18985324777 hd
                subst q
                change (17 : ZMod 3888527896632684121)^204817560 ≠ 1
                reduce_mod_char
                decide

theorem prime_3907170424828140697 : Nat.Prime 3907170424828140697 := by
  apply lucas_primality 3907170424828140697 (5 : ZMod 3907170424828140697)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3907170424828140697 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((79 : ℕ)^1 * ((6619 : ℕ)^1 * ((103779216143 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3907170424828140697)^1953585212414070348 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 3907170424828140697)^1302390141609380232 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (5 : ZMod 3907170424828140697)^49457853478837224 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 6619 := Nat.prime_eq_prime_of_dvd_pow hq prime_6619 hd
            subst q
            change (5 : ZMod 3907170424828140697)^590296181421384 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 103779216143 := Nat.prime_eq_prime_of_dvd_pow hq prime_103779216143 hd
            subst q
            change (5 : ZMod 3907170424828140697)^37648872 ≠ 1
            reduce_mod_char
            decide

theorem prime_3925887374183366701 : Nat.Prime 3925887374183366701 := by
  apply lucas_primality 3925887374183366701 (2 : ZMod 3925887374183366701)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3925887374183366701 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^2 * ((47 : ℕ)^1 * ((92810576221829 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3925887374183366701)^1962943687091683350 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3925887374183366701)^1308629124727788900 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 3925887374183366701)^785177474836673340 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
            subst q
            change (2 : ZMod 3925887374183366701)^83529518599646100 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 92810576221829 := Nat.prime_eq_prime_of_dvd_pow hq prime_92810576221829 hd
            subst q
            change (2 : ZMod 3925887374183366701)^42300 ≠ 1
            reduce_mod_char
            decide

theorem prime_3944678982180857653 : Nat.Prime 3944678982180857653 := by
  apply lucas_primality 3944678982180857653 (5 : ZMod 3944678982180857653)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3944678982180857653 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((328723248515071471 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3944678982180857653)^1972339491090428826 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 3944678982180857653)^1314892994060285884 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 328723248515071471 := Nat.prime_eq_prime_of_dvd_pow hq prime_328723248515071471 hd
        subst q
        change (5 : ZMod 3944678982180857653)^12 ≠ 1
        reduce_mod_char
        decide

theorem prime_3963545486871022231 : Nat.Prime 3963545486871022231 := by
  apply lucas_primality 3963545486871022231 (3 : ZMod 3963545486871022231)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3963545486871022231 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((5851 : ℕ)^1 * ((22580444863391 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3963545486871022231)^1981772743435511115 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3963545486871022231)^1321181828957007410 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 3963545486871022231)^792709097374204446 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 5851 := Nat.prime_eq_prime_of_dvd_pow hq prime_5851 hd
            subst q
            change (3 : ZMod 3963545486871022231)^677413345901730 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 22580444863391 := Nat.prime_eq_prime_of_dvd_pow hq prime_22580444863391 hd
            subst q
            change (3 : ZMod 3963545486871022231)^175530 ≠ 1
            reduce_mod_char
            decide

theorem prime_3982487126873086493 : Nat.Prime 3982487126873086493 := by
  apply lucas_primality 3982487126873086493 (2 : ZMod 3982487126873086493)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3982487126873086493 - 1 = (2 : ℕ)^2 * ((173 : ℕ)^1 * ((5858731 : ℕ)^1 * ((982301321 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3982487126873086493)^1991243563436543246 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
        subst q
        change (2 : ZMod 3982487126873086493)^23020156802734604 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5858731 := Nat.prime_eq_prime_of_dvd_pow hq prime_5858731 hd
          subst q
          change (2 : ZMod 3982487126873086493)^679752514132 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 982301321 := Nat.prime_eq_prime_of_dvd_pow hq prime_982301321 hd
          subst q
          change (2 : ZMod 3982487126873086493)^4054241852 ≠ 1
          reduce_mod_char
          decide

end LegendreK6.Pratt
