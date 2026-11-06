import LegendreK6.Pratt.Block024

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LegendreK6.Pratt

theorem prime_575398903529078873 : Nat.Prime 575398903529078873 := by
  apply lucas_primality 575398903529078873 (3 : ZMod 575398903529078873)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 575398903529078873 - 1 = (2 : ℕ)^3 * ((1087 : ℕ)^1 * ((66168227176757 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 575398903529078873)^287699451764539436 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1087 := Nat.prime_eq_prime_of_dvd_pow hq prime_1087 hd
        subst q
        change (3 : ZMod 575398903529078873)^529345817414056 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 66168227176757 := Nat.prime_eq_prime_of_dvd_pow hq prime_66168227176757 hd
        subst q
        change (3 : ZMod 575398903529078873)^8696 ≠ 1
        reduce_mod_char
        decide

theorem prime_579194814785959013 : Nat.Prime 579194814785959013 := by
  apply lucas_primality 579194814785959013 (2 : ZMod 579194814785959013)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 579194814785959013 - 1 = (2 : ℕ)^2 * ((1143091 : ℕ)^1 * ((126672945283 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 579194814785959013)^289597407392979506 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1143091 := Nat.prime_eq_prime_of_dvd_pow hq prime_1143091 hd
        subst q
        change (2 : ZMod 579194814785959013)^506691781132 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 126672945283 := Nat.prime_eq_prime_of_dvd_pow hq prime_126672945283 hd
        subst q
        change (2 : ZMod 579194814785959013)^4572364 ≠ 1
        reduce_mod_char
        decide

theorem prime_583011571186179169 : Nat.Prime 583011571186179169 := by
  apply lucas_primality 583011571186179169 (13 : ZMod 583011571186179169)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 583011571186179169 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((953 : ℕ)^1 * ((242129 : ℕ)^1 * ((2392619 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 583011571186179169)^291505785593089584 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 583011571186179169)^194337190395393056 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (13 : ZMod 583011571186179169)^53001051926016288 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 953 := Nat.prime_eq_prime_of_dvd_pow hq prime_953 hd
            subst q
            change (13 : ZMod 583011571186179169)^611764502818656 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 242129 := Nat.prime_eq_prime_of_dvd_pow hq prime_242129 hd
              subst q
              change (13 : ZMod 583011571186179169)^2407855197792 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 2392619 := Nat.prime_eq_prime_of_dvd_pow hq prime_2392619 hd
              subst q
              change (13 : ZMod 583011571186179169)^243670877472 ≠ 1
              reduce_mod_char
              decide

theorem prime_586849264205765653 : Nat.Prime 586849264205765653 := by
  apply lucas_primality 586849264205765653 (2 : ZMod 586849264205765653)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 586849264205765653 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((9967 : ℕ)^1 * ((21397 : ℕ)^1 * ((279991 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 586849264205765653)^293424632102882826 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 586849264205765653)^195616421401921884 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 586849264205765653)^83835609172252236 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (2 : ZMod 586849264205765653)^45142251092751204 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 9967 := Nat.prime_eq_prime_of_dvd_pow hq prime_9967 hd
              subst q
              change (2 : ZMod 586849264205765653)^58879227872556 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 21397 := Nat.prime_eq_prime_of_dvd_pow hq prime_21397 hd
                subst q
                change (2 : ZMod 586849264205765653)^27426707678916 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 279991 := Nat.prime_eq_prime_of_dvd_pow hq prime_279991 hd
                subst q
                change (2 : ZMod 586849264205765653)^2095957599372 ≠ 1
                reduce_mod_char
                decide

theorem prime_590707985621487631 : Nat.Prime 590707985621487631 := by
  apply lucas_primality 590707985621487631 (7 : ZMod 590707985621487631)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 590707985621487631 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((1021 : ℕ)^1 * ((1483482723377 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 590707985621487631)^295353992810743815 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 590707985621487631)^196902661873829210 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 590707985621487631)^118141597124297526 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (7 : ZMod 590707985621487631)^45439075817037510 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1021 := Nat.prime_eq_prime_of_dvd_pow hq prime_1021 hd
              subst q
              change (7 : ZMod 590707985621487631)^578558262117030 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1483482723377 := Nat.prime_eq_prime_of_dvd_pow hq prime_1483482723377 hd
              subst q
              change (7 : ZMod 590707985621487631)^398190 ≠ 1
              reduce_mod_char
              decide

theorem prime_594587827511515441 : Nat.Prime 594587827511515441 := by
  apply lucas_primality 594587827511515441 (11 : ZMod 594587827511515441)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 594587827511515441 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((89 : ℕ)^1 * ((56999 : ℕ)^1 * ((162789457 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 594587827511515441)^297293913755757720 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 594587827511515441)^198195942503838480 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 594587827511515441)^118917565502303088 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
            subst q
            change (11 : ZMod 594587827511515441)^6680762106870960 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 56999 := Nat.prime_eq_prime_of_dvd_pow hq prime_56999 hd
              subst q
              change (11 : ZMod 594587827511515441)^10431548404560 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 162789457 := Nat.prime_eq_prime_of_dvd_pow hq prime_162789457 hd
              subst q
              change (11 : ZMod 594587827511515441)^3652495920 ≠ 1
              reduce_mod_char
              decide

theorem prime_598488882256079467 : Nat.Prime 598488882256079467 := by
  apply lucas_primality 598488882256079467 (7 : ZMod 598488882256079467)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 598488882256079467 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((929 : ℕ)^1 * ((3947 : ℕ)^1 * ((27203325397 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 598488882256079467)^299244441128039733 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 598488882256079467)^199496294085359822 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 929 := Nat.prime_eq_prime_of_dvd_pow hq prime_929 hd
          subst q
          change (7 : ZMod 598488882256079467)^644229152051754 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3947 := Nat.prime_eq_prime_of_dvd_pow hq prime_3947 hd
            subst q
            change (7 : ZMod 598488882256079467)^151631335762878 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 27203325397 := Nat.prime_eq_prime_of_dvd_pow hq prime_27203325397 hd
            subst q
            change (7 : ZMod 598488882256079467)^22000578 ≠ 1
            reduce_mod_char
            decide

theorem prime_602411242538130491 : Nat.Prime 602411242538130491 := by
  apply lucas_primality 602411242538130491 (2 : ZMod 602411242538130491)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 602411242538130491 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((22273 : ℕ)^1 * ((2704670419513 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 602411242538130491)^301205621269065245 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 602411242538130491)^120482248507626098 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 22273 := Nat.prime_eq_prime_of_dvd_pow hq prime_22273 hd
          subst q
          change (2 : ZMod 602411242538130491)^27046704195130 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2704670419513 := Nat.prime_eq_prime_of_dvd_pow hq prime_2704670419513 hd
          subst q
          change (2 : ZMod 602411242538130491)^222730 ≠ 1
          reduce_mod_char
          decide

theorem prime_606355001344000009 : Nat.Prime 606355001344000009 := by
  apply lucas_primality 606355001344000009 (11 : ZMod 606355001344000009)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 606355001344000009 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((43 : ℕ)^1 * ((141067 : ℕ)^1 * ((1388355169 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 606355001344000009)^303177500672000004 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 606355001344000009)^202118333781333336 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (11 : ZMod 606355001344000009)^14101279101023256 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 141067 := Nat.prime_eq_prime_of_dvd_pow hq prime_141067 hd
            subst q
            change (11 : ZMod 606355001344000009)^4298347603224 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1388355169 := Nat.prime_eq_prime_of_dvd_pow hq prime_1388355169 hd
            subst q
            change (11 : ZMod 606355001344000009)^436743432 ≠ 1
            reduce_mod_char
            decide

theorem prime_610320251964061631 : Nat.Prime 610320251964061631 := by
  apply lucas_primality 610320251964061631 (11 : ZMod 610320251964061631)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 610320251964061631 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((61032025196406163 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 610320251964061631)^305160125982030815 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 610320251964061631)^122064050392812326 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 61032025196406163 := Nat.prime_eq_prime_of_dvd_pow hq prime_61032025196406163 hd
        subst q
        change (11 : ZMod 610320251964061631)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_614307087993392753 : Nat.Prime 614307087993392753 := by
  apply lucas_primality 614307087993392753 (3 : ZMod 614307087993392753)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 614307087993392753 - 1 = (2 : ℕ)^4 * ((7 : ℕ)^1 * ((37 : ℕ)^1 * ((181 : ℕ)^1 * ((38239 : ℕ)^1 * ((21418087 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 614307087993392753)^307153543996696376 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 614307087993392753)^87758155427627536 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (3 : ZMod 614307087993392753)^16602894270091696 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 181 := Nat.prime_eq_prime_of_dvd_pow hq prime_181 hd
            subst q
            change (3 : ZMod 614307087993392753)^3393961812118192 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 38239 := Nat.prime_eq_prime_of_dvd_pow hq prime_38239 hd
              subst q
              change (3 : ZMod 614307087993392753)^16064936007568 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 21418087 := Nat.prime_eq_prime_of_dvd_pow hq prime_21418087 hd
              subst q
              change (3 : ZMod 614307087993392753)^28681697296 ≠ 1
              reduce_mod_char
              decide

theorem prime_618315603332438093 : Nat.Prime 618315603332438093 := by
  apply lucas_primality 618315603332438093 (2 : ZMod 618315603332438093)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 618315603332438093 - 1 = (2 : ℕ)^2 * ((73 : ℕ)^1 * ((193 : ℕ)^1 * ((499 : ℕ)^1 * ((15739 : ℕ)^1 * ((1396987 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 618315603332438093)^309157801666219046 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
        subst q
        change (2 : ZMod 618315603332438093)^8470076757978604 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
          subst q
          change (2 : ZMod 618315603332438093)^3203707789287244 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 499 := Nat.prime_eq_prime_of_dvd_pow hq prime_499 hd
            subst q
            change (2 : ZMod 618315603332438093)^1239109425515908 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 15739 := Nat.prime_eq_prime_of_dvd_pow hq prime_15739 hd
              subst q
              change (2 : ZMod 618315603332438093)^39285571086628 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1396987 := Nat.prime_eq_prime_of_dvd_pow hq prime_1396987 hd
              subst q
              change (2 : ZMod 618315603332438093)^442606554916 ≠ 1
              reduce_mod_char
              decide

theorem prime_622345892187672617 : Nat.Prime 622345892187672617 := by
  apply lucas_primality 622345892187672617 (3 : ZMod 622345892187672617)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 622345892187672617 - 1 = (2 : ℕ)^3 * ((77793236523459077 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 622345892187672617)^311172946093836308 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 77793236523459077 := Nat.prime_eq_prime_of_dvd_pow hq prime_77793236523459077 hd
      subst q
      change (3 : ZMod 622345892187672617)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_625394597730972203 : Nat.Prime 625394597730972203 := by
  apply lucas_primality 625394597730972203 (2 : ZMod 625394597730972203)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 625394597730972203 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((149 : ℕ)^1 * ((7317169 : ℕ)^1 * ((40972903 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 625394597730972203)^312697298865486101 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 625394597730972203)^89342085390138886 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
          subst q
          change (2 : ZMod 625394597730972203)^4197279179402498 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7317169 := Nat.prime_eq_prime_of_dvd_pow hq prime_7317169 hd
            subst q
            change (2 : ZMod 625394597730972203)^85469475658 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 40972903 := Nat.prime_eq_prime_of_dvd_pow hq prime_40972903 hd
            subst q
            change (2 : ZMod 625394597730972203)^15263614534 ≠ 1
            reduce_mod_char
            decide

theorem prime_626398049072265629 : Nat.Prime 626398049072265629 := by
  apply lucas_primality 626398049072265629 (2 : ZMod 626398049072265629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 626398049072265629 - 1 = (2 : ℕ)^2 * ((547 : ℕ)^1 * ((286287956614381 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 626398049072265629)^313199024536132814 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 547 := Nat.prime_eq_prime_of_dvd_pow hq prime_547 hd
        subst q
        change (2 : ZMod 626398049072265629)^1145151826457524 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 286287956614381 := Nat.prime_eq_prime_of_dvd_pow hq prime_286287956614381 hd
        subst q
        change (2 : ZMod 626398049072265629)^2188 ≠ 1
        reduce_mod_char
        decide

theorem prime_630472168806746251 : Nat.Prime 630472168806746251 := by
  apply lucas_primality 630472168806746251 (3 : ZMod 630472168806746251)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 630472168806746251 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^4 * ((41 : ℕ)^1 * ((4100631992239 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 630472168806746251)^315236084403373125 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 630472168806746251)^210157389602248750 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 630472168806746251)^126094433761349250 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (3 : ZMod 630472168806746251)^15377369970896250 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 4100631992239 := Nat.prime_eq_prime_of_dvd_pow hq prime_4100631992239 hd
            subst q
            change (3 : ZMod 630472168806746251)^153750 ≠ 1
            reduce_mod_char
            decide

theorem prime_634568346519668371 : Nat.Prime 634568346519668371 := by
  apply lucas_primality 634568346519668371 (2 : ZMod 634568346519668371)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 634568346519668371 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((46083394808981 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 634568346519668371)^317284173259834185 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 634568346519668371)^211522782173222790 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 634568346519668371)^126913669303933674 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (2 : ZMod 634568346519668371)^37327549795274610 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 46083394808981 := Nat.prime_eq_prime_of_dvd_pow hq prime_46083394808981 hd
            subst q
            change (2 : ZMod 634568346519668371)^13770 ≠ 1
            reduce_mod_char
            decide

theorem prime_638686677648277541 : Nat.Prime 638686677648277541 := by
  apply lucas_primality 638686677648277541 (3 : ZMod 638686677648277541)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 638686677648277541 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((41 : ℕ)^2 * ((241 : ℕ)^1 * ((2657 : ℕ)^1 * ((29667541 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 638686677648277541)^319343338824138770 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 638686677648277541)^127737335529655508 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (3 : ZMod 638686677648277541)^15577723845079940 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 241 := Nat.prime_eq_prime_of_dvd_pow hq prime_241 hd
            subst q
            change (3 : ZMod 638686677648277541)^2650152189411940 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 2657 := Nat.prime_eq_prime_of_dvd_pow hq prime_2657 hd
              subst q
              change (3 : ZMod 638686677648277541)^240378877549220 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 29667541 := Nat.prime_eq_prime_of_dvd_pow hq prime_29667541 hd
              subst q
              change (3 : ZMod 638686677648277541)^21528129940 ≠ 1
              reduce_mod_char
              decide

theorem prime_642827257939177963 : Nat.Prime 642827257939177963 := by
  apply lucas_primality 642827257939177963 (5 : ZMod 642827257939177963)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 642827257939177963 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((79 : ℕ)^1 * ((81019 : ℕ)^1 * ((2391283261 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 642827257939177963)^321413628969588981 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 642827257939177963)^214275752646392654 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 642827257939177963)^91832465419882566 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
            subst q
            change (5 : ZMod 642827257939177963)^8137053897964278 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 81019 := Nat.prime_eq_prime_of_dvd_pow hq prime_81019 hd
              subst q
              change (5 : ZMod 642827257939177963)^7934277859998 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 2391283261 := Nat.prime_eq_prime_of_dvd_pow hq prime_2391283261 hd
              subst q
              change (5 : ZMod 642827257939177963)^268821042 ≠ 1
              reduce_mod_char
              decide

theorem prime_646990183449000011 : Nat.Prime 646990183449000011 := by
  apply lucas_primality 646990183449000011 (2 : ZMod 646990183449000011)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 646990183449000011 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((607 : ℕ)^1 * ((227303 : ℕ)^1 * ((468925481 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 646990183449000011)^323495091724500005 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 646990183449000011)^129398036689800002 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 607 := Nat.prime_eq_prime_of_dvd_pow hq prime_607 hd
          subst q
          change (2 : ZMod 646990183449000011)^1065881686077430 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 227303 := Nat.prime_eq_prime_of_dvd_pow hq prime_227303 hd
            subst q
            change (2 : ZMod 646990183449000011)^2846377669670 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 468925481 := Nat.prime_eq_prime_of_dvd_pow hq prime_468925481 hd
            subst q
            change (2 : ZMod 646990183449000011)^1379729210 ≠ 1
            reduce_mod_char
            decide

theorem prime_651175550545069117 : Nat.Prime 651175550545069117 := by
  apply lucas_primality 651175550545069117 (2 : ZMod 651175550545069117)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 651175550545069117 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((17 : ℕ)^1 * ((47 : ℕ)^1 * ((1078026684389 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 651175550545069117)^325587775272534558 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 651175550545069117)^217058516848356372 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 651175550545069117)^93025078649295588 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (2 : ZMod 651175550545069117)^38304444149709948 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
              subst q
              change (2 : ZMod 651175550545069117)^13854798947767428 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1078026684389 := Nat.prime_eq_prime_of_dvd_pow hq prime_1078026684389 hd
              subst q
              change (2 : ZMod 651175550545069117)^604044 ≠ 1
              reduce_mod_char
              decide

theorem prime_655383455906074627 : Nat.Prime 655383455906074627 := by
  apply lucas_primality 655383455906074627 (2 : ZMod 655383455906074627)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 655383455906074627 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((89 : ℕ)^1 * ((283 : ℕ)^1 * ((61121 : ℕ)^1 * ((4173769 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 655383455906074627)^327691727953037313 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 655383455906074627)^218461151968691542 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 655383455906074627)^38551967994474978 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
            subst q
            change (2 : ZMod 655383455906074627)^7363859055124434 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 283 := Nat.prime_eq_prime_of_dvd_pow hq prime_283 hd
              subst q
              change (2 : ZMod 655383455906074627)^2315842600374822 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 61121 := Nat.prime_eq_prime_of_dvd_pow hq prime_61121 hd
                subst q
                change (2 : ZMod 655383455906074627)^10722721419906 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 4173769 := Nat.prime_eq_prime_of_dvd_pow hq prime_4173769 hd
                subst q
                change (2 : ZMod 655383455906074627)^157024371954 ≠ 1
                reduce_mod_char
                decide

theorem prime_659613996522740227 : Nat.Prime 659613996522740227 := by
  apply lucas_primality 659613996522740227 (2 : ZMod 659613996522740227)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 659613996522740227 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((1063 : ℕ)^1 * ((98717 : ℕ)^1 * ((95240291 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 659613996522740227)^329806998261370113 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 659613996522740227)^219871332174246742 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 659613996522740227)^59964908774794566 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1063 := Nat.prime_eq_prime_of_dvd_pow hq prime_1063 hd
            subst q
            change (2 : ZMod 659613996522740227)^620521163238702 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 98717 := Nat.prime_eq_prime_of_dvd_pow hq prime_98717 hd
              subst q
              change (2 : ZMod 659613996522740227)^6681868335978 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 95240291 := Nat.prime_eq_prime_of_dvd_pow hq prime_95240291 hd
              subst q
              change (2 : ZMod 659613996522740227)^6925787286 ≠ 1
              reduce_mod_char
              decide

theorem prime_663867269698494053 : Nat.Prime 663867269698494053 := by
  apply lucas_primality 663867269698494053 (2 : ZMod 663867269698494053)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 663867269698494053 - 1 = (2 : ℕ)^2 * ((1693 : ℕ)^1 * ((98031197533741 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 663867269698494053)^331933634849247026 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1693 := Nat.prime_eq_prime_of_dvd_pow hq prime_1693 hd
        subst q
        change (2 : ZMod 663867269698494053)^392124790134964 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 98031197533741 := Nat.prime_eq_prime_of_dvd_pow hq prime_98031197533741 hd
        subst q
        change (2 : ZMod 663867269698494053)^6772 ≠ 1
        reduce_mod_char
        decide

theorem prime_668143373050140667 : Nat.Prime 668143373050140667 := by
  apply lucas_primality 668143373050140667 (2 : ZMod 668143373050140667)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 668143373050140667 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((61 : ℕ)^1 * ((260789763095293 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 668143373050140667)^334071686525070333 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 668143373050140667)^222714457683380222 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 668143373050140667)^95449053292877238 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
            subst q
            change (2 : ZMod 668143373050140667)^10953170050002306 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 260789763095293 := Nat.prime_eq_prime_of_dvd_pow hq prime_260789763095293 hd
            subst q
            change (2 : ZMod 668143373050140667)^2562 ≠ 1
            reduce_mod_char
            decide

theorem prime_672442404508532759 : Nat.Prime 672442404508532759 := by
  apply lucas_primality 672442404508532759 (17 : ZMod 672442404508532759)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 672442404508532759 - 1 = (2 : ℕ)^1 * ((5393 : ℕ)^1 * ((62344001901403 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 672442404508532759)^336221202254266379 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5393 := Nat.prime_eq_prime_of_dvd_pow hq prime_5393 hd
        subst q
        change (17 : ZMod 672442404508532759)^124688003802806 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 62344001901403 := Nat.prime_eq_prime_of_dvd_pow hq prime_62344001901403 hd
        subst q
        change (17 : ZMod 672442404508532759)^10786 ≠ 1
        reduce_mod_char
        decide

theorem prime_676764462319244237 : Nat.Prime 676764462319244237 := by
  apply lucas_primality 676764462319244237 (5 : ZMod 676764462319244237)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 676764462319244237 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((19 : ℕ)^1 * ((31 : ℕ)^1 * ((37 : ℕ)^1 * ((103 : ℕ)^1 * ((109 : ℕ)^1 * ((151 : ℕ)^1 * ((307 : ℕ)^1 * ((2131 : ℕ)^1))))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 676764462319244237)^338382231159622118 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 676764462319244237)^96680637474177748 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (5 : ZMod 676764462319244237)^35619182227328644 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (5 : ZMod 676764462319244237)^21831111687717556 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
              subst q
              change (5 : ZMod 676764462319244237)^18290931414033628 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
                subst q
                change (5 : ZMod 676764462319244237)^6570528760381012 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
                  subst q
                  change (5 : ZMod 676764462319244237)^6208848278158204 ≠ 1
                  reduce_mod_char
                  decide
                · rcases hq.dvd_mul.mp hd with hd | hd
                  · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
                    subst q
                    change (5 : ZMod 676764462319244237)^4481883856418836 ≠ 1
                    reduce_mod_char
                    decide
                  · rcases hq.dvd_mul.mp hd with hd | hd
                    · have heq : q = 307 := Nat.prime_eq_prime_of_dvd_pow hq prime_307 hd
                      subst q
                      change (5 : ZMod 676764462319244237)^2204444502668548 ≠ 1
                      reduce_mod_char
                      decide
                    · have heq : q = 2131 := Nat.prime_eq_prime_of_dvd_pow hq prime_2131 hd
                      subst q
                      change (5 : ZMod 676764462319244237)^317580695597956 ≠ 1
                      reduce_mod_char
                      decide

theorem prime_681109645043243629 : Nat.Prime 681109645043243629 := by
  apply lucas_primality 681109645043243629 (2 : ZMod 681109645043243629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 681109645043243629 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^5 * ((367 : ℕ)^1 * ((1909346287447 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 681109645043243629)^340554822521621814 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 681109645043243629)^227036548347747876 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 367 := Nat.prime_eq_prime_of_dvd_pow hq prime_367 hd
          subst q
          change (2 : ZMod 681109645043243629)^1855884591398484 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1909346287447 := Nat.prime_eq_prime_of_dvd_pow hq prime_1909346287447 hd
          subst q
          change (2 : ZMod 681109645043243629)^356724 ≠ 1
          reduce_mod_char
          decide

theorem prime_685478051557568441 : Nat.Prime 685478051557568441 := by
  apply lucas_primality 685478051557568441 (6 : ZMod 685478051557568441)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 685478051557568441 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((919 : ℕ)^1 * ((18647389868269 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 685478051557568441)^342739025778784220 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 685478051557568441)^137095610311513688 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 919 := Nat.prime_eq_prime_of_dvd_pow hq prime_919 hd
          subst q
          change (6 : ZMod 685478051557568441)^745895594730760 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 18647389868269 := Nat.prime_eq_prime_of_dvd_pow hq prime_18647389868269 hd
          subst q
          change (6 : ZMod 685478051557568441)^36760 ≠ 1
          reduce_mod_char
          decide

theorem prime_689869781056000033 : Nat.Prime 689869781056000033 := by
  apply lucas_primality 689869781056000033 (5 : ZMod 689869781056000033)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 689869781056000033 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((283 : ℕ)^1 * ((1493690200097 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 689869781056000033)^344934890528000016 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 689869781056000033)^229956593685333344 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (5 : ZMod 689869781056000033)^40580575356235296 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 283 := Nat.prime_eq_prime_of_dvd_pow hq prime_283 hd
            subst q
            change (5 : ZMod 689869781056000033)^2437702406558304 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1493690200097 := Nat.prime_eq_prime_of_dvd_pow hq prime_1493690200097 hd
            subst q
            change (5 : ZMod 689869781056000033)^461856 ≠ 1
            reduce_mod_char
            decide

theorem prime_694284933049739653 : Nat.Prime 694284933049739653 := by
  apply lucas_primality 694284933049739653 (2 : ZMod 694284933049739653)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 694284933049739653 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((179 : ℕ)^1 * ((214457 : ℕ)^1 * ((1507173457 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 694284933049739653)^347142466524869826 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 694284933049739653)^231428311016579884 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 179 := Nat.prime_eq_prime_of_dvd_pow hq prime_179 hd
          subst q
          change (2 : ZMod 694284933049739653)^3878686776814188 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 214457 := Nat.prime_eq_prime_of_dvd_pow hq prime_214457 hd
            subst q
            change (2 : ZMod 694284933049739653)^3237408585636 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1507173457 := Nat.prime_eq_prime_of_dvd_pow hq prime_1507173457 hd
            subst q
            change (2 : ZMod 694284933049739653)^460653636 ≠ 1
            reduce_mod_char
            decide

theorem prime_698723607368084647 : Nat.Prime 698723607368084647 := by
  apply lucas_primality 698723607368084647 (6 : ZMod 698723607368084647)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 698723607368084647 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((35141 : ℕ)^1 * ((3313904970301 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 698723607368084647)^349361803684042323 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 698723607368084647)^232907869122694882 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 35141 := Nat.prime_eq_prime_of_dvd_pow hq prime_35141 hd
          subst q
          change (6 : ZMod 698723607368084647)^19883429821806 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3313904970301 := Nat.prime_eq_prime_of_dvd_pow hq prime_3313904970301 hd
          subst q
          change (6 : ZMod 698723607368084647)^210846 ≠ 1
          reduce_mod_char
          decide

theorem prime_703185904159105351 : Nat.Prime 703185904159105351 := by
  apply lucas_primality 703185904159105351 (3 : ZMod 703185904159105351)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 703185904159105351 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((1933 : ℕ)^1 * ((2425197117293 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 703185904159105351)^351592952079552675 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 703185904159105351)^234395301386368450 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 703185904159105351)^140637180831821070 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1933 := Nat.prime_eq_prime_of_dvd_pow hq prime_1933 hd
            subst q
            change (3 : ZMod 703185904159105351)^363779567593950 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2425197117293 := Nat.prime_eq_prime_of_dvd_pow hq prime_2425197117293 hd
            subst q
            change (3 : ZMod 703185904159105351)^289950 ≠ 1
            reduce_mod_char
            decide

theorem prime_707671923890323463 : Nat.Prime 707671923890323463 := by
  apply lucas_primality 707671923890323463 (7 : ZMod 707671923890323463)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 707671923890323463 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((19763 : ℕ)^1 * ((2557708574791 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 707671923890323463)^353835961945161731 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 707671923890323463)^101095989127189066 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19763 := Nat.prime_eq_prime_of_dvd_pow hq prime_19763 hd
          subst q
          change (7 : ZMod 707671923890323463)^35807920047074 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2557708574791 := Nat.prime_eq_prime_of_dvd_pow hq prime_2557708574791 hd
          subst q
          change (7 : ZMod 707671923890323463)^276682 ≠ 1
          reduce_mod_char
          decide

theorem prime_712181767349390627 : Nat.Prime 712181767349390627 := by
  apply lucas_primality 712181767349390627 (2 : ZMod 712181767349390627)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 712181767349390627 - 1 = (2 : ℕ)^1 * ((29 : ℕ)^1 * ((89 : ℕ)^1 * ((173 : ℕ)^1 * ((36433 : ℕ)^1 * ((21889297 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 712181767349390627)^356090883674695313 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (2 : ZMod 712181767349390627)^24557991977565194 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (2 : ZMod 712181767349390627)^8002042329768434 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
            subst q
            change (2 : ZMod 712181767349390627)^4116657614736362 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 36433 := Nat.prime_eq_prime_of_dvd_pow hq prime_36433 hd
              subst q
              change (2 : ZMod 712181767349390627)^19547711342722 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 21889297 := Nat.prime_eq_prime_of_dvd_pow hq prime_21889297 hd
              subst q
              change (2 : ZMod 712181767349390627)^32535616258 ≠ 1
              reduce_mod_char
              decide

theorem prime_716715535644767299 : Nat.Prime 716715535644767299 := by
  apply lucas_primality 716715535644767299 (2 : ZMod 716715535644767299)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 716715535644767299 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1019 : ℕ)^1 * ((1097 : ℕ)^1 * ((4211 : ℕ)^1 * ((25376371 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 716715535644767299)^358357767822383649 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 716715535644767299)^238905178548255766 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1019 := Nat.prime_eq_prime_of_dvd_pow hq prime_1019 hd
          subst q
          change (2 : ZMod 716715535644767299)^703351850485542 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1097 := Nat.prime_eq_prime_of_dvd_pow hq prime_1097 hd
            subst q
            change (2 : ZMod 716715535644767299)^653341418090034 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 4211 := Nat.prime_eq_prime_of_dvd_pow hq prime_4211 hd
              subst q
              change (2 : ZMod 716715535644767299)^170200792126518 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 25376371 := Nat.prime_eq_prime_of_dvd_pow hq prime_25376371 hd
              subst q
              change (2 : ZMod 716715535644767299)^28243421238 ≠ 1
              reduce_mod_char
              decide

theorem prime_721273330206403259 : Nat.Prime 721273330206403259 := by
  apply lucas_primality 721273330206403259 (2 : ZMod 721273330206403259)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 721273330206403259 - 1 = (2 : ℕ)^1 * ((1171619 : ℕ)^1 * ((307810529791 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 721273330206403259)^360636665103201629 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1171619 := Nat.prime_eq_prime_of_dvd_pow hq prime_1171619 hd
        subst q
        change (2 : ZMod 721273330206403259)^615621059582 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 307810529791 := Nat.prime_eq_prime_of_dvd_pow hq prime_307810529791 hd
        subst q
        change (2 : ZMod 721273330206403259)^2343238 ≠ 1
        reduce_mod_char
        decide

theorem prime_725855252786417669 : Nat.Prime 725855252786417669 := by
  apply lucas_primality 725855252786417669 (2 : ZMod 725855252786417669)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 725855252786417669 - 1 = (2 : ℕ)^2 * ((4129 : ℕ)^1 * ((43948610607073 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 725855252786417669)^362927626393208834 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 4129 := Nat.prime_eq_prime_of_dvd_pow hq prime_4129 hd
        subst q
        change (2 : ZMod 725855252786417669)^175794442428292 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 43948610607073 := Nat.prime_eq_prime_of_dvd_pow hq prime_43948610607073 hd
        subst q
        change (2 : ZMod 725855252786417669)^16516 ≠ 1
        reduce_mod_char
        decide

theorem prime_730461405459781847 : Nat.Prime 730461405459781847 := by
  apply lucas_primality 730461405459781847 (5 : ZMod 730461405459781847)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 730461405459781847 - 1 = (2 : ℕ)^1 * ((29 : ℕ)^1 * ((43 : ℕ)^1 * ((3163 : ℕ)^1 * ((92598005743 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 730461405459781847)^365230702729890923 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (5 : ZMod 730461405459781847)^25188324326199374 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (5 : ZMod 730461405459781847)^16987474545576322 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3163 := Nat.prime_eq_prime_of_dvd_pow hq prime_3163 hd
            subst q
            change (5 : ZMod 730461405459781847)^230939426323042 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 92598005743 := Nat.prime_eq_prime_of_dvd_pow hq prime_92598005743 hd
            subst q
            change (5 : ZMod 730461405459781847)^7888522 ≠ 1
            reduce_mod_char
            decide

theorem prime_735091890625000079 : Nat.Prime 735091890625000079 := by
  apply lucas_primality 735091890625000079 (13 : ZMod 735091890625000079)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 735091890625000079 - 1 = (2 : ℕ)^1 * ((11211883 : ℕ)^1 * ((32781821333 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 735091890625000079)^367545945312500039 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11211883 := Nat.prime_eq_prime_of_dvd_pow hq prime_11211883 hd
        subst q
        change (13 : ZMod 735091890625000079)^65563642666 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 32781821333 := Nat.prime_eq_prime_of_dvd_pow hq prime_32781821333 hd
        subst q
        change (13 : ZMod 735091890625000079)^22423766 ≠ 1
        reduce_mod_char
        decide

theorem prime_739746811004793227 : Nat.Prime 739746811004793227 := by
  apply lucas_primality 739746811004793227 (2 : ZMod 739746811004793227)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 739746811004793227 - 1 = (2 : ℕ)^1 * ((401 : ℕ)^1 * ((922377569831413 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 739746811004793227)^369873405502396613 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 401 := Nat.prime_eq_prime_of_dvd_pow hq prime_401 hd
        subst q
        change (2 : ZMod 739746811004793227)^1844755139662826 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 922377569831413 := Nat.prime_eq_prime_of_dvd_pow hq prime_922377569831413 hd
        subst q
        change (2 : ZMod 739746811004793227)^802 ≠ 1
        reduce_mod_char
        decide

theorem prime_744426269646782561 : Nat.Prime 744426269646782561 := by
  apply lucas_primality 744426269646782561 (3 : ZMod 744426269646782561)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 744426269646782561 - 1 = (2 : ℕ)^5 * ((5 : ℕ)^1 * ((4652664185292391 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 744426269646782561)^372213134823391280 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 744426269646782561)^148885253929356512 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 4652664185292391 := Nat.prime_eq_prime_of_dvd_pow hq prime_4652664185292391 hd
        subst q
        change (3 : ZMod 744426269646782561)^160 ≠ 1
        reduce_mod_char
        decide

theorem prime_749130369924173387 : Nat.Prime 749130369924173387 := by
  apply lucas_primality 749130369924173387 (2 : ZMod 749130369924173387)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 749130369924173387 - 1 = (2 : ℕ)^1 * ((374565184962086693 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 749130369924173387)^374565184962086693 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 374565184962086693 := Nat.prime_eq_prime_of_dvd_pow hq prime_374565184962086693 hd
      subst q
      change (2 : ZMod 749130369924173387)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_753859215536440987 : Nat.Prime 753859215536440987 := by
  apply lucas_primality 753859215536440987 (3 : ZMod 753859215536440987)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 753859215536440987 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((41 : ℕ)^1 * ((659 : ℕ)^1 * ((221437123769 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 753859215536440987)^376929607768220493 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 753859215536440987)^251286405178813662 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 753859215536440987)^107694173648062998 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (3 : ZMod 753859215536440987)^18386810135035146 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 659 := Nat.prime_eq_prime_of_dvd_pow hq prime_659 hd
              subst q
              change (3 : ZMod 753859215536440987)^1143944181390654 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 221437123769 := Nat.prime_eq_prime_of_dvd_pow hq prime_221437123769 hd
              subst q
              change (3 : ZMod 753859215536440987)^3404394 ≠ 1
              reduce_mod_char
              decide

theorem prime_758612910510015683 : Nat.Prime 758612910510015683 := by
  apply lucas_primality 758612910510015683 (2 : ZMod 758612910510015683)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 758612910510015683 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((38393 : ℕ)^1 * ((898143021467 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 758612910510015683)^379306455255007841 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 758612910510015683)^68964810046365062 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 38393 := Nat.prime_eq_prime_of_dvd_pow hq prime_38393 hd
          subst q
          change (2 : ZMod 758612910510015683)^19759146472274 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 898143021467 := Nat.prime_eq_prime_of_dvd_pow hq prime_898143021467 hd
          subst q
          change (2 : ZMod 758612910510015683)^844646 ≠ 1
          reduce_mod_char
          decide

theorem prime_763391559198969947 : Nat.Prime 763391559198969947 := by
  apply lucas_primality 763391559198969947 (2 : ZMod 763391559198969947)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 763391559198969947 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((601 : ℕ)^1 * ((1499 : ℕ)^1 * ((60526172761 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 763391559198969947)^381695779599484973 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 763391559198969947)^109055937028424278 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 601 := Nat.prime_eq_prime_of_dvd_pow hq prime_601 hd
          subst q
          change (2 : ZMod 763391559198969947)^1270202261562346 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1499 := Nat.prime_eq_prime_of_dvd_pow hq prime_1499 hd
            subst q
            change (2 : ZMod 763391559198969947)^509267217611054 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 60526172761 := Nat.prime_eq_prime_of_dvd_pow hq prime_60526172761 hd
            subst q
            change (2 : ZMod 763391559198969947)^12612586 ≠ 1
            reduce_mod_char
            decide

theorem prime_768195266285705087 : Nat.Prime 768195266285705087 := by
  apply lucas_primality 768195266285705087 (5 : ZMod 768195266285705087)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 768195266285705087 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((233 : ℕ)^1 * ((380059 : ℕ)^1 * ((228286951 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 768195266285705087)^384097633142852543 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (5 : ZMod 768195266285705087)^40431329804510794 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
          subst q
          change (5 : ZMod 768195266285705087)^3296975391784142 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 380059 := Nat.prime_eq_prime_of_dvd_pow hq prime_380059 hd
            subst q
            change (5 : ZMod 768195266285705087)^2021252664154 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 228286951 := Nat.prime_eq_prime_of_dvd_pow hq prime_228286951 hd
            subst q
            change (5 : ZMod 768195266285705087)^3365042386 ≠ 1
            reduce_mod_char
            decide

theorem prime_773024136781639751 : Nat.Prime 773024136781639751 := by
  apply lucas_primality 773024136781639751 (7 : ZMod 773024136781639751)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 773024136781639751 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^3 * ((7 : ℕ)^1 * ((441728078160937 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 773024136781639751)^386512068390819875 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 773024136781639751)^154604827356327950 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 773024136781639751)^110432019540234250 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 441728078160937 := Nat.prime_eq_prime_of_dvd_pow hq prime_441728078160937 hd
          subst q
          change (7 : ZMod 773024136781639751)^1750 ≠ 1
          reduce_mod_char
          decide

theorem prime_777878276027898377 : Nat.Prime 777878276027898377 := by
  apply lucas_primality 777878276027898377 (3 : ZMod 777878276027898377)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 777878276027898377 - 1 = (2 : ℕ)^3 * ((83 : ℕ)^1 * ((508943 : ℕ)^1 * ((2301836213 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 777878276027898377)^388939138013949188 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
        subst q
        change (3 : ZMod 777878276027898377)^9372027422022872 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 508943 := Nat.prime_eq_prime_of_dvd_pow hq prime_508943 hd
          subst q
          change (3 : ZMod 777878276027898377)^1528419245432 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2301836213 := Nat.prime_eq_prime_of_dvd_pow hq prime_2301836213 hd
          subst q
          change (3 : ZMod 777878276027898377)^337938152 ≠ 1
          reduce_mod_char
          decide

theorem prime_782757789696000007 : Nat.Prime 782757789696000007 := by
  apply lucas_primality 782757789696000007 (3 : ZMod 782757789696000007)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 782757789696000007 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((3659 : ℕ)^1 * ((5093492820677 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 782757789696000007)^391378894848000003 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 782757789696000007)^260919263232000002 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 782757789696000007)^111822541385142858 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3659 := Nat.prime_eq_prime_of_dvd_pow hq prime_3659 hd
            subst q
            change (3 : ZMod 782757789696000007)^213926698468434 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 5093492820677 := Nat.prime_eq_prime_of_dvd_pow hq prime_5093492820677 hd
            subst q
            change (3 : ZMod 782757789696000007)^153678 ≠ 1
            reduce_mod_char
            decide

theorem prime_787662783788549789 : Nat.Prime 787662783788549789 := by
  apply lucas_primality 787662783788549789 (2 : ZMod 787662783788549789)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 787662783788549789 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((61 : ℕ)^1 * ((15187 : ℕ)^1 * ((32983 : ℕ)^1 * ((920641 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 787662783788549789)^393831391894274894 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 787662783788549789)^112523254826935684 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (2 : ZMod 787662783788549789)^12912504652271308 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 15187 := Nat.prime_eq_prime_of_dvd_pow hq prime_15187 hd
            subst q
            change (2 : ZMod 787662783788549789)^51864277591924 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 32983 := Nat.prime_eq_prime_of_dvd_pow hq prime_32983 hd
              subst q
              change (2 : ZMod 787662783788549789)^23880871472836 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 920641 := Nat.prime_eq_prime_of_dvd_pow hq prime_920641 hd
              subst q
              change (2 : ZMod 787662783788549789)^855559098268 ≠ 1
              reduce_mod_char
              decide

theorem prime_792593364639928393 : Nat.Prime 792593364639928393 := by
  apply lucas_primality 792593364639928393 (5 : ZMod 792593364639928393)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 792593364639928393 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((17 : ℕ)^1 * ((43 : ℕ)^1 * ((211 : ℕ)^1 * ((547 : ℕ)^1 * ((130476043 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 792593364639928393)^396296682319964196 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 792593364639928393)^264197788213309464 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (5 : ZMod 792593364639928393)^46623139096466376 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (5 : ZMod 792593364639928393)^18432403828835544 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 211 := Nat.prime_eq_prime_of_dvd_pow hq prime_211 hd
              subst q
              change (5 : ZMod 792593364639928393)^3756366657061272 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 547 := Nat.prime_eq_prime_of_dvd_pow hq prime_547 hd
                subst q
                change (5 : ZMod 792593364639928393)^1448982385082136 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 130476043 := Nat.prime_eq_prime_of_dvd_pow hq prime_130476043 hd
                subst q
                change (5 : ZMod 792593364639928393)^6074627544 ≠ 1
                reduce_mod_char
                decide

theorem prime_797549638916984431 : Nat.Prime 797549638916984431 := by
  apply lucas_primality 797549638916984431 (11 : ZMod 797549638916984431)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 797549638916984431 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((439 : ℕ)^1 * ((60558059143279 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 797549638916984431)^398774819458492215 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 797549638916984431)^265849879638994810 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 797549638916984431)^159509927783396886 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 439 := Nat.prime_eq_prime_of_dvd_pow hq prime_439 hd
            subst q
            change (11 : ZMod 797549638916984431)^1816741774298370 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 60558059143279 := Nat.prime_eq_prime_of_dvd_pow hq prime_60558059143279 hd
            subst q
            change (11 : ZMod 797549638916984431)^13170 ≠ 1
            reduce_mod_char
            decide

theorem prime_802531713619726361 : Nat.Prime 802531713619726361 := by
  apply lucas_primality 802531713619726361 (6 : ZMod 802531713619726361)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 802531713619726361 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((101 : ℕ)^1 * ((271 : ℕ)^1 * ((17569 : ℕ)^1 * ((41721941 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 802531713619726361)^401265856809863180 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 802531713619726361)^160506342723945272 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
          subst q
          change (6 : ZMod 802531713619726361)^7945858550690360 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 271 := Nat.prime_eq_prime_of_dvd_pow hq prime_271 hd
            subst q
            change (6 : ZMod 802531713619726361)^2961371636973160 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 17569 := Nat.prime_eq_prime_of_dvd_pow hq prime_17569 hd
              subst q
              change (6 : ZMod 802531713619726361)^45678849884440 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 41721941 := Nat.prime_eq_prime_of_dvd_pow hq prime_41721941 hd
              subst q
              change (6 : ZMod 802531713619726361)^19235243960 ≠ 1
              reduce_mod_char
              decide

theorem prime_807539696082015703 : Nat.Prime 807539696082015703 := by
  apply lucas_primality 807539696082015703 (3 : ZMod 807539696082015703)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 807539696082015703 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((101 : ℕ)^1 * ((1949 : ℕ)^1 * ((52593983341 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 807539696082015703)^403769848041007851 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 807539696082015703)^269179898694005234 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 807539696082015703)^62118438160155054 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
            subst q
            change (3 : ZMod 807539696082015703)^7995442535465502 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1949 := Nat.prime_eq_prime_of_dvd_pow hq prime_1949 hd
              subst q
              change (3 : ZMod 807539696082015703)^414335400760398 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 52593983341 := Nat.prime_eq_prime_of_dvd_pow hq prime_52593983341 hd
              subst q
              change (3 : ZMod 807539696082015703)^15354222 ≠ 1
              reduce_mod_char
              decide

theorem prime_812573693972260481 : Nat.Prime 812573693972260481 := by
  apply lucas_primality 812573693972260481 (3 : ZMod 812573693972260481)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 812573693972260481 - 1 = (2 : ℕ)^7 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((41 : ℕ)^1 * ((569 : ℕ)^1 * ((4186424941 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 812573693972260481)^406286846986130240 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 812573693972260481)^162514738794452096 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 812573693972260481)^62505668767096960 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (3 : ZMod 812573693972260481)^19818870584689280 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 569 := Nat.prime_eq_prime_of_dvd_pow hq prime_569 hd
              subst q
              change (3 : ZMod 812573693972260481)^1428073275873920 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 4186424941 := Nat.prime_eq_prime_of_dvd_pow hq prime_4186424941 hd
              subst q
              change (3 : ZMod 812573693972260481)^194097280 ≠ 1
              reduce_mod_char
              decide

theorem prime_817633815294109993 : Nat.Prime 817633815294109993 := by
  apply lucas_primality 817633815294109993 (10 : ZMod 817633815294109993)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 817633815294109993 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((197 : ℕ)^1 * ((100907 : ℕ)^1 * ((1713799777 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 817633815294109993)^408816907647054996 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 817633815294109993)^272544605098036664 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
          subst q
          change (10 : ZMod 817633815294109993)^4150425458345736 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 100907 := Nat.prime_eq_prime_of_dvd_pow hq prime_100907 hd
            subst q
            change (10 : ZMod 817633815294109993)^8102845345656 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1713799777 := Nat.prime_eq_prime_of_dvd_pow hq prime_1713799777 hd
            subst q
            change (10 : ZMod 817633815294109993)^477088296 ≠ 1
            reduce_mod_char
            decide

theorem prime_822720168387149881 : Nat.Prime 822720168387149881 := by
  apply lucas_primality 822720168387149881 (11 : ZMod 822720168387149881)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 822720168387149881 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((19 : ℕ)^1 * ((11238587 : ℕ)^1 * ((32107433 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 822720168387149881)^411360084193574940 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 822720168387149881)^274240056129049960 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 822720168387149881)^164544033677429976 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (11 : ZMod 822720168387149881)^43301061494060520 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 11238587 := Nat.prime_eq_prime_of_dvd_pow hq prime_11238587 hd
              subst q
              change (11 : ZMod 822720168387149881)^73204947240 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 32107433 := Nat.prime_eq_prime_of_dvd_pow hq prime_32107433 hd
              subst q
              change (11 : ZMod 822720168387149881)^25623978360 ≠ 1
              reduce_mod_char
              decide

theorem prime_827832861927597709 : Nat.Prime 827832861927597709 := by
  apply lucas_primality 827832861927597709 (17 : ZMod 827832861927597709)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 827832861927597709 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((13 : ℕ)^2 * ((67 : ℕ)^1 * ((463 : ℕ)^1 * ((4657 : ℕ)^1 * ((44851 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 827832861927597709)^413916430963798854 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 827832861927597709)^275944287309199236 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (17 : ZMod 827832861927597709)^118261837418228244 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (17 : ZMod 827832861927597709)^63679450917507516 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
              subst q
              change (17 : ZMod 827832861927597709)^12355714357128324 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 463 := Nat.prime_eq_prime_of_dvd_pow hq prime_463 hd
                subst q
                change (17 : ZMod 827832861927597709)^1787975943688116 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 4657 := Nat.prime_eq_prime_of_dvd_pow hq prime_4657 hd
                  subst q
                  change (17 : ZMod 827832861927597709)^177760975290444 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 44851 := Nat.prime_eq_prime_of_dvd_pow hq prime_44851 hd
                  subst q
                  change (17 : ZMod 827832861927597709)^18457400323908 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_832972004929000007 : Nat.Prime 832972004929000007 := by
  apply lucas_primality 832972004929000007 (5 : ZMod 832972004929000007)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 832972004929000007 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((8243 : ℕ)^1 * ((1116937 : ℕ)^1 * ((6462319 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 832972004929000007)^416486002464500003 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 832972004929000007)^118996000704142858 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 8243 := Nat.prime_eq_prime_of_dvd_pow hq prime_8243 hd
          subst q
          change (5 : ZMod 832972004929000007)^101052044756642 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1116937 := Nat.prime_eq_prime_of_dvd_pow hq prime_1116937 hd
            subst q
            change (5 : ZMod 832972004929000007)^745764537238 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 6462319 := Nat.prime_eq_prime_of_dvd_pow hq prime_6462319 hd
            subst q
            change (5 : ZMod 832972004929000007)^128896763674 ≠ 1
            reduce_mod_char
            decide

theorem prime_838137706742929337 : Nat.Prime 838137706742929337 := by
  apply lucas_primality 838137706742929337 (3 : ZMod 838137706742929337)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 838137706742929337 - 1 = (2 : ℕ)^3 * ((23 : ℕ)^1 * ((229 : ℕ)^1 * ((2342657 : ℕ)^1 * ((8490893 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 838137706742929337)^419068853371464668 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (3 : ZMod 838137706742929337)^36440769858388232 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 229 := Nat.prime_eq_prime_of_dvd_pow hq prime_229 hd
          subst q
          change (3 : ZMod 838137706742929337)^3659989985776984 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2342657 := Nat.prime_eq_prime_of_dvd_pow hq prime_2342657 hd
            subst q
            change (3 : ZMod 838137706742929337)^357772267448 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 8490893 := Nat.prime_eq_prime_of_dvd_pow hq prime_8490893 hd
            subst q
            change (3 : ZMod 838137706742929337)^98710195352 ≠ 1
            reduce_mod_char
            decide

theorem prime_843330077059682339 : Nat.Prime 843330077059682339 := by
  apply lucas_primality 843330077059682339 (2 : ZMod 843330077059682339)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 843330077059682339 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((23 : ℕ)^1 * ((7699 : ℕ)^1 * ((340178920171 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 843330077059682339)^421665038529841169 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 843330077059682339)^120475725294240334 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 843330077059682339)^36666525089551406 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7699 := Nat.prime_eq_prime_of_dvd_pow hq prime_7699 hd
            subst q
            change (2 : ZMod 843330077059682339)^109537612295062 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 340178920171 := Nat.prime_eq_prime_of_dvd_pow hq prime_340178920171 hd
            subst q
            change (2 : ZMod 843330077059682339)^2479078 ≠ 1
            reduce_mod_char
            decide

theorem prime_848549225908978567 : Nat.Prime 848549225908978567 := by
  apply lucas_primality 848549225908978567 (3 : ZMod 848549225908978567)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 848549225908978567 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((15859 : ℕ)^1 * ((1273948735597 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 848549225908978567)^424274612954489283 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 848549225908978567)^282849741969659522 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 848549225908978567)^121221317986996938 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 15859 := Nat.prime_eq_prime_of_dvd_pow hq prime_15859 hd
            subst q
            change (3 : ZMod 848549225908978567)^53505846895074 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1273948735597 := Nat.prime_eq_prime_of_dvd_pow hq prime_1273948735597 hd
            subst q
            change (3 : ZMod 848549225908978567)^666078 ≠ 1
            reduce_mod_char
            decide

theorem prime_853795263660659779 : Nat.Prime 853795263660659779 := by
  apply lucas_primality 853795263660659779 (2 : ZMod 853795263660659779)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 853795263660659779 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13009 : ℕ)^1 * ((613177 : ℕ)^1 * ((17839091 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 853795263660659779)^426897631830329889 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 853795263660659779)^284598421220219926 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13009 := Nat.prime_eq_prime_of_dvd_pow hq prime_13009 hd
          subst q
          change (2 : ZMod 853795263660659779)^65631121812642 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 613177 := Nat.prime_eq_prime_of_dvd_pow hq prime_613177 hd
            subst q
            change (2 : ZMod 853795263660659779)^1392412408914 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 17839091 := Nat.prime_eq_prime_of_dvd_pow hq prime_17839091 hd
            subst q
            change (2 : ZMod 853795263660659779)^47860917558 ≠ 1
            reduce_mod_char
            decide

theorem prime_859068301025390653 : Nat.Prime 859068301025390653 := by
  apply lucas_primality 859068301025390653 (2 : ZMod 859068301025390653)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 859068301025390653 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((19 : ℕ)^1 * ((103 : ℕ)^1 * ((3067 : ℕ)^1 * ((11317 : ℕ)^1 * ((16729 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 859068301025390653)^429534150512695326 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 859068301025390653)^286356100341796884 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 859068301025390653)^122724043003627236 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (2 : ZMod 859068301025390653)^45214121106599508 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
              subst q
              change (2 : ZMod 859068301025390653)^8340468941994084 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 3067 := Nat.prime_eq_prime_of_dvd_pow hq prime_3067 hd
                subst q
                change (2 : ZMod 859068301025390653)^280100522016756 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 11317 := Nat.prime_eq_prime_of_dvd_pow hq prime_11317 hd
                  subst q
                  change (2 : ZMod 859068301025390653)^75909543255756 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 16729 := Nat.prime_eq_prime_of_dvd_pow hq prime_16729 hd
                  subst q
                  change (2 : ZMod 859068301025390653)^51352041426588 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_864368449055358997 : Nat.Prime 864368449055358997 := by
  apply lucas_primality 864368449055358997 (2 : ZMod 864368449055358997)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 864368449055358997 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((1470014369141767 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 864368449055358997)^432184224527679498 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 864368449055358997)^288122816351786332 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 864368449055358997)^123481207007908428 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1470014369141767 := Nat.prime_eq_prime_of_dvd_pow hq prime_1470014369141767 hd
          subst q
          change (2 : ZMod 864368449055358997)^588 ≠ 1
          reduce_mod_char
          decide

theorem prime_869695819144977917 : Nat.Prime 869695819144977917 := by
  apply lucas_primality 869695819144977917 (3 : ZMod 869695819144977917)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 869695819144977917 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((67 : ℕ)^1 * ((127 : ℕ)^1 * ((1879 : ℕ)^1 * ((2029 : ℕ)^1 * ((73651 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 869695819144977917)^434847909572488958 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 869695819144977917)^124242259877853988 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 869695819144977917)^66899678395767532 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
            subst q
            change (3 : ZMod 869695819144977917)^12980534614104148 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
              subst q
              change (3 : ZMod 869695819144977917)^6847998575944708 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 1879 := Nat.prime_eq_prime_of_dvd_pow hq prime_1879 hd
                subst q
                change (3 : ZMod 869695819144977917)^462850356117604 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 2029 := Nat.prime_eq_prime_of_dvd_pow hq prime_2029 hd
                  subst q
                  change (3 : ZMod 869695819144977917)^428632734916204 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 73651 := Nat.prime_eq_prime_of_dvd_pow hq prime_73651 hd
                  subst q
                  change (3 : ZMod 869695819144977917)^11808336874516 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_875050523031587921 : Nat.Prime 875050523031587921 := by
  apply lucas_primality 875050523031587921 (3 : ZMod 875050523031587921)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 875050523031587921 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((29 : ℕ)^1 * ((733 : ℕ)^1 * ((514566097657 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 875050523031587921)^437525261515793960 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 875050523031587921)^175010104606317584 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (3 : ZMod 875050523031587921)^30174155966606480 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 733 := Nat.prime_eq_prime_of_dvd_pow hq prime_733 hd
            subst q
            change (3 : ZMod 875050523031587921)^1193793346564240 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 514566097657 := Nat.prime_eq_prime_of_dvd_pow hq prime_514566097657 hd
            subst q
            change (3 : ZMod 875050523031587921)^1700560 ≠ 1
            reduce_mod_char
            decide

theorem prime_880432672796160223 : Nat.Prime 880432672796160223 := by
  apply lucas_primality 880432672796160223 (3 : ZMod 880432672796160223)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 880432672796160223 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((146738778799360037 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 880432672796160223)^440216336398080111 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 880432672796160223)^293477557598720074 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 146738778799360037 := Nat.prime_eq_prime_of_dvd_pow hq prime_146738778799360037 hd
        subst q
        change (3 : ZMod 880432672796160223)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_885842380864000019 : Nat.Prime 885842380864000019 := by
  apply lucas_primality 885842380864000019 (2 : ZMod 885842380864000019)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 885842380864000019 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((23311641601684211 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 885842380864000019)^442921190432000009 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 885842380864000019)^46623283203368422 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 23311641601684211 := Nat.prime_eq_prime_of_dvd_pow hq prime_23311641601684211 hd
        subst q
        change (2 : ZMod 885842380864000019)^38 ≠ 1
        reduce_mod_char
        decide

theorem prime_891279760005451991 : Nat.Prime 891279760005451991 := by
  apply lucas_primality 891279760005451991 (13 : ZMod 891279760005451991)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 891279760005451991 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((47 : ℕ)^1 * ((109 : ℕ)^1 * ((9437 : ℕ)^1 * ((1843553449 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 891279760005451991)^445639880002725995 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (13 : ZMod 891279760005451991)^178255952001090398 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (13 : ZMod 891279760005451991)^18963399149052170 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
            subst q
            change (13 : ZMod 891279760005451991)^8176878532160110 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 9437 := Nat.prime_eq_prime_of_dvd_pow hq prime_9437 hd
              subst q
              change (13 : ZMod 891279760005451991)^94445243192270 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1843553449 := Nat.prime_eq_prime_of_dvd_pow hq prime_1843553449 hd
              subst q
              change (13 : ZMod 891279760005451991)^483457510 ≠ 1
              reduce_mod_char
              decide

theorem prime_896744923336604273 : Nat.Prime 896744923336604273 := by
  apply lucas_primality 896744923336604273 (3 : ZMod 896744923336604273)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 896744923336604273 - 1 = (2 : ℕ)^4 * ((7 : ℕ)^1 * ((590641 : ℕ)^1 * ((13555867441 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 896744923336604273)^448372461668302136 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 896744923336604273)^128106417619514896 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 590641 := Nat.prime_eq_prime_of_dvd_pow hq prime_590641 hd
          subst q
          change (3 : ZMod 896744923336604273)^1518257153392 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13555867441 := Nat.prime_eq_prime_of_dvd_pow hq prime_13555867441 hd
          subst q
          change (3 : ZMod 896744923336604273)^66151792 ≠ 1
          reduce_mod_char
          decide

theorem prime_902237984319995599 : Nat.Prime 902237984319995599 := by
  apply lucas_primality 902237984319995599 (11 : ZMod 902237984319995599)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 902237984319995599 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((503 : ℕ)^1 * ((761 : ℕ)^1 * ((35712851641 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 902237984319995599)^451118992159997799 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 902237984319995599)^300745994773331866 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (11 : ZMod 902237984319995599)^82021634938181418 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 503 := Nat.prime_eq_prime_of_dvd_pow hq prime_503 hd
            subst q
            change (11 : ZMod 902237984319995599)^1793713686520866 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 761 := Nat.prime_eq_prime_of_dvd_pow hq prime_761 hd
              subst q
              change (11 : ZMod 902237984319995599)^1185595248777918 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 35712851641 := Nat.prime_eq_prime_of_dvd_pow hq prime_35712851641 hd
              subst q
              change (11 : ZMod 902237984319995599)^25263678 ≠ 1
              reduce_mod_char
              decide

theorem prime_907759056765321221 : Nat.Prime 907759056765321221 := by
  apply lucas_primality 907759056765321221 (2 : ZMod 907759056765321221)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 907759056765321221 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((229 : ℕ)^1 * ((6997 : ℕ)^1 * ((1666265941 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 907759056765321221)^453879528382660610 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 907759056765321221)^181551811353064244 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 907759056765321221)^53397591574430660 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 229 := Nat.prime_eq_prime_of_dvd_pow hq prime_229 hd
            subst q
            change (2 : ZMod 907759056765321221)^3964013348320180 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 6997 := Nat.prime_eq_prime_of_dvd_pow hq prime_6997 hd
              subst q
              change (2 : ZMod 907759056765321221)^129735466166260 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1666265941 := Nat.prime_eq_prime_of_dvd_pow hq prime_1666265941 hd
              subst q
              change (2 : ZMod 907759056765321221)^544786420 ≠ 1
              reduce_mod_char
              decide

theorem prime_913308254830140629 : Nat.Prime 913308254830140629 := by
  apply lucas_primality 913308254830140629 (2 : ZMod 913308254830140629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 913308254830140629 - 1 = (2 : ℕ)^2 * ((228327063707535157 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 913308254830140629)^456654127415070314 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 228327063707535157 := Nat.prime_eq_prime_of_dvd_pow hq prime_228327063707535157 hd
      subst q
      change (2 : ZMod 913308254830140629)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_918885693020585561 : Nat.Prime 918885693020585561 := by
  apply lucas_primality 918885693020585561 (3 : ZMod 918885693020585561)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 918885693020585561 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((114321269 : ℕ)^1 * ((200943731 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 918885693020585561)^459442846510292780 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 918885693020585561)^183777138604117112 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 114321269 := Nat.prime_eq_prime_of_dvd_pow hq prime_114321269 hd
          subst q
          change (3 : ZMod 918885693020585561)^8037749240 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 200943731 := Nat.prime_eq_prime_of_dvd_pow hq prime_200943731 hd
          subst q
          change (3 : ZMod 918885693020585561)^4572850760 ≠ 1
          reduce_mod_char
          decide

theorem prime_924491486192068813 : Nat.Prime 924491486192068813 := by
  apply lucas_primality 924491486192068813 (6 : ZMod 924491486192068813)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 924491486192068813 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((8500633 : ℕ)^1 * ((9062967097 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 924491486192068813)^462245743096034406 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 924491486192068813)^308163828730689604 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 8500633 := Nat.prime_eq_prime_of_dvd_pow hq prime_8500633 hd
          subst q
          change (6 : ZMod 924491486192068813)^108755605164 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 9062967097 := Nat.prime_eq_prime_of_dvd_pow hq prime_9062967097 hd
          subst q
          change (6 : ZMod 924491486192068813)^102007596 ≠ 1
          reduce_mod_char
          decide

theorem prime_930125749549993987 : Nat.Prime 930125749549993987 := by
  apply lucas_primality 930125749549993987 (2 : ZMod 930125749549993987)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 930125749549993987 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((14092814387121121 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 930125749549993987)^465062874774996993 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 930125749549993987)^310041916516664662 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 930125749549993987)^84556886322726726 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 14092814387121121 := Nat.prime_eq_prime_of_dvd_pow hq prime_14092814387121121 hd
          subst q
          change (2 : ZMod 930125749549993987)^66 ≠ 1
          reduce_mod_char
          decide

theorem prime_935788598650465589 : Nat.Prime 935788598650465589 := by
  apply lucas_primality 935788598650465589 (2 : ZMod 935788598650465589)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 935788598650465589 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((181 : ℕ)^1 * ((193 : ℕ)^1 * ((975157 : ℕ)^1 * ((981091 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 935788598650465589)^467894299325232794 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 935788598650465589)^133684085521495084 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 181 := Nat.prime_eq_prime_of_dvd_pow hq prime_181 hd
          subst q
          change (2 : ZMod 935788598650465589)^5170102754974948 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
            subst q
            change (2 : ZMod 935788598650465589)^4848645588862516 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 975157 := Nat.prime_eq_prime_of_dvd_pow hq prime_975157 hd
              subst q
              change (2 : ZMod 935788598650465589)^959628653284 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 981091 := Nat.prime_eq_prime_of_dvd_pow hq prime_981091 hd
              subst q
              change (2 : ZMod 935788598650465589)^953824465468 ≠ 1
              reduce_mod_char
              decide

theorem prime_941480149401000067 : Nat.Prime 941480149401000067 := by
  apply lucas_primality 941480149401000067 (2 : ZMod 941480149401000067)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 941480149401000067 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((1097296211423077 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 941480149401000067)^470740074700500033 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 941480149401000067)^313826716467000022 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 941480149401000067)^85589104491000006 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (2 : ZMod 941480149401000067)^72421549953923082 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1097296211423077 := Nat.prime_eq_prime_of_dvd_pow hq prime_1097296211423077 hd
            subst q
            change (2 : ZMod 941480149401000067)^858 ≠ 1
            reduce_mod_char
            decide

theorem prime_947200518061237457 : Nat.Prime 947200518061237457 := by
  apply lucas_primality 947200518061237457 (3 : ZMod 947200518061237457)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 947200518061237457 - 1 = (2 : ℕ)^4 * ((17 : ℕ)^1 * ((16189 : ℕ)^1 * ((215106235457 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 947200518061237457)^473600259030618728 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (3 : ZMod 947200518061237457)^55717677533013968 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 16189 := Nat.prime_eq_prime_of_dvd_pow hq prime_16189 hd
          subst q
          change (3 : ZMod 947200518061237457)^58508896044304 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 215106235457 := Nat.prime_eq_prime_of_dvd_pow hq prime_215106235457 hd
          subst q
          change (3 : ZMod 947200518061237457)^4403408 ≠ 1
          reduce_mod_char
          decide

theorem prime_952949821243654159 : Nat.Prime 952949821243654159 := by
  apply lucas_primality 952949821243654159 (3 : ZMod 952949821243654159)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 952949821243654159 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((85304377 : ℕ)^1 * ((1861861909 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 952949821243654159)^476474910621827079 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 952949821243654159)^317649940414551386 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 85304377 := Nat.prime_eq_prime_of_dvd_pow hq prime_85304377 hd
          subst q
          change (3 : ZMod 952949821243654159)^11171171454 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1861861909 := Nat.prime_eq_prime_of_dvd_pow hq prime_1861861909 hd
          subst q
          change (3 : ZMod 952949821243654159)^511826262 ≠ 1
          reduce_mod_char
          decide

theorem prime_958728175914275731 : Nat.Prime 958728175914275731 := by
  apply lucas_primality 958728175914275731 (2 : ZMod 958728175914275731)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 958728175914275731 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((5 : ℕ)^1 * ((7841 : ℕ)^1 * ((150952051013 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 958728175914275731)^479364087957137865 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 958728175914275731)^319576058638091910 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 958728175914275731)^191745635182855146 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7841 := Nat.prime_eq_prime_of_dvd_pow hq prime_7841 hd
            subst q
            change (2 : ZMod 958728175914275731)^122271161320530 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 150952051013 := Nat.prime_eq_prime_of_dvd_pow hq prime_150952051013 hd
            subst q
            change (2 : ZMod 958728175914275731)^6351210 ≠ 1
            reduce_mod_char
            decide

theorem prime_964535699393390723 : Nat.Prime 964535699393390723 := by
  apply lucas_primality 964535699393390723 (2 : ZMod 964535699393390723)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 964535699393390723 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((2917 : ℕ)^1 * ((12717698628641 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 964535699393390723)^482267849696695361 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 964535699393390723)^74195053799491594 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2917 := Nat.prime_eq_prime_of_dvd_pow hq prime_2917 hd
          subst q
          change (2 : ZMod 964535699393390723)^330660164344666 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 12717698628641 := Nat.prime_eq_prime_of_dvd_pow hq prime_12717698628641 hd
          subst q
          change (2 : ZMod 964535699393390723)^75842 ≠ 1
          reduce_mod_char
          decide

theorem prime_970372509356265709 : Nat.Prime 970372509356265709 := by
  apply lucas_primality 970372509356265709 (6 : ZMod 970372509356265709)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 970372509356265709 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((7993 : ℕ)^1 * ((131388302069 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 970372509356265709)^485186254678132854 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 970372509356265709)^323457503118755236 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 970372509356265709)^138624644193752244 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (6 : ZMod 970372509356265709)^88215682668751428 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 7993 := Nat.prime_eq_prime_of_dvd_pow hq prime_7993 hd
              subst q
              change (6 : ZMod 970372509356265709)^121402791111756 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 131388302069 := Nat.prime_eq_prime_of_dvd_pow hq prime_131388302069 hd
              subst q
              change (6 : ZMod 970372509356265709)^7385532 ≠ 1
              reduce_mod_char
              decide

theorem prime_976238723833860139 : Nat.Prime 976238723833860139 := by
  apply lucas_primality 976238723833860139 (2 : ZMod 976238723833860139)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 976238723833860139 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((23 : ℕ)^1 * ((43 : ℕ)^1 * ((9677419495171 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 976238723833860139)^488119361916930069 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 976238723833860139)^325412907944620046 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 976238723833860139)^57425807284344714 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (2 : ZMod 976238723833860139)^42445161905820006 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
              subst q
              change (2 : ZMod 976238723833860139)^22703226135671166 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 9677419495171 := Nat.prime_eq_prime_of_dvd_pow hq prime_9677419495171 hd
              subst q
              change (2 : ZMod 976238723833860139)^100878 ≠ 1
              reduce_mod_char
              decide

theorem prime_982134461213542783 : Nat.Prime 982134461213542783 := by
  apply lucas_primality 982134461213542783 (3 : ZMod 982134461213542783)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 982134461213542783 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5167 : ℕ)^1 * ((10559904320297 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 982134461213542783)^491067230606771391 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 982134461213542783)^327378153737847594 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5167 := Nat.prime_eq_prime_of_dvd_pow hq prime_5167 hd
          subst q
          change (3 : ZMod 982134461213542783)^190078277765346 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 10559904320297 := Nat.prime_eq_prime_of_dvd_pow hq prime_10559904320297 hd
          subst q
          change (3 : ZMod 982134461213542783)^93006 ≠ 1
          reduce_mod_char
          decide

theorem prime_988059840239808209 : Nat.Prime 988059840239808209 := by
  apply lucas_primality 988059840239808209 (3 : ZMod 988059840239808209)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 988059840239808209 - 1 = (2 : ℕ)^4 * ((5281 : ℕ)^1 * ((11693569402573 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 988059840239808209)^494029920119904104 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5281 := Nat.prime_eq_prime_of_dvd_pow hq prime_5281 hd
        subst q
        change (3 : ZMod 988059840239808209)^187097110441168 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 11693569402573 := Nat.prime_eq_prime_of_dvd_pow hq prime_11693569402573 hd
        subst q
        change (3 : ZMod 988059840239808209)^84496 ≠ 1
        reduce_mod_char
        decide

theorem prime_994014980014994029 : Nat.Prime 994014980014994029 := by
  apply lucas_primality 994014980014994029 (14 : ZMod 994014980014994029)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 994014980014994029 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((31 : ℕ)^1 * ((109 : ℕ)^2 * ((823 : ℕ)^1 * ((333667 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 994014980014994029)^497007490007497014 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 994014980014994029)^331338326671664676 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (14 : ZMod 994014980014994029)^142002140002142004 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (14 : ZMod 994014980014994029)^76462690770384156 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
              subst q
              change (14 : ZMod 994014980014994029)^32064999355322388 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
                subst q
                change (14 : ZMod 994014980014994029)^9119403486376092 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 823 := Nat.prime_eq_prime_of_dvd_pow hq prime_823 hd
                  subst q
                  change (14 : ZMod 994014980014994029)^1207794629422836 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 333667 := Nat.prime_eq_prime_of_dvd_pow hq prime_333667 hd
                  subst q
                  change (14 : ZMod 994014980014994029)^2979062898084 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_1000000000000000003 : Nat.Prime 1000000000000000003 := by
  apply lucas_primality 1000000000000000003 (2 : ZMod 1000000000000000003)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1000000000000000003 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((131 : ℕ)^1 * ((1427 : ℕ)^1 * ((52445056723 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1000000000000000003)^500000000000000001 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1000000000000000003)^333333333333333334 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 1000000000000000003)^58823529411764706 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
            subst q
            change (2 : ZMod 1000000000000000003)^7633587786259542 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1427 := Nat.prime_eq_prime_of_dvd_pow hq prime_1427 hd
              subst q
              change (2 : ZMod 1000000000000000003)^700770847932726 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 52445056723 := Nat.prime_eq_prime_of_dvd_pow hq prime_52445056723 hd
              subst q
              change (2 : ZMod 1000000000000000003)^19067574 ≠ 1
              reduce_mod_char
              decide

theorem prime_1006015020015006019 : Nat.Prime 1006015020015006019 := by
  apply lucas_primality 1006015020015006019 (2 : ZMod 1006015020015006019)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1006015020015006019 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((37501 : ℕ)^1 * ((165594764389 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1006015020015006019)^503007510007503009 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1006015020015006019)^335338340005002006 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37501 := Nat.prime_eq_prime_of_dvd_pow hq prime_37501 hd
          subst q
          change (2 : ZMod 1006015020015006019)^26826351831018 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 165594764389 := Nat.prime_eq_prime_of_dvd_pow hq prime_165594764389 hd
          subst q
          change (2 : ZMod 1006015020015006019)^6075162 ≠ 1
          reduce_mod_char
          decide

theorem prime_1012060160240192143 : Nat.Prime 1012060160240192143 := by
  apply lucas_primality 1012060160240192143 (3 : ZMod 1012060160240192143)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1012060160240192143 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((8803 : ℕ)^1 * ((53149 : ℕ)^1 * ((360519931 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1012060160240192143)^506030080120096071 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1012060160240192143)^337353386746730714 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 8803 := Nat.prime_eq_prime_of_dvd_pow hq prime_8803 hd
          subst q
          change (3 : ZMod 1012060160240192143)^114967642876314 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 53149 := Nat.prime_eq_prime_of_dvd_pow hq prime_53149 hd
            subst q
            change (3 : ZMod 1012060160240192143)^19041941715558 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 360519931 := Nat.prime_eq_prime_of_dvd_pow hq prime_360519931 hd
            subst q
            change (3 : ZMod 1012060160240192143)^2807223882 ≠ 1
            reduce_mod_char
            decide

theorem prime_1018135541216458781 : Nat.Prime 1018135541216458781 := by
  apply lucas_primality 1018135541216458781 (2 : ZMod 1018135541216458781)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1018135541216458781 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((1069 : ℕ)^1 * ((2801231335543 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1018135541216458781)^509067770608229390 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 1018135541216458781)^203627108243291756 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 1018135541216458781)^59890325953909340 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1069 := Nat.prime_eq_prime_of_dvd_pow hq prime_1069 hd
            subst q
            change (2 : ZMod 1018135541216458781)^952418654084620 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2801231335543 := Nat.prime_eq_prime_of_dvd_pow hq prime_2801231335543 hd
            subst q
            change (2 : ZMod 1018135541216458781)^363460 ≠ 1
            reduce_mod_char
            decide

theorem prime_1024241283846148157 : Nat.Prime 1024241283846148157 := by
  apply lucas_primality 1024241283846148157 (2 : ZMod 1024241283846148157)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1024241283846148157 - 1 = (2 : ℕ)^2 * ((31 : ℕ)^1 * ((139 : ℕ)^1 * ((59424534917971 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1024241283846148157)^512120641923074078 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (2 : ZMod 1024241283846148157)^33040041414391876 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
          subst q
          change (2 : ZMod 1024241283846148157)^7368642329828404 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 59424534917971 := Nat.prime_eq_prime_of_dvd_pow hq prime_59424534917971 hd
          subst q
          change (2 : ZMod 1024241283846148157)^17236 ≠ 1
          reduce_mod_char
          decide

theorem prime_1030377509393765627 : Nat.Prime 1030377509393765627 := by
  apply lucas_primality 1030377509393765627 (2 : ZMod 1030377509393765627)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1030377509393765627 - 1 = (2 : ℕ)^1 * ((37 : ℕ)^1 * ((61 : ℕ)^1 * ((229 : ℕ)^1 * ((13649 : ℕ)^1 * ((73029529 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1030377509393765627)^515188754696882813 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (2 : ZMod 1030377509393765627)^27848040794426098 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (2 : ZMod 1030377509393765627)^16891434580225666 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 229 := Nat.prime_eq_prime_of_dvd_pow hq prime_229 hd
            subst q
            change (2 : ZMod 1030377509393765627)^4499465106522994 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 13649 := Nat.prime_eq_prime_of_dvd_pow hq prime_13649 hd
              subst q
              change (2 : ZMod 1030377509393765627)^75491062304474 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 73029529 := Nat.prime_eq_prime_of_dvd_pow hq prime_73029529 hd
              subst q
              change (2 : ZMod 1030377509393765627)^14109053194 ≠ 1
              reduce_mod_char
              decide

theorem prime_1036544339486702659 : Nat.Prime 1036544339486702659 := by
  apply lucas_primality 1036544339486702659 (2 : ZMod 1036544339486702659)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1036544339486702659 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((10162199406732379 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1036544339486702659)^518272169743351329 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1036544339486702659)^345514779828900886 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 1036544339486702659)^60973196440394274 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 10162199406732379 := Nat.prime_eq_prime_of_dvd_pow hq prime_10162199406732379 hd
          subst q
          change (2 : ZMod 1036544339486702659)^102 ≠ 1
          reduce_mod_char
          decide

theorem prime_1042741896115959691 : Nat.Prime 1042741896115959691 := by
  apply lucas_primality 1042741896115959691 (2 : ZMod 1042741896115959691)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1042741896115959691 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((47 : ℕ)^1 * ((857 : ℕ)^1 * ((123276089291 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1042741896115959691)^521370948057979845 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1042741896115959691)^347580632038653230 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 1042741896115959691)^208548379223191938 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (2 : ZMod 1042741896115959691)^148963128016565670 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
              subst q
              change (2 : ZMod 1042741896115959691)^22185997789701270 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 857 := Nat.prime_eq_prime_of_dvd_pow hq prime_857 hd
                subst q
                change (2 : ZMod 1042741896115959691)^1216735001302170 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 123276089291 := Nat.prime_eq_prime_of_dvd_pow hq prime_123276089291 hd
                subst q
                change (2 : ZMod 1042741896115959691)^8458590 ≠ 1
                reduce_mod_char
                decide

theorem prime_1048970301636870157 : Nat.Prime 1048970301636870157 := by
  apply lucas_primality 1048970301636870157 (2 : ZMod 1048970301636870157)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1048970301636870157 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((29085439 : ℕ)^1 * ((3005427967 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1048970301636870157)^524485150818435078 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1048970301636870157)^349656767212290052 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29085439 := Nat.prime_eq_prime_of_dvd_pow hq prime_29085439 hd
          subst q
          change (2 : ZMod 1048970301636870157)^36065135604 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3005427967 := Nat.prime_eq_prime_of_dvd_pow hq prime_3005427967 hd
          subst q
          change (2 : ZMod 1048970301636870157)^349025268 ≠ 1
          reduce_mod_char
          decide

theorem prime_1055229678769825487 : Nat.Prime 1055229678769825487 := by
  apply lucas_primality 1055229678769825487 (5 : ZMod 1055229678769825487)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1055229678769825487 - 1 = (2 : ℕ)^1 * ((527614839384912743 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1055229678769825487)^527614839384912743 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 527614839384912743 := Nat.prime_eq_prime_of_dvd_pow hq prime_527614839384912743 hd
      subst q
      change (5 : ZMod 1055229678769825487)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_1061520150601000007 : Nat.Prime 1061520150601000007 := by
  apply lucas_primality 1061520150601000007 (7 : ZMod 1061520150601000007)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1061520150601000007 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((29 : ℕ)^1 * ((2614581651726601 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1061520150601000007)^530760075300500003 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 1061520150601000007)^151645735800142858 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (7 : ZMod 1061520150601000007)^36604143124172414 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2614581651726601 := Nat.prime_eq_prime_of_dvd_pow hq prime_2614581651726601 hd
          subst q
          change (7 : ZMod 1061520150601000007)^406 ≠ 1
          reduce_mod_char
          decide

theorem prime_1067841840583077691 : Nat.Prime 1067841840583077691 := by
  apply lucas_primality 1067841840583077691 (3 : ZMod 1067841840583077691)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1067841840583077691 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((83 : ℕ)^1 * ((2423 : ℕ)^1 * ((9941 : ℕ)^1 * ((1369559 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1067841840583077691)^533920920291538845 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1067841840583077691)^355947280194359230 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 1067841840583077691)^213568368116615538 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (3 : ZMod 1067841840583077691)^82141680044852130 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
              subst q
              change (3 : ZMod 1067841840583077691)^12865564344374430 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 2423 := Nat.prime_eq_prime_of_dvd_pow hq prime_2423 hd
                subst q
                change (3 : ZMod 1067841840583077691)^440710623435030 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 9941 := Nat.prime_eq_prime_of_dvd_pow hq prime_9941 hd
                  subst q
                  change (3 : ZMod 1067841840583077691)^107417949963090 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 1369559 := Nat.prime_eq_prime_of_dvd_pow hq prime_1369559 hd
                  subst q
                  change (3 : ZMod 1067841840583077691)^779697581910 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_1074194872535978029 : Nat.Prime 1074194872535978029 := by
  apply lucas_primality 1074194872535978029 (6 : ZMod 1074194872535978029)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1074194872535978029 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((1787 : ℕ)^1 * ((1517970517339 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 1074194872535978029)^537097436267989014 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 1074194872535978029)^358064957511992676 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (6 : ZMod 1074194872535978029)^97654079321452548 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1787 := Nat.prime_eq_prime_of_dvd_pow hq prime_1787 hd
            subst q
            change (6 : ZMod 1074194872535978029)^601116324866244 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1517970517339 := Nat.prime_eq_prime_of_dvd_pow hq prime_1517970517339 hd
            subst q
            change (6 : ZMod 1074194872535978029)^707652 ≠ 1
            reduce_mod_char
            decide

theorem prime_1080579370647584813 : Nat.Prime 1080579370647584813 := by
  apply lucas_primality 1080579370647584813 (2 : ZMod 1080579370647584813)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1080579370647584813 - 1 = (2 : ℕ)^2 * ((593702821 : ℕ)^1 * ((455016943 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1080579370647584813)^540289685323792406 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 593702821 := Nat.prime_eq_prime_of_dvd_pow hq prime_593702821 hd
        subst q
        change (2 : ZMod 1080579370647584813)^1820067772 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 455016943 := Nat.prime_eq_prime_of_dvd_pow hq prime_455016943 hd
        subst q
        change (2 : ZMod 1080579370647584813)^2374811284 ≠ 1
        reduce_mod_char
        decide

theorem prime_1086995459474473597 : Nat.Prime 1086995459474473597 := by
  apply lucas_primality 1086995459474473597 (2 : ZMod 1086995459474473597)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1086995459474473597 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((5328409115070949 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1086995459474473597)^543497729737236798 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1086995459474473597)^362331819824824532 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 1086995459474473597)^63940909380851388 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 5328409115070949 := Nat.prime_eq_prime_of_dvd_pow hq prime_5328409115070949 hd
          subst q
          change (2 : ZMod 1086995459474473597)^204 ≠ 1
          reduce_mod_char
          decide

theorem prime_1093443263942640649 : Nat.Prime 1093443263942640649 := by
  apply lucas_primality 1093443263942640649 (7 : ZMod 1093443263942640649)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1093443263942640649 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((31 : ℕ)^1 * ((5099 : ℕ)^1 * ((288229418783 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1093443263942640649)^546721631971320324 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 1093443263942640649)^364481087980880216 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (7 : ZMod 1093443263942640649)^35272363352988408 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 5099 := Nat.prime_eq_prime_of_dvd_pow hq prime_5099 hd
            subst q
            change (7 : ZMod 1093443263942640649)^214442687574552 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 288229418783 := Nat.prime_eq_prime_of_dvd_pow hq prime_288229418783 hd
            subst q
            change (7 : ZMod 1093443263942640649)^3793656 ≠ 1
            reduce_mod_char
            decide

theorem prime_1099922909348233241 : Nat.Prime 1099922909348233241 := by
  apply lucas_primality 1099922909348233241 (3 : ZMod 1099922909348233241)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1099922909348233241 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((227 : ℕ)^1 * ((51001 : ℕ)^1 * ((2375186453 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1099922909348233241)^549961454674116620 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 1099922909348233241)^219984581869646648 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 227 := Nat.prime_eq_prime_of_dvd_pow hq prime_227 hd
          subst q
          change (3 : ZMod 1099922909348233241)^4845475371578120 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 51001 := Nat.prime_eq_prime_of_dvd_pow hq prime_51001 hd
            subst q
            change (3 : ZMod 1099922909348233241)^21566692993240 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2375186453 := Nat.prime_eq_prime_of_dvd_pow hq prime_2375186453 hd
            subst q
            change (3 : ZMod 1099922909348233241)^463089080 ≠ 1
            reduce_mod_char
            decide

theorem prime_1106434521358279583 : Nat.Prime 1106434521358279583 := by
  apply lucas_primality 1106434521358279583 (5 : ZMod 1106434521358279583)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1106434521358279583 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((173 : ℕ)^1 * ((277 : ℕ)^1 * ((1649194241353 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1106434521358279583)^553217260679139791 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 1106434521358279583)^158062074479754226 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
          subst q
          change (5 : ZMod 1106434521358279583)^6395575267966934 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 277 := Nat.prime_eq_prime_of_dvd_pow hq prime_277 hd
            subst q
            change (5 : ZMod 1106434521358279583)^3994348452556966 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1649194241353 := Nat.prime_eq_prime_of_dvd_pow hq prime_1649194241353 hd
            subst q
            change (5 : ZMod 1106434521358279583)^670894 ≠ 1
            reduce_mod_char
            decide

theorem prime_1112978226011420311 : Nat.Prime 1112978226011420311 := by
  apply lucas_primality 1112978226011420311 (6 : ZMod 1112978226011420311)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1112978226011420311 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((304537 : ℕ)^1 * ((121821894221 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 1112978226011420311)^556489113005710155 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 1112978226011420311)^370992742003806770 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 1112978226011420311)^222595645202284062 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 304537 := Nat.prime_eq_prime_of_dvd_pow hq prime_304537 hd
            subst q
            change (6 : ZMod 1112978226011420311)^3654656826630 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 121821894221 := Nat.prime_eq_prime_of_dvd_pow hq prime_121821894221 hd
            subst q
            change (6 : ZMod 1112978226011420311)^9136110 ≠ 1
            reduce_mod_char
            decide

theorem prime_1119554149718639933 : Nat.Prime 1119554149718639933 := by
  apply lucas_primality 1119554149718639933 (2 : ZMod 1119554149718639933)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1119554149718639933 - 1 = (2 : ℕ)^2 * ((11 : ℕ)^1 * ((29 : ℕ)^1 * ((877393534262257 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1119554149718639933)^559777074859319966 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 1119554149718639933)^101777649974421812 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (2 : ZMod 1119554149718639933)^38605315507539308 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 877393534262257 := Nat.prime_eq_prime_of_dvd_pow hq prime_877393534262257 hd
          subst q
          change (2 : ZMod 1119554149718639933)^1276 ≠ 1
          reduce_mod_char
          decide

theorem prime_1126162419264000011 : Nat.Prime 1126162419264000011 := by
  apply lucas_primality 1126162419264000011 (2 : ZMod 1126162419264000011)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1126162419264000011 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((23 : ℕ)^1 * ((223361 : ℕ)^1 * ((21921276967 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1126162419264000011)^563081209632000005 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 1126162419264000011)^225232483852800002 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 1126162419264000011)^48963583446260870 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 223361 := Nat.prime_eq_prime_of_dvd_pow hq prime_223361 hd
            subst q
            change (2 : ZMod 1126162419264000011)^5041893702410 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 21921276967 := Nat.prime_eq_prime_of_dvd_pow hq prime_21921276967 hd
            subst q
            change (2 : ZMod 1126162419264000011)^51373030 ≠ 1
            reduce_mod_char
            decide

theorem prime_1132803161805372199 : Nat.Prime 1132803161805372199 := by
  apply lucas_primality 1132803161805372199 (3 : ZMod 1132803161805372199)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1132803161805372199 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((8329 : ℕ)^1 * ((25367 : ℕ)^1 * ((893596031 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1132803161805372199)^566401580902686099 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1132803161805372199)^377601053935124066 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 8329 := Nat.prime_eq_prime_of_dvd_pow hq prime_8329 hd
          subst q
          change (3 : ZMod 1132803161805372199)^136007103110262 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 25367 := Nat.prime_eq_prime_of_dvd_pow hq prime_25367 hd
            subst q
            change (3 : ZMod 1132803161805372199)^44656568053194 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 893596031 := Nat.prime_eq_prime_of_dvd_pow hq prime_893596031 hd
            subst q
            change (3 : ZMod 1132803161805372199)^1267690458 ≠ 1
            reduce_mod_char
            decide

theorem prime_1139476504875171949 : Nat.Prime 1139476504875171949 := by
  apply lucas_primality 1139476504875171949 (7 : ZMod 1139476504875171949)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1139476504875171949 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((71 : ℕ)^1 * ((683 : ℕ)^1 * ((652715343151 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1139476504875171949)^569738252437585974 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 1139476504875171949)^379825501625057316 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
          subst q
          change (7 : ZMod 1139476504875171949)^16048964857396788 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 683 := Nat.prime_eq_prime_of_dvd_pow hq prime_683 hd
            subst q
            change (7 : ZMod 1139476504875171949)^1668340417093956 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 652715343151 := Nat.prime_eq_prime_of_dvd_pow hq prime_652715343151 hd
            subst q
            change (7 : ZMod 1139476504875171949)^1745748 ≠ 1
            reduce_mod_char
            decide

theorem prime_1146182576381093981 : Nat.Prime 1146182576381093981 := by
  apply lucas_primality 1146182576381093981 (2 : ZMod 1146182576381093981)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1146182576381093981 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((79 : ℕ)^1 * ((599 : ℕ)^1 * ((7607 : ℕ)^1 * ((159204917 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1146182576381093981)^573091288190546990 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 1146182576381093981)^229236515276218796 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (2 : ZMod 1146182576381093981)^14508640207355620 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 599 := Nat.prime_eq_prime_of_dvd_pow hq prime_599 hd
            subst q
            change (2 : ZMod 1146182576381093981)^1913493449718020 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 7607 := Nat.prime_eq_prime_of_dvd_pow hq prime_7607 hd
              subst q
              change (2 : ZMod 1146182576381093981)^150674717547140 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 159204917 := Nat.prime_eq_prime_of_dvd_pow hq prime_159204917 hd
              subst q
              change (2 : ZMod 1146182576381093981)^7199416940 ≠ 1
              reduce_mod_char
              decide

theorem prime_1152921504606847009 : Nat.Prime 1152921504606847009 := by
  apply lucas_primality 1152921504606847009 (13 : ZMod 1152921504606847009)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1152921504606847009 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((11 : ℕ)^2 * ((683 : ℕ)^1 * ((2971 : ℕ)^1 * ((48912491 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 1152921504606847009)^576460752303423504 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (13 : ZMod 1152921504606847009)^384307168202282336 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (13 : ZMod 1152921504606847009)^104811045873349728 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 683 := Nat.prime_eq_prime_of_dvd_pow hq prime_683 hd
            subst q
            change (13 : ZMod 1152921504606847009)^1688025628999776 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 2971 := Nat.prime_eq_prime_of_dvd_pow hq prime_2971 hd
              subst q
              change (13 : ZMod 1152921504606847009)^388058399396448 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 48912491 := Nat.prime_eq_prime_of_dvd_pow hq prime_48912491 hd
              subst q
              change (13 : ZMod 1152921504606847009)^23571105888 ≠ 1
              reduce_mod_char
              decide

theorem prime_1159693418212890653 : Nat.Prime 1159693418212890653 := by
  apply lucas_primality 1159693418212890653 (3 : ZMod 1159693418212890653)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1159693418212890653 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((61 : ℕ)^1 * ((109 : ℕ)^1 * ((1321 : ℕ)^1 * ((1381 : ℕ)^1 * ((262657 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1159693418212890653)^579846709106445326 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 1159693418212890653)^165670488316127236 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 1159693418212890653)^89207186016376204 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
            subst q
            change (3 : ZMod 1159693418212890653)^19011367511686732 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
              subst q
              change (3 : ZMod 1159693418212890653)^10639389157916428 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 1321 := Nat.prime_eq_prime_of_dvd_pow hq prime_1321 hd
                subst q
                change (3 : ZMod 1159693418212890653)^877890551258812 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 1381 := Nat.prime_eq_prime_of_dvd_pow hq prime_1381 hd
                  subst q
                  change (3 : ZMod 1159693418212890653)^839749035635692 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 262657 := Nat.prime_eq_prime_of_dvd_pow hq prime_262657 hd
                  subst q
                  change (3 : ZMod 1159693418212890653)^4415238955036 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_1166498446237171799 : Nat.Prime 1166498446237171799 := by
  apply lucas_primality 1166498446237171799 (13 : ZMod 1166498446237171799)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1166498446237171799 - 1 = (2 : ℕ)^1 * ((47 : ℕ)^1 * ((12409557938693317 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 1166498446237171799)^583249223118585899 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (13 : ZMod 1166498446237171799)^24819115877386634 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 12409557938693317 := Nat.prime_eq_prime_of_dvd_pow hq prime_12409557938693317 hd
        subst q
        change (13 : ZMod 1166498446237171799)^94 ≠ 1
        reduce_mod_char
        decide

theorem prime_1173336718095862631 : Nat.Prime 1173336718095862631 := by
  apply lucas_primality 1173336718095862631 (11 : ZMod 1173336718095862631)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1173336718095862631 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((41 : ℕ)^1 * ((139943 : ℕ)^1 * ((20449732201 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 1173336718095862631)^586668359047931315 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 1173336718095862631)^234667343619172526 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (11 : ZMod 1173336718095862631)^28617968734045430 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 139943 := Nat.prime_eq_prime_of_dvd_pow hq prime_139943 hd
            subst q
            change (11 : ZMod 1173336718095862631)^8384390202410 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 20449732201 := Nat.prime_eq_prime_of_dvd_pow hq prime_20449732201 hd
            subst q
            change (11 : ZMod 1173336718095862631)^57376630 ≠ 1
            reduce_mod_char
            decide

theorem prime_1180208363584098311 : Nat.Prime 1180208363584098311 := by
  apply lucas_primality 1180208363584098311 (7 : ZMod 1180208363584098311)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1180208363584098311 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((1532738134524803 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1180208363584098311)^590104181792049155 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 1180208363584098311)^236041672716819662 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 1180208363584098311)^168601194797728330 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (7 : ZMod 1180208363584098311)^107291669416736210 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1532738134524803 := Nat.prime_eq_prime_of_dvd_pow hq prime_1532738134524803 hd
            subst q
            change (7 : ZMod 1180208363584098311)^770 ≠ 1
            reduce_mod_char
            decide

theorem prime_1187113512876717331 : Nat.Prime 1187113512876717331 := by
  apply lucas_primality 1187113512876717331 (2 : ZMod 1187113512876717331)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1187113512876717331 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((193 : ℕ)^1 * ((68342746855309 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1187113512876717331)^593556756438358665 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1187113512876717331)^395704504292239110 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 1187113512876717331)^237422702575343466 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
            subst q
            change (2 : ZMod 1187113512876717331)^6150847216977810 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 68342746855309 := Nat.prime_eq_prime_of_dvd_pow hq prime_68342746855309 hd
            subst q
            change (2 : ZMod 1187113512876717331)^17370 ≠ 1
            reduce_mod_char
            decide

theorem prime_1194052296529000003 : Nat.Prime 1194052296529000003 := by
  apply lucas_primality 1194052296529000003 (2 : ZMod 1194052296529000003)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1194052296529000003 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((59 : ℕ)^1 * ((3373029086240113 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1194052296529000003)^597026148264500001 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1194052296529000003)^398017432176333334 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (2 : ZMod 1194052296529000003)^20238174517440678 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3373029086240113 := Nat.prime_eq_prime_of_dvd_pow hq prime_3373029086240113 hd
          subst q
          change (2 : ZMod 1194052296529000003)^354 ≠ 1
          reduce_mod_char
          decide

theorem prime_1201024845477409747 : Nat.Prime 1201024845477409747 := by
  apply lucas_primality 1201024845477409747 (7 : ZMod 1201024845477409747)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1201024845477409747 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((576341 : ℕ)^1 * ((803867 : ℕ)^1 * ((432053 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1201024845477409747)^600512422738704873 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 1201024845477409747)^400341615159136582 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 576341 := Nat.prime_eq_prime_of_dvd_pow hq prime_576341 hd
          subst q
          change (7 : ZMod 1201024845477409747)^2083878893706 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 803867 := Nat.prime_eq_prime_of_dvd_pow hq prime_803867 hd
            subst q
            change (7 : ZMod 1201024845477409747)^1494059148438 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 432053 := Nat.prime_eq_prime_of_dvd_pow hq prime_432053 hd
            subst q
            change (7 : ZMod 1201024845477409747)^2779809063882 ≠ 1
            reduce_mod_char
            decide

theorem prime_1208031291040334027 : Nat.Prime 1208031291040334027 := by
  apply lucas_primality 1208031291040334027 (2 : ZMod 1208031291040334027)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1208031291040334027 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^2 * ((17 : ℕ)^1 * ((8329 : ℕ)^1 * ((87058328509 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1208031291040334027)^604015645520167013 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 1208031291040334027)^172575898720047718 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 1208031291040334027)^71060664178843178 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 8329 := Nat.prime_eq_prime_of_dvd_pow hq prime_8329 hd
            subst q
            change (2 : ZMod 1208031291040334027)^145039175295994 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 87058328509 := Nat.prime_eq_prime_of_dvd_pow hq prime_87058328509 hd
            subst q
            change (2 : ZMod 1208031291040334027)^13876114 ≠ 1
            reduce_mod_char
            decide

theorem prime_1215071764918825973 : Nat.Prime 1215071764918825973 := by
  apply lucas_primality 1215071764918825973 (2 : ZMod 1215071764918825973)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1215071764918825973 - 1 = (2 : ℕ)^2 * ((73 : ℕ)^1 * ((100609 : ℕ)^1 * ((41360163349 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1215071764918825973)^607535882459412986 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
        subst q
        change (2 : ZMod 1215071764918825973)^16644818697518164 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 100609 := Nat.prime_eq_prime_of_dvd_pow hq prime_100609 hd
          subst q
          change (2 : ZMod 1215071764918825973)^12077167697908 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 41360163349 := Nat.prime_eq_prime_of_dvd_pow hq prime_41360163349 hd
          subst q
          change (2 : ZMod 1215071764918825973)^29377828 ≠ 1
          reduce_mod_char
          decide

theorem prime_1222146399197348431 : Nat.Prime 1222146399197348431 := by
  apply lucas_primality 1222146399197348431 (3 : ZMod 1222146399197348431)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1222146399197348431 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((3133708715890637 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1222146399197348431)^611073199598674215 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1222146399197348431)^407382133065782810 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 1222146399197348431)^244429279839469686 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (3 : ZMod 1222146399197348431)^94011261476719110 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3133708715890637 := Nat.prime_eq_prime_of_dvd_pow hq prime_3133708715890637 hd
            subst q
            change (3 : ZMod 1222146399197348431)^390 ≠ 1
            reduce_mod_char
            decide

theorem prime_1229255326344515749 : Nat.Prime 1229255326344515749 := by
  apply lucas_primality 1229255326344515749 (2 : ZMod 1229255326344515749)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1229255326344515749 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((853 : ℕ)^1 * ((31337 : ℕ)^1 * ((225426767 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1229255326344515749)^614627663172257874 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1229255326344515749)^409751775448171916 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 1229255326344515749)^72309136843795044 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 853 := Nat.prime_eq_prime_of_dvd_pow hq prime_853 hd
            subst q
            change (2 : ZMod 1229255326344515749)^1441096513885716 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 31337 := Nat.prime_eq_prime_of_dvd_pow hq prime_31337 hd
              subst q
              change (2 : ZMod 1229255326344515749)^39226962579204 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 225426767 := Nat.prime_eq_prime_of_dvd_pow hq prime_225426767 hd
              subst q
              change (2 : ZMod 1229255326344515749)^5453014044 ≠ 1
              reduce_mod_char
              decide

theorem prime_1236398679213838367 : Nat.Prime 1236398679213838367 := by
  apply lucas_primality 1236398679213838367 (5 : ZMod 1236398679213838367)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1236398679213838367 - 1 = (2 : ℕ)^1 * ((47 : ℕ)^1 * ((131 : ℕ)^1 * ((100405934644619 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1236398679213838367)^618199339606919183 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (5 : ZMod 1236398679213838367)^26306354876890178 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
          subst q
          change (5 : ZMod 1236398679213838367)^9438157856594186 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 100405934644619 := Nat.prime_eq_prime_of_dvd_pow hq prime_100405934644619 hd
          subst q
          change (5 : ZMod 1236398679213838367)^12314 ≠ 1
          reduce_mod_char
          decide

theorem prime_1243576591044468431 : Nat.Prime 1243576591044468431 := by
  apply lucas_primality 1243576591044468431 (7 : ZMod 1243576591044468431)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1243576591044468431 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((124357659104446843 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1243576591044468431)^621788295522234215 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 1243576591044468431)^248715318208893686 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 124357659104446843 := Nat.prime_eq_prime_of_dvd_pow hq prime_124357659104446843 hd
        subst q
        change (7 : ZMod 1243576591044468431)^10 ≠ 1
        reduce_mod_char
        decide

theorem prime_1250789195461944407 : Nat.Prime 1250789195461944407 := by
  apply lucas_primality 1250789195461944407 (5 : ZMod 1250789195461944407)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1250789195461944407 - 1 = (2 : ℕ)^1 * ((625394597730972203 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1250789195461944407)^625394597730972203 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 625394597730972203 := Nat.prime_eq_prime_of_dvd_pow hq prime_625394597730972203 hd
      subst q
      change (5 : ZMod 1250789195461944407)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_1258036626478937813 : Nat.Prime 1258036626478937813 := by
  apply lucas_primality 1258036626478937813 (2 : ZMod 1258036626478937813)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1258036626478937813 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((79349 : ℕ)^1 * ((304893723269 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1258036626478937813)^629018313239468906 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 1258036626478937813)^96772048190687524 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 79349 := Nat.prime_eq_prime_of_dvd_pow hq prime_79349 hd
          subst q
          change (2 : ZMod 1258036626478937813)^15854473609988 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 304893723269 := Nat.prime_eq_prime_of_dvd_pow hq prime_304893723269 hd
          subst q
          change (2 : ZMod 1258036626478937813)^4126148 ≠ 1
          reduce_mod_char
          decide

theorem prime_1265319018496000037 : Nat.Prime 1265319018496000037 := by
  apply lucas_primality 1265319018496000037 (2 : ZMod 1265319018496000037)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1265319018496000037 - 1 = (2 : ℕ)^2 * ((17 : ℕ)^1 * ((41 : ℕ)^1 * ((16253 : ℕ)^1 * ((24197 : ℕ)^1 * ((1154017 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1265319018496000037)^632659509248000018 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 1265319018496000037)^74430530499764708 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (2 : ZMod 1265319018496000037)^30861439475512196 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 16253 := Nat.prime_eq_prime_of_dvd_pow hq prime_16253 hd
            subst q
            change (2 : ZMod 1265319018496000037)^77851413185012 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 24197 := Nat.prime_eq_prime_of_dvd_pow hq prime_24197 hd
              subst q
              change (2 : ZMod 1265319018496000037)^52292392383188 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1154017 := Nat.prime_eq_prime_of_dvd_pow hq prime_1154017 hd
              subst q
              change (2 : ZMod 1265319018496000037)^1096447468708 ≠ 1
              reduce_mod_char
              decide

theorem prime_1272636506302310251 : Nat.Prime 1272636506302310251 := by
  apply lucas_primality 1272636506302310251 (2 : ZMod 1272636506302310251)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1272636506302310251 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((5 : ℕ)^3 * ((565616225023249 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1272636506302310251)^636318253151155125 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1272636506302310251)^424212168767436750 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 1272636506302310251)^254527301260462050 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 565616225023249 := Nat.prime_eq_prime_of_dvd_pow hq prime_565616225023249 hd
          subst q
          change (2 : ZMod 1272636506302310251)^2250 ≠ 1
          reduce_mod_char
          decide

theorem prime_1279989225076423831 : Nat.Prime 1279989225076423831 := by
  apply lucas_primality 1279989225076423831 (7 : ZMod 1279989225076423831)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1279989225076423831 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((271 : ℕ)^1 * ((1187 : ℕ)^1 * ((3253 : ℕ)^1 * ((40773781 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1279989225076423831)^639994612538211915 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 1279989225076423831)^426663075025474610 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 1279989225076423831)^255997845015284766 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 271 := Nat.prime_eq_prime_of_dvd_pow hq prime_271 hd
            subst q
            change (7 : ZMod 1279989225076423831)^4723207472606730 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1187 := Nat.prime_eq_prime_of_dvd_pow hq prime_1187 hd
              subst q
              change (7 : ZMod 1279989225076423831)^1078339700991090 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 3253 := Nat.prime_eq_prime_of_dvd_pow hq prime_3253 hd
                subst q
                change (7 : ZMod 1279989225076423831)^393479626522110 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 40773781 := Nat.prime_eq_prime_of_dvd_pow hq prime_40773781 hd
                subst q
                change (7 : ZMod 1279989225076423831)^31392458430 ≠ 1
                reduce_mod_char
                decide

theorem prime_1287377310387021083 : Nat.Prime 1287377310387021083 := by
  apply lucas_primality 1287377310387021083 (2 : ZMod 1287377310387021083)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1287377310387021083 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((6659 : ℕ)^1 * ((620029 : ℕ)^1 * ((6778397 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1287377310387021083)^643688655193510541 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (2 : ZMod 1287377310387021083)^55972926538566134 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 6659 := Nat.prime_eq_prime_of_dvd_pow hq prime_6659 hd
          subst q
          change (2 : ZMod 1287377310387021083)^193328924821598 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 620029 := Nat.prime_eq_prime_of_dvd_pow hq prime_620029 hd
            subst q
            change (2 : ZMod 1287377310387021083)^2076317898658 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 6778397 := Nat.prime_eq_prime_of_dvd_pow hq prime_6778397 hd
            subst q
            change (2 : ZMod 1287377310387021083)^189923563106 ≠ 1
            reduce_mod_char
            decide

theorem prime_1294800898193657887 : Nat.Prime 1294800898193657887 := by
  apply lucas_primality 1294800898193657887 (3 : ZMod 1294800898193657887)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1294800898193657887 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((176819 : ℕ)^1 * ((1220457924199 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1294800898193657887)^647400449096828943 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1294800898193657887)^431600299397885962 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 176819 := Nat.prime_eq_prime_of_dvd_pow hq prime_176819 hd
          subst q
          change (3 : ZMod 1294800898193657887)^7322747545194 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1220457924199 := Nat.prime_eq_prime_of_dvd_pow hq prime_1220457924199 hd
          subst q
          change (3 : ZMod 1294800898193657887)^1060914 ≠ 1
          reduce_mod_char
          decide

theorem prime_1302260124847515643 : Nat.Prime 1302260124847515643 := by
  apply lucas_primality 1302260124847515643 (17 : ZMod 1302260124847515643)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1302260124847515643 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((23 : ℕ)^1 * ((51749 : ℕ)^1 * ((63131 : ℕ)^1 * ((962837 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 1302260124847515643)^651130062423757821 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 1302260124847515643)^434086708282505214 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (17 : ZMod 1302260124847515643)^56620005428152854 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 51749 := Nat.prime_eq_prime_of_dvd_pow hq prime_51749 hd
            subst q
            change (17 : ZMod 1302260124847515643)^25164933135858 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 63131 := Nat.prime_eq_prime_of_dvd_pow hq prime_63131 hd
              subst q
              change (17 : ZMod 1302260124847515643)^20627902691982 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 962837 := Nat.prime_eq_prime_of_dvd_pow hq prime_962837 hd
              subst q
              change (17 : ZMod 1302260124847515643)^1352523973266 ≠ 1
              reduce_mod_char
              decide

theorem prime_1309755127092152899 : Nat.Prime 1309755127092152899 := by
  apply lucas_primality 1309755127092152899 (2 : ZMod 1309755127092152899)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1309755127092152899 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1072129 : ℕ)^1 * ((203606582027 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1309755127092152899)^654877563546076449 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1309755127092152899)^436585042364050966 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1072129 := Nat.prime_eq_prime_of_dvd_pow hq prime_1072129 hd
          subst q
          change (2 : ZMod 1309755127092152899)^1221639492162 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 203606582027 := Nat.prime_eq_prime_of_dvd_pow hq prime_203606582027 hd
          subst q
          change (2 : ZMod 1309755127092152899)^6432774 ≠ 1
          reduce_mod_char
          decide

theorem prime_1317286042064257339 : Nat.Prime 1317286042064257339 := by
  apply lucas_primality 1317286042064257339 (2 : ZMod 1317286042064257339)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1317286042064257339 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((197 : ℕ)^1 * ((577 : ℕ)^1 * ((643821603889 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1317286042064257339)^658643021032128669 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1317286042064257339)^439095347354752446 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 197 := Nat.prime_eq_prime_of_dvd_pow hq prime_197 hd
          subst q
          change (2 : ZMod 1317286042064257339)^6686731177991154 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 577 := Nat.prime_eq_prime_of_dvd_pow hq prime_577 hd
            subst q
            change (2 : ZMod 1317286042064257339)^2282991407390394 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 643821603889 := Nat.prime_eq_prime_of_dvd_pow hq prime_643821603889 hd
            subst q
            change (2 : ZMod 1317286042064257339)^2046042 ≠ 1
            reduce_mod_char
            decide

theorem prime_1324853007294398513 : Nat.Prime 1324853007294398513 := by
  apply lucas_primality 1324853007294398513 (3 : ZMod 1324853007294398513)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1324853007294398513 - 1 = (2 : ℕ)^4 * ((7 : ℕ)^2 * ((631 : ℕ)^1 * ((643 : ℕ)^1 * ((5737 : ℕ)^1 * ((725983 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1324853007294398513)^662426503647199256 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 1324853007294398513)^189264715327771216 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 631 := Nat.prime_eq_prime_of_dvd_pow hq prime_631 hd
          subst q
          change (3 : ZMod 1324853007294398513)^2099608569404752 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 643 := Nat.prime_eq_prime_of_dvd_pow hq prime_643 hd
            subst q
            change (3 : ZMod 1324853007294398513)^2060424583661584 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 5737 := Nat.prime_eq_prime_of_dvd_pow hq prime_5737 hd
              subst q
              change (3 : ZMod 1324853007294398513)^230931324262576 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 725983 := Nat.prime_eq_prime_of_dvd_pow hq prime_725983 hd
              subst q
              change (3 : ZMod 1324853007294398513)^1824909133264 ≠ 1
              reduce_mod_char
              decide

theorem prime_1332456160707781217 : Nat.Prime 1332456160707781217 := by
  apply lucas_primality 1332456160707781217 (3 : ZMod 1332456160707781217)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1332456160707781217 - 1 = (2 : ℕ)^5 * ((17 : ℕ)^1 * ((2449367942477539 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1332456160707781217)^666228080353890608 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (3 : ZMod 1332456160707781217)^78379774159281248 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2449367942477539 := Nat.prime_eq_prime_of_dvd_pow hq prime_2449367942477539 hd
        subst q
        change (3 : ZMod 1332456160707781217)^544 ≠ 1
        reduce_mod_char
        decide

theorem prime_1340095640625000013 : Nat.Prime 1340095640625000013 := by
  apply lucas_primality 1340095640625000013 (5 : ZMod 1340095640625000013)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1340095640625000013 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((19 : ℕ)^1 * ((6691 : ℕ)^1 * ((67571967613 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1340095640625000013)^670047820312500006 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1340095640625000013)^446698546875000004 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (5 : ZMod 1340095640625000013)^103084280048076924 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (5 : ZMod 1340095640625000013)^70531349506578948 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 6691 := Nat.prime_eq_prime_of_dvd_pow hq prime_6691 hd
              subst q
              change (5 : ZMod 1340095640625000013)^200283312004932 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 67571967613 := Nat.prime_eq_prime_of_dvd_pow hq prime_67571967613 hd
              subst q
              change (5 : ZMod 1340095640625000013)^19832124 ≠ 1
              reduce_mod_char
              decide

theorem prime_1347771585762793813 : Nat.Prime 1347771585762793813 := by
  apply lucas_primality 1347771585762793813 (2 : ZMod 1347771585762793813)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1347771585762793813 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((137 : ℕ)^1 * ((819812400099023 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1347771585762793813)^673885792881396906 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1347771585762793813)^449257195254264604 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
          subst q
          change (2 : ZMod 1347771585762793813)^9837748801188276 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 819812400099023 := Nat.prime_eq_prime_of_dvd_pow hq prime_819812400099023 hd
          subst q
          change (2 : ZMod 1347771585762793813)^1644 ≠ 1
          reduce_mod_char
          decide

theorem prime_1355484135234801707 : Nat.Prime 1355484135234801707 := by
  apply lucas_primality 1355484135234801707 (2 : ZMod 1355484135234801707)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1355484135234801707 - 1 = (2 : ℕ)^1 * ((149 : ℕ)^1 * ((33769 : ℕ)^1 * ((134697636313 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1355484135234801707)^677742067617400853 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
        subst q
        change (2 : ZMod 1355484135234801707)^9097208961307394 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 33769 := Nat.prime_eq_prime_of_dvd_pow hq prime_33769 hd
          subst q
          change (2 : ZMod 1355484135234801707)^40139895621274 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 134697636313 := Nat.prime_eq_prime_of_dvd_pow hq prime_134697636313 hd
          subst q
          change (2 : ZMod 1355484135234801707)^10063162 ≠ 1
          reduce_mod_char
          decide

theorem prime_1363233428552319143 : Nat.Prime 1363233428552319143 := by
  apply lucas_primality 1363233428552319143 (5 : ZMod 1363233428552319143)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1363233428552319143 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^2 * ((13 : ℕ)^1 * ((29 : ℕ)^1 * ((3082889 : ℕ)^1 * ((11968643 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1363233428552319143)^681616714276159571 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 1363233428552319143)^194747632650331306 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (5 : ZMod 1363233428552319143)^104864109888639934 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (5 : ZMod 1363233428552319143)^47008049260424798 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 3082889 := Nat.prime_eq_prime_of_dvd_pow hq prime_3082889 hd
              subst q
              change (5 : ZMod 1363233428552319143)^442193484278 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 11968643 := Nat.prime_eq_prime_of_dvd_pow hq prime_11968643 hd
              subst q
              change (5 : ZMod 1363233428552319143)^113900416994 ≠ 1
              reduce_mod_char
              decide

theorem prime_1371019605625055339 : Nat.Prime 1371019605625055339 := by
  apply lucas_primality 1371019605625055339 (2 : ZMod 1371019605625055339)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1371019605625055339 - 1 = (2 : ℕ)^1 * ((89 : ℕ)^1 * ((1193 : ℕ)^1 * ((3581 : ℕ)^1 * ((1802930137 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1371019605625055339)^685509802812527669 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
        subst q
        change (2 : ZMod 1371019605625055339)^15404714669944442 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1193 := Nat.prime_eq_prime_of_dvd_pow hq prime_1193 hd
          subst q
          change (2 : ZMod 1371019605625055339)^1149220122066266 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3581 := Nat.prime_eq_prime_of_dvd_pow hq prime_3581 hd
            subst q
            change (2 : ZMod 1371019605625055339)^382859426312498 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1802930137 := Nat.prime_eq_prime_of_dvd_pow hq prime_1802930137 hd
            subst q
            change (2 : ZMod 1371019605625055339)^760439674 ≠ 1
            reduce_mod_char
            decide

theorem prime_1378842806761890643 : Nat.Prime 1378842806761890643 := by
  apply lucas_primality 1378842806761890643 (2 : ZMod 1378842806761890643)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1378842806761890643 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((89 : ℕ)^1 * ((347 : ℕ)^1 * ((259771 : ℕ)^1 * ((1060937 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1378842806761890643)^689421403380945321 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1378842806761890643)^459614268920630214 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 89 := Nat.prime_eq_prime_of_dvd_pow hq prime_89 hd
          subst q
          change (2 : ZMod 1378842806761890643)^15492615806313378 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 347 := Nat.prime_eq_prime_of_dvd_pow hq prime_347 hd
            subst q
            change (2 : ZMod 1378842806761890643)^3973610394126486 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 259771 := Nat.prime_eq_prime_of_dvd_pow hq prime_259771 hd
              subst q
              change (2 : ZMod 1378842806761890643)^5307916614102 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1060937 := Nat.prime_eq_prime_of_dvd_pow hq prime_1060937 hd
              subst q
              change (2 : ZMod 1378842806761890643)^1299646262466 ≠ 1
              reduce_mod_char
              decide

theorem prime_1386703172671635479 : Nat.Prime 1386703172671635479 := by
  apply lucas_primality 1386703172671635479 (11 : ZMod 1386703172671635479)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1386703172671635479 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((39662933 : ℕ)^1 * ((1589190653 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 1386703172671635479)^693351586335817739 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (11 : ZMod 1386703172671635479)^126063924788330498 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 39662933 := Nat.prime_eq_prime_of_dvd_pow hq prime_39662933 hd
          subst q
          change (11 : ZMod 1386703172671635479)^34962194366 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1589190653 := Nat.prime_eq_prime_of_dvd_pow hq prime_1589190653 hd
          subst q
          change (11 : ZMod 1386703172671635479)^872584526 ≠ 1
          reduce_mod_char
          decide

theorem prime_1394600844463789253 : Nat.Prime 1394600844463789253 := by
  apply lucas_primality 1394600844463789253 (2 : ZMod 1394600844463789253)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1394600844463789253 - 1 = (2 : ℕ)^2 * ((103 : ℕ)^1 * ((226141 : ℕ)^1 * ((14968331731 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1394600844463789253)^697300422231894626 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
        subst q
        change (2 : ZMod 1394600844463789253)^13539814023920284 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 226141 := Nat.prime_eq_prime_of_dvd_pow hq prime_226141 hd
          subst q
          change (2 : ZMod 1394600844463789253)^6166952673172 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 14968331731 := Nat.prime_eq_prime_of_dvd_pow hq prime_14968331731 hd
          subst q
          change (2 : ZMod 1394600844463789253)^93170092 ≠ 1
          reduce_mod_char
          decide

theorem prime_1402535963649300589 : Nat.Prime 1402535963649300589 := by
  apply lucas_primality 1402535963649300589 (2 : ZMod 1402535963649300589)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1402535963649300589 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((195089 : ℕ)^1 * ((199700302547 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1402535963649300589)^701267981824650294 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1402535963649300589)^467511987883100196 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 195089 := Nat.prime_eq_prime_of_dvd_pow hq prime_195089 hd
          subst q
          change (2 : ZMod 1402535963649300589)^7189210891692 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 199700302547 := Nat.prime_eq_prime_of_dvd_pow hq prime_199700302547 hd
          subst q
          change (2 : ZMod 1402535963649300589)^7023204 ≠ 1
          reduce_mod_char
          decide

theorem prime_1410508672141327643 : Nat.Prime 1410508672141327643 := by
  apply lucas_primality 1410508672141327643 (2 : ZMod 1410508672141327643)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1410508672141327643 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((37 : ℕ)^1 * ((137 : ℕ)^1 * ((4093 : ℕ)^1 * ((4153 : ℕ)^1 * ((629617 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1410508672141327643)^705254336070663821 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 1410508672141327643)^108500667087794434 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (2 : ZMod 1410508672141327643)^38121856003819666 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
            subst q
            change (2 : ZMod 1410508672141327643)^10295683738257866 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 4093 := Nat.prime_eq_prime_of_dvd_pow hq prime_4093 hd
              subst q
              change (2 : ZMod 1410508672141327643)^344614872255394 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 4153 := Nat.prime_eq_prime_of_dvd_pow hq prime_4153 hd
                subst q
                change (2 : ZMod 1410508672141327643)^339636087681514 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 629617 := Nat.prime_eq_prime_of_dvd_pow hq prime_629617 hd
                subst q
                change (2 : ZMod 1410508672141327643)^2240264592826 ≠ 1
                reduce_mod_char
                decide

theorem prime_1418519112256000033 : Nat.Prime 1418519112256000033 := by
  apply lucas_primality 1418519112256000033 (7 : ZMod 1418519112256000033)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1418519112256000033 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((43 : ℕ)^1 * ((347 : ℕ)^1 * ((990298287827 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1418519112256000033)^709259556128000016 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 1418519112256000033)^472839704085333344 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (7 : ZMod 1418519112256000033)^32988816564093024 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 347 := Nat.prime_eq_prime_of_dvd_pow hq prime_347 hd
            subst q
            change (7 : ZMod 1418519112256000033)^4087951332149856 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 990298287827 := Nat.prime_eq_prime_of_dvd_pow hq prime_990298287827 hd
            subst q
            change (7 : ZMod 1418519112256000033)^1432416 ≠ 1
            reduce_mod_char
            decide

theorem prime_1426567426713180379 : Nat.Prime 1426567426713180379 := by
  apply lucas_primality 1426567426713180379 (2 : ZMod 1426567426713180379)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1426567426713180379 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((11 : ℕ)^1 * ((131 : ℕ)^1 * ((1286629 : ℕ)^1 * ((42746689 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1426567426713180379)^713283713356590189 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1426567426713180379)^475522475571060126 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 1426567426713180379)^129687947883016398 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
            subst q
            change (2 : ZMod 1426567426713180379)^10889827684833438 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1286629 := Nat.prime_eq_prime_of_dvd_pow hq prime_1286629 hd
              subst q
              change (2 : ZMod 1426567426713180379)^1108763619282 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 42746689 := Nat.prime_eq_prime_of_dvd_pow hq prime_42746689 hd
              subst q
              change (2 : ZMod 1426567426713180379)^33372583002 ≠ 1
              reduce_mod_char
              decide

theorem prime_1434653758637227819 : Nat.Prime 1434653758637227819 := by
  apply lucas_primality 1434653758637227819 (2 : ZMod 1434653758637227819)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1434653758637227819 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((17 : ℕ)^1 * ((1877 : ℕ)^1 * ((2497821510889 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1434653758637227819)^717326879318613909 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1434653758637227819)^478217919545742606 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 1434653758637227819)^84391397566895754 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1877 := Nat.prime_eq_prime_of_dvd_pow hq prime_1877 hd
            subst q
            change (2 : ZMod 1434653758637227819)^764333382332034 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2497821510889 := Nat.prime_eq_prime_of_dvd_pow hq prime_2497821510889 hd
            subst q
            change (2 : ZMod 1434653758637227819)^574362 ≠ 1
            reduce_mod_char
            decide

theorem prime_1442778251557760233 : Nat.Prime 1442778251557760233 := by
  apply lucas_primality 1442778251557760233 (10 : ZMod 1442778251557760233)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1442778251557760233 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((31 : ℕ)^1 * ((463 : ℕ)^1 * ((4188375982831 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 1442778251557760233)^721389125778880116 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 1442778251557760233)^480926083852586744 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (10 : ZMod 1442778251557760233)^46541233921218072 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 463 := Nat.prime_eq_prime_of_dvd_pow hq prime_463 hd
            subst q
            change (10 : ZMod 1442778251557760233)^3116151731226264 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 4188375982831 := Nat.prime_eq_prime_of_dvd_pow hq prime_4188375982831 hd
            subst q
            change (10 : ZMod 1442778251557760233)^344472 ≠ 1
            reduce_mod_char
            decide

theorem prime_1450941049410420857 : Nat.Prime 1450941049410420857 := by
  apply lucas_primality 1450941049410420857 (3 : ZMod 1450941049410420857)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1450941049410420857 - 1 = (2 : ℕ)^3 * ((79 : ℕ)^1 * ((2295792799700033 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1450941049410420857)^725470524705210428 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
        subst q
        change (3 : ZMod 1450941049410420857)^18366342397600264 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2295792799700033 := Nat.prime_eq_prime_of_dvd_pow hq prime_2295792799700033 hd
        subst q
        change (3 : ZMod 1450941049410420857)^632 ≠ 1
        reduce_mod_char
        decide

theorem prime_1459142296537640639 : Nat.Prime 1459142296537640639 := by
  apply lucas_primality 1459142296537640639 (7 : ZMod 1459142296537640639)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1459142296537640639 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((15149 : ℕ)^1 * ((625450523303 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1459142296537640639)^729571148268820319 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (7 : ZMod 1459142296537640639)^208448899505377234 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (7 : ZMod 1459142296537640639)^132649299685240058 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 15149 := Nat.prime_eq_prime_of_dvd_pow hq prime_15149 hd
            subst q
            change (7 : ZMod 1459142296537640639)^96319380588662 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 625450523303 := Nat.prime_eq_prime_of_dvd_pow hq prime_625450523303 hd
            subst q
            change (7 : ZMod 1459142296537640639)^2332946 ≠ 1
            reduce_mod_char
            decide

theorem prime_1467382137689406067 : Nat.Prime 1467382137689406067 := by
  apply lucas_primality 1467382137689406067 (3 : ZMod 1467382137689406067)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1467382137689406067 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((19 : ℕ)^1 * ((1657 : ℕ)^1 * ((2300267 : ℕ)^1 * ((3377051 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1467382137689406067)^733691068844703033 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1467382137689406067)^489127379229802022 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
          subst q
          change (3 : ZMod 1467382137689406067)^77230638825758214 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1657 := Nat.prime_eq_prime_of_dvd_pow hq prime_1657 hd
            subst q
            change (3 : ZMod 1467382137689406067)^885565562878338 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 2300267 := Nat.prime_eq_prime_of_dvd_pow hq prime_2300267 hd
              subst q
              change (3 : ZMod 1467382137689406067)^637918179798 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 3377051 := Nat.prime_eq_prime_of_dvd_pow hq prime_3377051 hd
              subst q
              change (3 : ZMod 1467382137689406067)^434515835766 ≠ 1
              reduce_mod_char
              decide

theorem prime_1475660718024024199 : Nat.Prime 1475660718024024199 := by
  apply lucas_primality 1475660718024024199 (3 : ZMod 1475660718024024199)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1475660718024024199 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((245943453004004033 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1475660718024024199)^737830359012012099 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1475660718024024199)^491886906008008066 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 245943453004004033 := Nat.prime_eq_prime_of_dvd_pow hq prime_245943453004004033 hd
        subst q
        change (3 : ZMod 1475660718024024199)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_1483978183108890691 : Nat.Prime 1483978183108890691 := by
  apply lucas_primality 1483978183108890691 (2 : ZMod 1483978183108890691)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1483978183108890691 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((30649 : ℕ)^1 * ((124149964579 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1483978183108890691)^741989091554445345 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1483978183108890691)^494659394369630230 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 1483978183108890691)^296795636621778138 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (2 : ZMod 1483978183108890691)^114152167931453130 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 30649 := Nat.prime_eq_prime_of_dvd_pow hq prime_30649 hd
              subst q
              change (2 : ZMod 1483978183108890691)^48418486185810 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 124149964579 := Nat.prime_eq_prime_of_dvd_pow hq prime_124149964579 hd
              subst q
              change (2 : ZMod 1483978183108890691)^11953110 ≠ 1
              reduce_mod_char
              decide

theorem prime_1492334678921257099 : Nat.Prime 1492334678921257099 := by
  apply lucas_primality 1492334678921257099 (2 : ZMod 1492334678921257099)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1492334678921257099 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((47149 : ℕ)^1 * ((586138144763 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1492334678921257099)^746167339460628549 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1492334678921257099)^497444892973752366 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47149 := Nat.prime_eq_prime_of_dvd_pow hq prime_47149 hd
          subst q
          change (2 : ZMod 1492334678921257099)^31651459817202 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 586138144763 := Nat.prime_eq_prime_of_dvd_pow hq prime_586138144763 hd
          subst q
          change (2 : ZMod 1492334678921257099)^2546046 ≠ 1
          reduce_mod_char
          decide

theorem prime_1500730351849000039 : Nat.Prime 1500730351849000039 := by
  apply lucas_primality 1500730351849000039 (11 : ZMod 1500730351849000039)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1500730351849000039 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((307 : ℕ)^1 * ((479 : ℕ)^1 * ((572573 : ℕ)^1 * ((228509 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 1500730351849000039)^750365175924500019 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 1500730351849000039)^500243450616333346 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (11 : ZMod 1500730351849000039)^115440796296076926 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 307 := Nat.prime_eq_prime_of_dvd_pow hq prime_307 hd
            subst q
            change (11 : ZMod 1500730351849000039)^4888372481592834 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 479 := Nat.prime_eq_prime_of_dvd_pow hq prime_479 hd
              subst q
              change (11 : ZMod 1500730351849000039)^3133048751250522 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 572573 := Nat.prime_eq_prime_of_dvd_pow hq prime_572573 hd
                subst q
                change (11 : ZMod 1500730351849000039)^2621028850206 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 228509 := Nat.prime_eq_prime_of_dvd_pow hq prime_228509 hd
                subst q
                change (11 : ZMod 1500730351849000039)^6567489034782 ≠ 1
                reduce_mod_char
                decide

theorem prime_1509165348691389941 : Nat.Prime 1509165348691389941 := by
  apply lucas_primality 1509165348691389941 (2 : ZMod 1509165348691389941)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1509165348691389941 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((47 : ℕ)^1 * ((15078797 : ℕ)^1 * ((106473683 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1509165348691389941)^754582674345694970 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 1509165348691389941)^301833069738277988 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
          subst q
          change (2 : ZMod 1509165348691389941)^32109901035987020 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 15078797 := Nat.prime_eq_prime_of_dvd_pow hq prime_15078797 hd
            subst q
            change (2 : ZMod 1509165348691389941)^100085262020 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 106473683 := Nat.prime_eq_prime_of_dvd_pow hq prime_106473683 hd
            subst q
            change (2 : ZMod 1509165348691389941)^14174069180 ≠ 1
            reduce_mod_char
            decide

theorem prime_1517639816659861513 : Nat.Prime 1517639816659861513 := by
  apply lucas_primality 1517639816659861513 (5 : ZMod 1517639816659861513)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1517639816659861513 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((73 : ℕ)^1 * ((409 : ℕ)^1 * ((191531 : ℕ)^1 * ((3685963 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1517639816659861513)^758819908329930756 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1517639816659861513)^505879938886620504 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
          subst q
          change (5 : ZMod 1517639816659861513)^20789586529587144 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 409 := Nat.prime_eq_prime_of_dvd_pow hq prime_409 hd
            subst q
            change (5 : ZMod 1517639816659861513)^3710610798679368 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 191531 := Nat.prime_eq_prime_of_dvd_pow hq prime_191531 hd
              subst q
              change (5 : ZMod 1517639816659861513)^7923729404952 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 3685963 := Nat.prime_eq_prime_of_dvd_pow hq prime_3685963 hd
              subst q
              change (5 : ZMod 1517639816659861513)^411734956824 ≠ 1
              reduce_mod_char
              decide

theorem prime_1526153903378784307 : Nat.Prime 1526153903378784307 := by
  apply lucas_primality 1526153903378784307 (2 : ZMod 1526153903378784307)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1526153903378784307 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((11 : ℕ)^1 * ((45841 : ℕ)^1 * ((56047701089 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1526153903378784307)^763076951689392153 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1526153903378784307)^508717967792928102 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 1526153903378784307)^138741263943525846 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 45841 := Nat.prime_eq_prime_of_dvd_pow hq prime_45841 hd
            subst q
            change (2 : ZMod 1526153903378784307)^33292334446866 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 56047701089 := Nat.prime_eq_prime_of_dvd_pow hq prime_56047701089 hd
            subst q
            change (2 : ZMod 1526153903378784307)^27229554 ≠ 1
            reduce_mod_char
            decide

theorem prime_1534707756886234187 : Nat.Prime 1534707756886234187 := by
  apply lucas_primality 1534707756886234187 (2 : ZMod 1534707756886234187)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1534707756886234187 - 1 = (2 : ℕ)^1 * ((41 : ℕ)^1 * ((18715948254710173 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1534707756886234187)^767353878443117093 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
        subst q
        change (2 : ZMod 1534707756886234187)^37431896509420346 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 18715948254710173 := Nat.prime_eq_prime_of_dvd_pow hq prime_18715948254710173 hd
        subst q
        change (2 : ZMod 1534707756886234187)^82 ≠ 1
        reduce_mod_char
        decide

theorem prime_1543301525634765629 : Nat.Prime 1543301525634765629 := by
  apply lucas_primality 1543301525634765629 (2 : ZMod 1543301525634765629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1543301525634765629 - 1 = (2 : ℕ)^2 * ((385825381408691407 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1543301525634765629)^771650762817382814 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 385825381408691407 := Nat.prime_eq_prime_of_dvd_pow hq prime_385825381408691407 hd
      subst q
      change (2 : ZMod 1543301525634765629)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_1551935358492184639 : Nat.Prime 1551935358492184639 := by
  apply lucas_primality 1551935358492184639 (15 : ZMod 1551935358492184639)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1551935358492184639 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((4105649096540171 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (15 : ZMod 1551935358492184639)^775967679246092319 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (15 : ZMod 1551935358492184639)^517311786164061546 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (15 : ZMod 1551935358492184639)^221705051213169234 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4105649096540171 := Nat.prime_eq_prime_of_dvd_pow hq prime_4105649096540171 hd
          subst q
          change (15 : ZMod 1551935358492184639)^378 ≠ 1
          reduce_mod_char
          decide

theorem prime_1560609404742322163 : Nat.Prime 1560609404742322163 := by
  apply lucas_primality 1560609404742322163 (2 : ZMod 1560609404742322163)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1560609404742322163 - 1 = (2 : ℕ)^1 * ((10607 : ℕ)^1 * ((73565070460183 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1560609404742322163)^780304702371161081 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 10607 := Nat.prime_eq_prime_of_dvd_pow hq prime_10607 hd
        subst q
        change (2 : ZMod 1560609404742322163)^147130140920366 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 73565070460183 := Nat.prime_eq_prime_of_dvd_pow hq prime_73565070460183 hd
        subst q
        change (2 : ZMod 1560609404742322163)^21214 ≠ 1
        reduce_mod_char
        decide

theorem prime_1569323814085808741 : Nat.Prime 1569323814085808741 := by
  apply lucas_primality 1569323814085808741 (2 : ZMod 1569323814085808741)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1569323814085808741 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((28229 : ℕ)^1 * ((2779630546753 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1569323814085808741)^784661907042904370 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 1569323814085808741)^313864762817161748 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 28229 := Nat.prime_eq_prime_of_dvd_pow hq prime_28229 hd
          subst q
          change (2 : ZMod 1569323814085808741)^55592610935060 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2779630546753 := Nat.prime_eq_prime_of_dvd_pow hq prime_2779630546753 hd
          subst q
          change (2 : ZMod 1569323814085808741)^564580 ≠ 1
          reduce_mod_char
          decide

theorem prime_1578078736640849557 : Nat.Prime 1578078736640849557 := by
  apply lucas_primality 1578078736640849557 (5 : ZMod 1578078736640849557)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1578078736640849557 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((701 : ℕ)^1 * ((20479 : ℕ)^1 * ((3053510399 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1578078736640849557)^789039368320424778 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1578078736640849557)^526026245546949852 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 701 := Nat.prime_eq_prime_of_dvd_pow hq prime_701 hd
          subst q
          change (5 : ZMod 1578078736640849557)^2251182220600356 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 20479 := Nat.prime_eq_prime_of_dvd_pow hq prime_20479 hd
            subst q
            change (5 : ZMod 1578078736640849557)^77058388429164 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3053510399 := Nat.prime_eq_prime_of_dvd_pow hq prime_3053510399 hd
            subst q
            change (5 : ZMod 1578078736640849557)^516808044 ≠ 1
            reduce_mod_char
            decide

theorem prime_1586874322944000017 : Nat.Prime 1586874322944000017 := by
  apply lucas_primality 1586874322944000017 (3 : ZMod 1586874322944000017)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1586874322944000017 - 1 = (2 : ℕ)^4 * ((8389 : ℕ)^1 * ((427789 : ℕ)^1 * ((27636481 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1586874322944000017)^793437161472000008 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 8389 := Nat.prime_eq_prime_of_dvd_pow hq prime_8389 hd
        subst q
        change (3 : ZMod 1586874322944000017)^189161321128144 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 427789 := Nat.prime_eq_prime_of_dvd_pow hq prime_427789 hd
          subst q
          change (3 : ZMod 1586874322944000017)^3709479025744 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 27636481 := Nat.prime_eq_prime_of_dvd_pow hq prime_27636481 hd
          subst q
          change (3 : ZMod 1586874322944000017)^57419550736 ≠ 1
          reduce_mod_char
          decide

theorem prime_1595710723950942509 : Nat.Prime 1595710723950942509 := by
  apply lucas_primality 1595710723950942509 (3 : ZMod 1595710723950942509)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1595710723950942509 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((31 : ℕ)^1 * ((79 : ℕ)^1 * ((163 : ℕ)^1 * ((37591 : ℕ)^1 * ((292141 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1595710723950942509)^797855361975471254 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 1595710723950942509)^227958674850134644 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 1595710723950942509)^122746978765457116 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (3 : ZMod 1595710723950942509)^51474539482288468 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
              subst q
              change (3 : ZMod 1595710723950942509)^20198869923429652 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
                subst q
                change (3 : ZMod 1595710723950942509)^9789636343257316 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 37591 := Nat.prime_eq_prime_of_dvd_pow hq prime_37591 hd
                  subst q
                  change (3 : ZMod 1595710723950942509)^42449275729588 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 292141 := Nat.prime_eq_prime_of_dvd_pow hq prime_292141 hd
                  subst q
                  change (3 : ZMod 1595710723950942509)^5462125220188 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_1604588091037263473 : Nat.Prime 1604588091037263473 := by
  apply lucas_primality 1604588091037263473 (3 : ZMod 1604588091037263473)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1604588091037263473 - 1 = (2 : ℕ)^4 * ((7 : ℕ)^1 * ((337 : ℕ)^1 * ((42512401733713 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1604588091037263473)^802294045518631736 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 1604588091037263473)^229226870148180496 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 337 := Nat.prime_eq_prime_of_dvd_pow hq prime_337 hd
          subst q
          change (3 : ZMod 1604588091037263473)^4761388994175856 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 42512401733713 := Nat.prime_eq_prime_of_dvd_pow hq prime_42512401733713 hd
          subst q
          change (3 : ZMod 1604588091037263473)^37744 ≠ 1
          reduce_mod_char
          decide

theorem prime_1613506575999231413 : Nat.Prime 1613506575999231413 := by
  apply lucas_primality 1613506575999231413 (2 : ZMod 1613506575999231413)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1613506575999231413 - 1 = (2 : ℕ)^2 * ((403376643999807853 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1613506575999231413)^806753287999615706 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 403376643999807853 := Nat.prime_eq_prime_of_dvd_pow hq prime_403376643999807853 hd
      subst q
      change (2 : ZMod 1613506575999231413)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_1622466331054575647 : Nat.Prime 1622466331054575647 := by
  apply lucas_primality 1622466331054575647 (5 : ZMod 1622466331054575647)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1622466331054575647 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((31 : ℕ)^1 * ((1137774425704471 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1622466331054575647)^811233165527287823 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (5 : ZMod 1622466331054575647)^70542014393677202 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (5 : ZMod 1622466331054575647)^52337623582405666 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1137774425704471 := Nat.prime_eq_prime_of_dvd_pow hq prime_1137774425704471 hd
          subst q
          change (5 : ZMod 1622466331054575647)^1426 ≠ 1
          reduce_mod_char
          decide

theorem prime_1631467508843265641 : Nat.Prime 1631467508843265641 := by
  apply lucas_primality 1631467508843265641 (13 : ZMod 1631467508843265641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1631467508843265641 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((40786687721081641 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 1631467508843265641)^815733754421632820 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (13 : ZMod 1631467508843265641)^326293501768653128 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 40786687721081641 := Nat.prime_eq_prime_of_dvd_pow hq prime_40786687721081641 hd
        subst q
        change (13 : ZMod 1631467508843265641)^40 ≠ 1
        reduce_mod_char
        decide

theorem prime_1640510262428291147 : Nat.Prime 1640510262428291147 := by
  apply lucas_primality 1640510262428291147 (2 : ZMod 1640510262428291147)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1640510262428291147 - 1 = (2 : ℕ)^1 * ((135173 : ℕ)^1 * ((162343 : ℕ)^1 * ((37378807 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1640510262428291147)^820255131214145573 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 135173 := Nat.prime_eq_prime_of_dvd_pow hq prime_135173 hd
        subst q
        change (2 : ZMod 1640510262428291147)^12136375329602 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 162343 := Nat.prime_eq_prime_of_dvd_pow hq prime_162343 hd
          subst q
          change (2 : ZMod 1640510262428291147)^10105210957222 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 37378807 := Nat.prime_eq_prime_of_dvd_pow hq prime_37378807 hd
          subst q
          change (2 : ZMod 1640510262428291147)^43888780678 ≠ 1
          reduce_mod_char
          decide

theorem prime_1649594745296443037 : Nat.Prime 1649594745296443037 := by
  apply lucas_primality 1649594745296443037 (2 : ZMod 1649594745296443037)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1649594745296443037 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((19 : ℕ)^1 * ((379 : ℕ)^1 * ((2221 : ℕ)^1 * ((3109 : ℕ)^1 * ((91141 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1649594745296443037)^824797372648221518 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 1649594745296443037)^235656392185206148 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 1649594745296443037)^126891903484341772 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (2 : ZMod 1649594745296443037)^86820776068233844 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 379 := Nat.prime_eq_prime_of_dvd_pow hq prime_379 hd
              subst q
              change (2 : ZMod 1649594745296443037)^4352492731652884 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 2221 := Nat.prime_eq_prime_of_dvd_pow hq prime_2221 hd
                subst q
                change (2 : ZMod 1649594745296443037)^742726134757516 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 3109 := Nat.prime_eq_prime_of_dvd_pow hq prime_3109 hd
                  subst q
                  change (2 : ZMod 1649594745296443037)^530586923543404 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 91141 := Nat.prime_eq_prime_of_dvd_pow hq prime_91141 hd
                  subst q
                  change (2 : ZMod 1649594745296443037)^18099370703596 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_1658721111359094791 : Nat.Prime 1658721111359094791 := by
  apply lucas_primality 1658721111359094791 (7 : ZMod 1658721111359094791)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1658721111359094791 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((53 : ℕ)^1 * ((313 : ℕ)^1 * ((1949 : ℕ)^1 * ((732897577 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1658721111359094791)^829360555679547395 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 1658721111359094791)^331744222271818958 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 1658721111359094791)^236960158765584970 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
            subst q
            change (7 : ZMod 1658721111359094791)^31296624742624430 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 313 := Nat.prime_eq_prime_of_dvd_pow hq prime_313 hd
              subst q
              change (7 : ZMod 1658721111359094791)^5299428470795830 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 1949 := Nat.prime_eq_prime_of_dvd_pow hq prime_1949 hd
                subst q
                change (7 : ZMod 1658721111359094791)^851062653339710 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 732897577 := Nat.prime_eq_prime_of_dvd_pow hq prime_732897577 hd
                subst q
                change (7 : ZMod 1658721111359094791)^2263237270 ≠ 1
                reduce_mod_char
                decide

theorem prime_1667889514952985179 : Nat.Prime 1667889514952985179 := by
  apply lucas_primality 1667889514952985179 (2 : ZMod 1667889514952985179)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1667889514952985179 - 1 = (2 : ℕ)^1 * ((19 : ℕ)^1 * ((23 : ℕ)^1 * ((109 : ℕ)^1 * ((233 : ℕ)^1 * ((503 : ℕ)^1 * ((149384467 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1667889514952985179)^833944757476492589 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 1667889514952985179)^87783658681736062 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (2 : ZMod 1667889514952985179)^72516935432738486 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
            subst q
            change (2 : ZMod 1667889514952985179)^15301738669293442 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 233 := Nat.prime_eq_prime_of_dvd_pow hq prime_233 hd
              subst q
              change (2 : ZMod 1667889514952985179)^7158324098510666 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 503 := Nat.prime_eq_prime_of_dvd_pow hq prime_503 hd
                subst q
                change (2 : ZMod 1667889514952985179)^3315883727540726 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 149384467 := Nat.prime_eq_prime_of_dvd_pow hq prime_149384467 hd
                subst q
                change (2 : ZMod 1667889514952985179)^11165079934 ≠ 1
                reduce_mod_char
                decide

theorem prime_1677100110841000003 : Nat.Prime 1677100110841000003 := by
  apply lucas_primality 1677100110841000003 (2 : ZMod 1677100110841000003)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1677100110841000003 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((53267 : ℕ)^1 * ((2011601 : ℕ)^1 * ((2608601 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1677100110841000003)^838550055420500001 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1677100110841000003)^559033370280333334 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 53267 := Nat.prime_eq_prime_of_dvd_pow hq prime_53267 hd
          subst q
          change (2 : ZMod 1677100110841000003)^31484786281206 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2011601 := Nat.prime_eq_prime_of_dvd_pow hq prime_2011601 hd
            subst q
            change (2 : ZMod 1677100110841000003)^833714096802 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2608601 := Nat.prime_eq_prime_of_dvd_pow hq prime_2608601 hd
            subst q
            change (2 : ZMod 1677100110841000003)^642911702802 ≠ 1
            reduce_mod_char
            decide

theorem prime_1686353054212958051 : Nat.Prime 1686353054212958051 := by
  apply lucas_primality 1686353054212958051 (2 : ZMod 1686353054212958051)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1686353054212958051 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((33727061084259161 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1686353054212958051)^843176527106479025 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 1686353054212958051)^337270610842591610 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 33727061084259161 := Nat.prime_eq_prime_of_dvd_pow hq prime_33727061084259161 hd
        subst q
        change (2 : ZMod 1686353054212958051)^50 ≠ 1
        reduce_mod_char
        decide

theorem prime_1695648500686393417 : Nat.Prime 1695648500686393417 := by
  apply lucas_primality 1695648500686393417 (5 : ZMod 1695648500686393417)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1695648500686393417 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((12041 : ℕ)^1 * ((1955873567033 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1695648500686393417)^847824250343196708 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1695648500686393417)^565216166895464472 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 12041 := Nat.prime_eq_prime_of_dvd_pow hq prime_12041 hd
          subst q
          change (5 : ZMod 1695648500686393417)^140822896826376 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1955873567033 := Nat.prime_eq_prime_of_dvd_pow hq prime_1955873567033 hd
          subst q
          change (5 : ZMod 1695648500686393417)^866952 ≠ 1
          reduce_mod_char
          decide

theorem prime_1704986606307341521 : Nat.Prime 1704986606307341521 := by
  apply lucas_primality 1704986606307341521 (7 : ZMod 1704986606307341521)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1704986606307341521 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((29 : ℕ)^1 * ((4451 : ℕ)^1 * ((34649 : ℕ)^1 * ((529471 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1704986606307341521)^852493303153670760 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 1704986606307341521)^568328868769113840 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 1704986606307341521)^340997321261468304 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
            subst q
            change (7 : ZMod 1704986606307341521)^58792641596804880 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 4451 := Nat.prime_eq_prime_of_dvd_pow hq prime_4451 hd
              subst q
              change (7 : ZMod 1704986606307341521)^383056977377520 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 34649 := Nat.prime_eq_prime_of_dvd_pow hq prime_34649 hd
                subst q
                change (7 : ZMod 1704986606307341521)^49207382790480 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 529471 := Nat.prime_eq_prime_of_dvd_pow hq prime_529471 hd
                subst q
                change (7 : ZMod 1704986606307341521)^3220169955120 ≠ 1
                reduce_mod_char
                decide

theorem prime_1714367527551125059 : Nat.Prime 1714367527551125059 := by
  apply lucas_primality 1714367527551125059 (7 : ZMod 1714367527551125059)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1714367527551125059 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((59 : ℕ)^2 * ((751481 : ℕ)^1 * ((109227163 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1714367527551125059)^857183763775562529 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 1714367527551125059)^571455842517041686 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (7 : ZMod 1714367527551125059)^29057076738154662 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 751481 := Nat.prime_eq_prime_of_dvd_pow hq prime_751481 hd
            subst q
            change (7 : ZMod 1714367527551125059)^2281318526418 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 109227163 := Nat.prime_eq_prime_of_dvd_pow hq prime_109227163 hd
            subst q
            change (7 : ZMod 1714367527551125059)^15695432166 ≠ 1
            reduce_mod_char
            decide

theorem prime_1723791421323140641 : Nat.Prime 1723791421323140641 := by
  apply lucas_primality 1723791421323140641 (7 : ZMod 1723791421323140641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1723791421323140641 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((4673 : ℕ)^1 * ((768506768191 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1723791421323140641)^861895710661570320 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 1723791421323140641)^574597140441046880 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 1723791421323140641)^344758284264628128 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 4673 := Nat.prime_eq_prime_of_dvd_pow hq prime_4673 hd
            subst q
            change (7 : ZMod 1723791421323140641)^368883248731680 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 768506768191 := Nat.prime_eq_prime_of_dvd_pow hq prime_768506768191 hd
            subst q
            change (7 : ZMod 1723791421323140641)^2243040 ≠ 1
            reduce_mod_char
            decide

theorem prime_1733258444959645699 : Nat.Prime 1733258444959645699 := by
  apply lucas_primality 1733258444959645699 (2 : ZMod 1733258444959645699)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1733258444959645699 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((43 : ℕ)^1 * ((131 : ℕ)^1 * ((214363 : ℕ)^1 * ((239233777 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1733258444959645699)^866629222479822849 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1733258444959645699)^577752814986548566 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (2 : ZMod 1733258444959645699)^40308335929294086 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
            subst q
            change (2 : ZMod 1733258444959645699)^13230980495875158 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 214363 := Nat.prime_eq_prime_of_dvd_pow hq prime_214363 hd
              subst q
              change (2 : ZMod 1733258444959645699)^8085623195046 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 239233777 := Nat.prime_eq_prime_of_dvd_pow hq prime_239233777 hd
              subst q
              change (2 : ZMod 1733258444959645699)^7245040674 ≠ 1
              reduce_mod_char
              decide

theorem prime_1742768756228546983 : Nat.Prime 1742768756228546983 := by
  apply lucas_primality 1742768756228546983 (3 : ZMod 1742768756228546983)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1742768756228546983 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((13 : ℕ)^1 * ((149 : ℕ)^1 * ((1811983 : ℕ)^1 * ((9195223 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1742768756228546983)^871384378114273491 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1742768756228546983)^580922918742848994 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 1742768756228546983)^134059135094503614 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 149 := Nat.prime_eq_prime_of_dvd_pow hq prime_149 hd
            subst q
            change (3 : ZMod 1742768756228546983)^11696434605560718 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1811983 := Nat.prime_eq_prime_of_dvd_pow hq prime_1811983 hd
              subst q
              change (3 : ZMod 1742768756228546983)^961801935354 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 9195223 := Nat.prime_eq_prime_of_dvd_pow hq prime_9195223 hd
              subst q
              change (3 : ZMod 1742768756228546983)^189529797834 ≠ 1
              reduce_mod_char
              decide

theorem prime_1752322513330188883 : Nat.Prime 1752322513330188883 := by
  apply lucas_primality 1752322513330188883 (2 : ZMod 1752322513330188883)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1752322513330188883 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((1907 : ℕ)^1 * ((2609 : ℕ)^1 * ((19566662923 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1752322513330188883)^876161256665094441 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1752322513330188883)^584107504443396294 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1907 := Nat.prime_eq_prime_of_dvd_pow hq prime_1907 hd
          subst q
          change (2 : ZMod 1752322513330188883)^918889624189926 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2609 := Nat.prime_eq_prime_of_dvd_pow hq prime_2609 hd
            subst q
            change (2 : ZMod 1752322513330188883)^671645271494898 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 19566662923 := Nat.prime_eq_prime_of_dvd_pow hq prime_19566662923 hd
            subst q
            change (2 : ZMod 1752322513330188883)^89556534 ≠ 1
            reduce_mod_char
            decide

theorem prime_1761919874898143591 : Nat.Prime 1761919874898143591 := by
  apply lucas_primality 1761919874898143591 (7 : ZMod 1761919874898143591)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1761919874898143591 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((223 : ℕ)^1 * ((593 : ℕ)^1 * ((398117 : ℕ)^1 * ((478099 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1761919874898143591)^880959937449071795 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 1761919874898143591)^352383974979628718 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 1761919874898143591)^251702839271163370 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 223 := Nat.prime_eq_prime_of_dvd_pow hq prime_223 hd
            subst q
            change (7 : ZMod 1761919874898143591)^7900985986090330 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 593 := Nat.prime_eq_prime_of_dvd_pow hq prime_593 hd
              subst q
              change (7 : ZMod 1761919874898143591)^2971197090890630 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 398117 := Nat.prime_eq_prime_of_dvd_pow hq prime_398117 hd
                subst q
                change (7 : ZMod 1761919874898143591)^4425633356270 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 478099 := Nat.prime_eq_prime_of_dvd_pow hq prime_478099 hd
                subst q
                change (7 : ZMod 1761919874898143591)^3685261577410 ≠ 1
                reduce_mod_char
                decide

theorem prime_1771561000000000019 : Nat.Prime 1771561000000000019 := by
  apply lucas_primality 1771561000000000019 (2 : ZMod 1771561000000000019)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1771561000000000019 - 1 = (2 : ℕ)^1 * ((26062891 : ℕ)^1 * ((33986271899 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1771561000000000019)^885780500000000009 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 26062891 := Nat.prime_eq_prime_of_dvd_pow hq prime_26062891 hd
        subst q
        change (2 : ZMod 1771561000000000019)^67972543798 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 33986271899 := Nat.prime_eq_prime_of_dvd_pow hq prime_33986271899 hd
        subst q
        change (2 : ZMod 1771561000000000019)^52125782 ≠ 1
        reduce_mod_char
        decide

theorem prime_1781246048138156641 : Nat.Prime 1781246048138156641 := by
  apply lucas_primality 1781246048138156641 (7 : ZMod 1781246048138156641)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1781246048138156641 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((4259 : ℕ)^1 * ((6311 : ℕ)^1 * ((138062857 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1781246048138156641)^890623024069078320 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 1781246048138156641)^593748682712718880 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 1781246048138156641)^356249209627631328 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 4259 := Nat.prime_eq_prime_of_dvd_pow hq prime_4259 hd
            subst q
            change (7 : ZMod 1781246048138156641)^418231051452960 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 6311 := Nat.prime_eq_prime_of_dvd_pow hq prime_6311 hd
              subst q
              change (7 : ZMod 1781246048138156641)^282244659822240 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 138062857 := Nat.prime_eq_prime_of_dvd_pow hq prime_138062857 hd
              subst q
              change (7 : ZMod 1781246048138156641)^12901703520 ≠ 1
              reduce_mod_char
              decide

theorem prime_1790975179250611273 : Nat.Prime 1790975179250611273 := by
  apply lucas_primality 1790975179250611273 (7 : ZMod 1790975179250611273)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1790975179250611273 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^4 * ((43 : ℕ)^1 * ((523 : ℕ)^1 * ((34147 : ℕ)^1 * ((3599083 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1790975179250611273)^895487589625305636 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 1790975179250611273)^596991726416870424 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (7 : ZMod 1790975179250611273)^41650585563967704 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 523 := Nat.prime_eq_prime_of_dvd_pow hq prime_523 hd
            subst q
            change (7 : ZMod 1790975179250611273)^3424426728968664 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 34147 := Nat.prime_eq_prime_of_dvd_pow hq prime_34147 hd
              subst q
              change (7 : ZMod 1790975179250611273)^52448975876376 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 3599083 := Nat.prime_eq_prime_of_dvd_pow hq prime_3599083 hd
              subst q
              change (7 : ZMod 1790975179250611273)^497619860184 ≠ 1
              reduce_mod_char
              decide

theorem prime_1800748553711754587 : Nat.Prime 1800748553711754587 := by
  apply lucas_primality 1800748553711754587 (2 : ZMod 1800748553711754587)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1800748553711754587 - 1 = (2 : ℕ)^1 * ((29 : ℕ)^1 * ((53 : ℕ)^1 * ((613 : ℕ)^1 * ((1163 : ℕ)^1 * ((10061 : ℕ)^1 * ((81671 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1800748553711754587)^900374276855877293 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (2 : ZMod 1800748553711754587)^62094777714198434 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (2 : ZMod 1800748553711754587)^33976387805882162 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 613 := Nat.prime_eq_prime_of_dvd_pow hq prime_613 hd
            subst q
            change (2 : ZMod 1800748553711754587)^2937599598224722 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1163 := Nat.prime_eq_prime_of_dvd_pow hq prime_1163 hd
              subst q
              change (2 : ZMod 1800748553711754587)^1548365050483022 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 10061 := Nat.prime_eq_prime_of_dvd_pow hq prime_10061 hd
                subst q
                change (2 : ZMod 1800748553711754587)^178983058713026 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 81671 := Nat.prime_eq_prime_of_dvd_pow hq prime_81671 hd
                subst q
                change (2 : ZMod 1800748553711754587)^22048812353366 ≠ 1
                reduce_mod_char
                decide

theorem prime_1810566332333162513 : Nat.Prime 1810566332333162513 := by
  apply lucas_primality 1810566332333162513 (3 : ZMod 1810566332333162513)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1810566332333162513 - 1 = (2 : ℕ)^4 * ((17 : ℕ)^1 * ((101 : ℕ)^1 * ((3321917 : ℕ)^1 * ((19839713 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1810566332333162513)^905283166166581256 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (3 : ZMod 1810566332333162513)^106503901901950736 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
          subst q
          change (3 : ZMod 1810566332333162513)^17926399330031312 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3321917 := Nat.prime_eq_prime_of_dvd_pow hq prime_3321917 hd
            subst q
            change (3 : ZMod 1810566332333162513)^545036595536 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 19839713 := Nat.prime_eq_prime_of_dvd_pow hq prime_19839713 hd
            subst q
            change (3 : ZMod 1810566332333162513)^91259703824 ≠ 1
            reduce_mod_char
            decide

theorem prime_1820428676364390629 : Nat.Prime 1820428676364390629 := by
  apply lucas_primality 1820428676364390629 (2 : ZMod 1820428676364390629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1820428676364390629 - 1 = (2 : ℕ)^2 * ((455107169091097657 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1820428676364390629)^910214338182195314 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 455107169091097657 := Nat.prime_eq_prime_of_dvd_pow hq prime_455107169091097657 hd
      subst q
      change (2 : ZMod 1820428676364390629)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_1830335747493768293 : Nat.Prime 1830335747493768293 := by
  apply lucas_primality 1830335747493768293 (2 : ZMod 1830335747493768293)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1830335747493768293 - 1 = (2 : ℕ)^2 * ((1597 : ℕ)^1 * ((6113 : ℕ)^1 * ((16301 : ℕ)^1 * ((2875393 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1830335747493768293)^915167873746884146 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1597 := Nat.prime_eq_prime_of_dvd_pow hq prime_1597 hd
        subst q
        change (2 : ZMod 1830335747493768293)^1146108796176436 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 6113 := Nat.prime_eq_prime_of_dvd_pow hq prime_6113 hd
          subst q
          change (2 : ZMod 1830335747493768293)^299416938899684 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 16301 := Nat.prime_eq_prime_of_dvd_pow hq prime_16301 hd
            subst q
            change (2 : ZMod 1830335747493768293)^112283648088692 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2875393 := Nat.prime_eq_prime_of_dvd_pow hq prime_2875393 hd
            subst q
            change (2 : ZMod 1830335747493768293)^636551507044 ≠ 1
            reduce_mod_char
            decide

theorem prime_1840287707849193859 : Nat.Prime 1840287707849193859 := by
  apply lucas_primality 1840287707849193859 (2 : ZMod 1840287707849193859)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1840287707849193859 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((102238205991621881 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1840287707849193859)^920143853924596929 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1840287707849193859)^613429235949731286 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 102238205991621881 := Nat.prime_eq_prime_of_dvd_pow hq prime_102238205991621881 hd
        subst q
        change (2 : ZMod 1840287707849193859)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_1850284719998930947 : Nat.Prime 1850284719998930947 := by
  apply lucas_primality 1850284719998930947 (2 : ZMod 1850284719998930947)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1850284719998930947 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((113 : ℕ)^1 * ((12918491 : ℕ)^1 * ((12426481 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1850284719998930947)^925142359999465473 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1850284719998930947)^616761573332976982 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 1850284719998930947)^108840277646995938 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
            subst q
            change (2 : ZMod 1850284719998930947)^16374201061937442 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 12918491 := Nat.prime_eq_prime_of_dvd_pow hq prime_12918491 hd
              subst q
              change (2 : ZMod 1850284719998930947)^143227620006 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 12426481 := Nat.prime_eq_prime_of_dvd_pow hq prime_12426481 hd
              subst q
              change (2 : ZMod 1850284719998930947)^148898527266 ≠ 1
              reduce_mod_char
              decide

theorem prime_1860326946952404871 : Nat.Prime 1860326946952404871 := by
  apply lucas_primality 1860326946952404871 (3 : ZMod 1860326946952404871)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1860326946952404871 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((181 : ℕ)^1 * ((22189 : ℕ)^1 * ((197341 : ℕ)^1 * ((78241 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1860326946952404871)^930163473476202435 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1860326946952404871)^620108982317468290 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 1860326946952404871)^372065389390480974 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 181 := Nat.prime_eq_prime_of_dvd_pow hq prime_181 hd
            subst q
            change (3 : ZMod 1860326946952404871)^10278049430676270 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 22189 := Nat.prime_eq_prime_of_dvd_pow hq prime_22189 hd
              subst q
              change (3 : ZMod 1860326946952404871)^83840053492830 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 197341 := Nat.prime_eq_prime_of_dvd_pow hq prime_197341 hd
                subst q
                change (3 : ZMod 1860326946952404871)^9426966251070 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 78241 := Nat.prime_eq_prime_of_dvd_pow hq prime_78241 hd
                subst q
                change (3 : ZMod 1860326946952404871)^23776881008070 ≠ 1
                reduce_mod_char
                decide

theorem prime_1870414552161000017 : Nat.Prime 1870414552161000017 := by
  apply lucas_primality 1870414552161000017 (3 : ZMod 1870414552161000017)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1870414552161000017 - 1 = (2 : ℕ)^4 * ((29 : ℕ)^2 * ((30773 : ℕ)^1 * ((36217 : ℕ)^1 * ((124721 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1870414552161000017)^935207276080500008 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (3 : ZMod 1870414552161000017)^64497053522793104 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 30773 := Nat.prime_eq_prime_of_dvd_pow hq prime_30773 hd
          subst q
          change (3 : ZMod 1870414552161000017)^60781027269392 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 36217 := Nat.prime_eq_prime_of_dvd_pow hq prime_36217 hd
            subst q
            change (3 : ZMod 1870414552161000017)^51644657264848 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 124721 := Nat.prime_eq_prime_of_dvd_pow hq prime_124721 hd
            subst q
            change (3 : ZMod 1870414552161000017)^14996789250896 ≠ 1
            reduce_mod_char
            decide

end LegendreK6.Pratt
