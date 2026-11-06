import LegendreK6.Pratt.Block020

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LegendreK6.Pratt

theorem prime_274225886881579 : Nat.Prime 274225886881579 := by
  apply lucas_primality 274225886881579 (2 : ZMod 274225886881579)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 274225886881579 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((29 : ℕ)^1 * ((2281 : ℕ)^1 * ((230309929 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 274225886881579)^137112943440789 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 274225886881579)^91408628960526 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (2 : ZMod 274225886881579)^9456065064882 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2281 := Nat.prime_eq_prime_of_dvd_pow hq prime_2281 hd
            subst q
            change (2 : ZMod 274225886881579)^120221782938 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 230309929 := Nat.prime_eq_prime_of_dvd_pow hq prime_230309929 hd
            subst q
            change (2 : ZMod 274225886881579)^1190682 ≠ 1
            reduce_mod_char
            decide

theorem prime_274941996890651 : Nat.Prime 274941996890651 := by
  apply lucas_primality 274941996890651 (2 : ZMod 274941996890651)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 274941996890651 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((5498839937813 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 274941996890651)^137470998445325 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 274941996890651)^54988399378130 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 5498839937813 := Nat.prime_eq_prime_of_dvd_pow hq prime_5498839937813 hd
        subst q
        change (2 : ZMod 274941996890651)^50 ≠ 1
        reduce_mod_char
        decide

theorem prime_281474976710677 : Nat.Prime 281474976710677 := by
  apply lucas_primality 281474976710677 (6 : ZMod 281474976710677)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 281474976710677 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((1361 : ℕ)^1 * ((2462081249 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 281474976710677)^140737488355338 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 281474976710677)^93824992236892 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (6 : ZMod 281474976710677)^40210710958668 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1361 := Nat.prime_eq_prime_of_dvd_pow hq prime_1361 hd
            subst q
            change (6 : ZMod 281474976710677)^206814824916 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2462081249 := Nat.prime_eq_prime_of_dvd_pow hq prime_2462081249 hd
            subst q
            change (6 : ZMod 281474976710677)^114324 ≠ 1
            reduce_mod_char
            decide

theorem prime_285960035542283 : Nat.Prime 285960035542283 := by
  apply lucas_primality 285960035542283 (2 : ZMod 285960035542283)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 285960035542283 - 1 = (2 : ℕ)^1 * ((20710867 : ℕ)^1 * ((6903623 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 285960035542283)^142980017771141 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 20710867 := Nat.prime_eq_prime_of_dvd_pow hq prime_20710867 hd
        subst q
        change (2 : ZMod 285960035542283)^13807246 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 6903623 := Nat.prime_eq_prime_of_dvd_pow hq prime_6903623 hd
        subst q
        change (2 : ZMod 285960035542283)^41421734 ≠ 1
        reduce_mod_char
        decide

theorem prime_286287956614381 : Nat.Prime 286287956614381 := by
  apply lucas_primality 286287956614381 (6 : ZMod 286287956614381)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 286287956614381 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((17 : ℕ)^1 * ((7607 : ℕ)^1 * ((5270981 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 286287956614381)^143143978307190 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 286287956614381)^95429318871460 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 286287956614381)^57257591322876 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (6 : ZMod 286287956614381)^40898279516340 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
              subst q
              change (6 : ZMod 286287956614381)^16840468036140 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 7607 := Nat.prime_eq_prime_of_dvd_pow hq prime_7607 hd
                subst q
                change (6 : ZMod 286287956614381)^37634804340 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 5270981 := Nat.prime_eq_prime_of_dvd_pow hq prime_5270981 hd
                subst q
                change (6 : ZMod 286287956614381)^54313980 ≠ 1
                reduce_mod_char
                decide

theorem prime_288136807515701 : Nat.Prime 288136807515701 := by
  apply lucas_primality 288136807515701 (3 : ZMod 288136807515701)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 288136807515701 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^2 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((29 : ℕ)^1 * ((694807831 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 288136807515701)^144068403757850 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 288136807515701)^57627361503140 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 288136807515701)^26194255228700 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (3 : ZMod 288136807515701)^22164369808900 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
              subst q
              change (3 : ZMod 288136807515701)^9935751983300 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 694807831 := Nat.prime_eq_prime_of_dvd_pow hq prime_694807831 hd
              subst q
              change (3 : ZMod 288136807515701)^414700 ≠ 1
              reduce_mod_char
              decide

theorem prime_294929514414167 : Nat.Prime 294929514414167 := by
  apply lucas_primality 294929514414167 (5 : ZMod 294929514414167)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 294929514414167 - 1 = (2 : ℕ)^1 * ((97 : ℕ)^1 * ((1520255228939 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 294929514414167)^147464757207083 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
        subst q
        change (5 : ZMod 294929514414167)^3040510457878 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1520255228939 := Nat.prime_eq_prime_of_dvd_pow hq prime_1520255228939 hd
        subst q
        change (5 : ZMod 294929514414167)^194 ≠ 1
        reduce_mod_char
        decide

theorem prime_298832342330909 : Nat.Prime 298832342330909 := by
  apply lucas_primality 298832342330909 (2 : ZMod 298832342330909)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 298832342330909 - 1 = (2 : ℕ)^2 * ((29 : ℕ)^1 * ((41 : ℕ)^1 * ((3251 : ℕ)^1 * ((19327193 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 298832342330909)^149416171165454 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (2 : ZMod 298832342330909)^10304563528652 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (2 : ZMod 298832342330909)^7288593715388 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3251 := Nat.prime_eq_prime_of_dvd_pow hq prime_3251 hd
            subst q
            change (2 : ZMod 298832342330909)^91920129908 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 19327193 := Nat.prime_eq_prime_of_dvd_pow hq prime_19327193 hd
            subst q
            change (2 : ZMod 298832342330909)^15461756 ≠ 1
            reduce_mod_char
            decide

theorem prime_301855146292481 : Nat.Prime 301855146292481 := by
  apply lucas_primality 301855146292481 (3 : ZMod 301855146292481)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 301855146292481 - 1 = (2 : ℕ)^8 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((41 : ℕ)^1 * ((522892091 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 301855146292481)^150927573146240 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 301855146292481)^60371029258496 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 301855146292481)^27441376935680 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (3 : ZMod 301855146292481)^7362320641280 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 522892091 := Nat.prime_eq_prime_of_dvd_pow hq prime_522892091 hd
            subst q
            change (3 : ZMod 301855146292481)^577280 ≠ 1
            reduce_mod_char
            decide

theorem prime_308915776000031 : Nat.Prime 308915776000031 := by
  apply lucas_primality 308915776000031 (13 : ZMod 308915776000031)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 308915776000031 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((59 : ℕ)^1 * ((523586061017 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 308915776000031)^154457888000015 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (13 : ZMod 308915776000031)^61783155200006 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (13 : ZMod 308915776000031)^5235860610170 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 523586061017 := Nat.prime_eq_prime_of_dvd_pow hq prime_523586061017 hd
          subst q
          change (13 : ZMod 308915776000031)^590 ≠ 1
          reduce_mod_char
          decide

theorem prime_311680595157047 : Nat.Prime 311680595157047 := by
  apply lucas_primality 311680595157047 (5 : ZMod 311680595157047)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 311680595157047 - 1 = (2 : ℕ)^1 * ((47 : ℕ)^1 * ((661 : ℕ)^1 * ((5016264769 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 311680595157047)^155840297578523 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (5 : ZMod 311680595157047)^6631502024618 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 661 := Nat.prime_eq_prime_of_dvd_pow hq prime_661 hd
          subst q
          change (5 : ZMod 311680595157047)^471528888286 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 5016264769 := Nat.prime_eq_prime_of_dvd_pow hq prime_5016264769 hd
          subst q
          change (5 : ZMod 311680595157047)^62134 ≠ 1
          reduce_mod_char
          decide

theorem prime_316113500535583 : Nat.Prime 316113500535583 := by
  apply lucas_primality 316113500535583 (5 : ZMod 316113500535583)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 316113500535583 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((52685583422597 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 316113500535583)^158056750267791 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 316113500535583)^105371166845194 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 52685583422597 := Nat.prime_eq_prime_of_dvd_pow hq prime_52685583422597 hd
        subst q
        change (5 : ZMod 316113500535583)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_323450441233987 : Nat.Prime 323450441233987 := by
  apply lucas_primality 323450441233987 (2 : ZMod 323450441233987)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 323450441233987 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((48593 : ℕ)^1 * ((100853297 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 323450441233987)^161725220616993 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 323450441233987)^107816813744662 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 323450441233987)^29404585566726 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 48593 := Nat.prime_eq_prime_of_dvd_pow hq prime_48593 hd
            subst q
            change (2 : ZMod 323450441233987)^6656317602 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 100853297 := Nat.prime_eq_prime_of_dvd_pow hq prime_100853297 hd
            subst q
            change (2 : ZMod 323450441233987)^3207138 ≠ 1
            reduce_mod_char
            decide

theorem prime_324199648731181 : Nat.Prime 324199648731181 := by
  apply lucas_primality 324199648731181 (2 : ZMod 324199648731181)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 324199648731181 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((1436999 : ℕ)^1 * ((3760147 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 324199648731181)^162099824365590 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 324199648731181)^108066549577060 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 324199648731181)^64839929746236 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1436999 := Nat.prime_eq_prime_of_dvd_pow hq prime_1436999 hd
            subst q
            change (2 : ZMod 324199648731181)^225608820 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3760147 := Nat.prime_eq_prime_of_dvd_pow hq prime_3760147 hd
            subst q
            change (2 : ZMod 324199648731181)^86219940 ≠ 1
            reduce_mod_char
            decide

theorem prime_330928743953887 : Nat.Prime 330928743953887 := by
  apply lucas_primality 330928743953887 (3 : ZMod 330928743953887)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 330928743953887 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((31 : ℕ)^1 * ((7079 : ℕ)^1 * ((19333313 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 330928743953887)^165464371976943 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 330928743953887)^110309581317962 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 330928743953887)^25456057227222 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (3 : ZMod 330928743953887)^10675120772706 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 7079 := Nat.prime_eq_prime_of_dvd_pow hq prime_7079 hd
              subst q
              change (3 : ZMod 330928743953887)^46747950834 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 19333313 := Nat.prime_eq_prime_of_dvd_pow hq prime_19333313 hd
              subst q
              change (3 : ZMod 330928743953887)^17117022 ≠ 1
              reduce_mod_char
              decide

theorem prime_338550579265601 : Nat.Prime 338550579265601 := by
  apply lucas_primality 338550579265601 (6 : ZMod 338550579265601)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 338550579265601 - 1 = (2 : ℕ)^6 * ((5 : ℕ)^2 * ((13 : ℕ)^1 * ((17 : ℕ)^1 * ((41 : ℕ)^1 * ((23352181 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 338550579265601)^169275289632800 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 338550579265601)^67710115853120 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (6 : ZMod 338550579265601)^26042352251200 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (6 : ZMod 338550579265601)^19914739956800 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
              subst q
              change (6 : ZMod 338550579265601)^8257331201600 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 23352181 := Nat.prime_eq_prime_of_dvd_pow hq prime_23352181 hd
              subst q
              change (6 : ZMod 338550579265601)^14497600 ≠ 1
              reduce_mod_char
              decide

theorem prime_343064484000001 : Nat.Prime 343064484000001 := by
  apply lucas_primality 343064484000001 (23 : ZMod 343064484000001)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 343064484000001 - 1 = (2 : ℕ)^8 * ((3 : ℕ)^6 * ((5 : ℕ)^6 * ((7 : ℕ)^6))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (23 : ZMod 343064484000001)^171532242000000 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (23 : ZMod 343064484000001)^114354828000000 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (23 : ZMod 343064484000001)^68612896800000 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (23 : ZMod 343064484000001)^49009212000000 ≠ 1
          reduce_mod_char
          decide

theorem prime_346318142640649 : Nat.Prime 346318142640649 := by
  apply lucas_primality 346318142640649 (23 : ZMod 346318142640649)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 346318142640649 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((31 : ℕ)^1 * ((16747 : ℕ)^1 * ((27794911 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (23 : ZMod 346318142640649)^173159071320324 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (23 : ZMod 346318142640649)^115439380880216 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (23 : ZMod 346318142640649)^11171552988408 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 16747 := Nat.prime_eq_prime_of_dvd_pow hq prime_16747 hd
            subst q
            change (23 : ZMod 346318142640649)^20679413784 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 27794911 := Nat.prime_eq_prime_of_dvd_pow hq prime_27794911 hd
            subst q
            change (23 : ZMod 346318142640649)^12459768 ≠ 1
            reduce_mod_char
            decide

theorem prime_350870543412491 : Nat.Prime 350870543412491 := by
  apply lucas_primality 350870543412491 (2 : ZMod 350870543412491)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 350870543412491 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((173 : ℕ)^1 * ((44203 : ℕ)^1 * ((4588271 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 350870543412491)^175435271706245 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 350870543412491)^70174108682498 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 173 := Nat.prime_eq_prime_of_dvd_pow hq prime_173 hd
          subst q
          change (2 : ZMod 350870543412491)^2028153430130 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 44203 := Nat.prime_eq_prime_of_dvd_pow hq prime_44203 hd
            subst q
            change (2 : ZMod 350870543412491)^7937708830 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 4588271 := Nat.prime_eq_prime_of_dvd_pow hq prime_4588271 hd
            subst q
            change (2 : ZMod 350870543412491)^76471190 ≠ 1
            reduce_mod_char
            decide

theorem prime_354233654641241 : Nat.Prime 354233654641241 := by
  apply lucas_primality 354233654641241 (3 : ZMod 354233654641241)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 354233654641241 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((941741 : ℕ)^1 * ((854881 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 354233654641241)^177116827320620 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 354233654641241)^70846730928248 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 354233654641241)^32203059512840 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 941741 := Nat.prime_eq_prime_of_dvd_pow hq prime_941741 hd
            subst q
            change (3 : ZMod 354233654641241)^376147640 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 854881 := Nat.prime_eq_prime_of_dvd_pow hq prime_854881 hd
            subst q
            change (3 : ZMod 354233654641241)^414366040 ≠ 1
            reduce_mod_char
            decide

theorem prime_362299361110619 : Nat.Prime 362299361110619 := by
  apply lucas_primality 362299361110619 (6 : ZMod 362299361110619)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 362299361110619 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((10655863562077 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 362299361110619)^181149680555309 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (6 : ZMod 362299361110619)^21311727124154 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 10655863562077 := Nat.prime_eq_prime_of_dvd_pow hq prime_10655863562077 hd
        subst q
        change (6 : ZMod 362299361110619)^34 ≠ 1
        reduce_mod_char
        decide

theorem prime_370517533364227 : Nat.Prime 370517533364227 := by
  apply lucas_primality 370517533364227 (2 : ZMod 370517533364227)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 370517533364227 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((59 : ℕ)^1 * ((4177 : ℕ)^1 * ((13931 : ℕ)^1 * ((17987 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 370517533364227)^185258766682113 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 370517533364227)^123505844454742 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (2 : ZMod 370517533364227)^6279958192614 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 4177 := Nat.prime_eq_prime_of_dvd_pow hq prime_4177 hd
            subst q
            change (2 : ZMod 370517533364227)^88704221538 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 13931 := Nat.prime_eq_prime_of_dvd_pow hq prime_13931 hd
              subst q
              change (2 : ZMod 370517533364227)^26596621446 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 17987 := Nat.prime_eq_prime_of_dvd_pow hq prime_17987 hd
              subst q
              change (2 : ZMod 370517533364227)^20599184598 ≠ 1
              reduce_mod_char
              decide

theorem prime_378350915984291 : Nat.Prime 378350915984291 := by
  apply lucas_primality 378350915984291 (2 : ZMod 378350915984291)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 378350915984291 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((2225593623437 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 378350915984291)^189175457992145 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 378350915984291)^75670183196858 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 378350915984291)^22255936234370 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2225593623437 := Nat.prime_eq_prime_of_dvd_pow hq prime_2225593623437 hd
          subst q
          change (2 : ZMod 378350915984291)^170 ≠ 1
          reduce_mod_char
          decide

theorem prime_378778403571209 : Nat.Prime 378778403571209 := by
  apply lucas_primality 378778403571209 (3 : ZMod 378778403571209)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 378778403571209 - 1 = (2 : ℕ)^3 * ((479 : ℕ)^1 * ((3623 : ℕ)^1 * ((27282953 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 378778403571209)^189389201785604 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 479 := Nat.prime_eq_prime_of_dvd_pow hq prime_479 hd
        subst q
        change (3 : ZMod 378778403571209)^790769109752 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 3623 := Nat.prime_eq_prime_of_dvd_pow hq prime_3623 hd
          subst q
          change (3 : ZMod 378778403571209)^104548275896 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 27282953 := Nat.prime_eq_prime_of_dvd_pow hq prime_27282953 hd
          subst q
          change (3 : ZMod 378778403571209)^13883336 ≠ 1
          reduce_mod_char
          decide

theorem prime_378890468381891 : Nat.Prime 378890468381891 := by
  apply lucas_primality 378890468381891 (2 : ZMod 378890468381891)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 378890468381891 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((113 : ℕ)^1 * ((26777 : ℕ)^1 * ((12521989 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 378890468381891)^189445234190945 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 378890468381891)^75778093676378 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
          subst q
          change (2 : ZMod 378890468381891)^3353012994530 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 26777 := Nat.prime_eq_prime_of_dvd_pow hq prime_26777 hd
            subst q
            change (2 : ZMod 378890468381891)^14149847570 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 12521989 := Nat.prime_eq_prime_of_dvd_pow hq prime_12521989 hd
            subst q
            change (2 : ZMod 378890468381891)^30258010 ≠ 1
            reduce_mod_char
            decide

theorem prime_382348919351039 : Nat.Prime 382348919351039 := by
  apply lucas_primality 382348919351039 (7 : ZMod 382348919351039)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 382348919351039 - 1 = (2 : ℕ)^1 * ((31 : ℕ)^1 * ((6166918054049 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 382348919351039)^191174459675519 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (7 : ZMod 382348919351039)^12333836108098 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 6166918054049 := Nat.prime_eq_prime_of_dvd_pow hq prime_6166918054049 hd
        subst q
        change (7 : ZMod 382348919351039)^62 ≠ 1
        reduce_mod_char
        decide

theorem prime_387420489000007 : Nat.Prime 387420489000007 := by
  apply lucas_primality 387420489000007 (5 : ZMod 387420489000007)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 387420489000007 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((838572487013 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 387420489000007)^193710244500003 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 387420489000007)^129140163000002 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 387420489000007)^55345784142858 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (5 : ZMod 387420489000007)^35220044454546 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 838572487013 := Nat.prime_eq_prime_of_dvd_pow hq prime_838572487013 hd
            subst q
            change (5 : ZMod 387420489000007)^462 ≠ 1
            reduce_mod_char
            decide

theorem prime_389240375013733 : Nat.Prime 389240375013733 := by
  apply lucas_primality 389240375013733 (2 : ZMod 389240375013733)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 389240375013733 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((329803 : ℕ)^1 * ((8941067 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 389240375013733)^194620187506866 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 389240375013733)^129746791671244 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 389240375013733)^35385488637612 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 329803 := Nat.prime_eq_prime_of_dvd_pow hq prime_329803 hd
            subst q
            change (2 : ZMod 389240375013733)^1180220844 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 8941067 := Nat.prime_eq_prime_of_dvd_pow hq prime_8941067 hd
            subst q
            change (2 : ZMod 389240375013733)^43533996 ≠ 1
            reduce_mod_char
            decide

theorem prime_392369146902877 : Nat.Prime 392369146902877 := by
  apply lucas_primality 392369146902877 (14 : ZMod 392369146902877)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 392369146902877 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((13 : ℕ)^1 * ((23 : ℕ)^1 * ((32191 : ℕ)^1 * ((308827 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 392369146902877)^196184573451438 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 392369146902877)^130789715634292 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (14 : ZMod 392369146902877)^35669922445716 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (14 : ZMod 392369146902877)^30182242069452 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
              subst q
              change (14 : ZMod 392369146902877)^17059528126212 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 32191 := Nat.prime_eq_prime_of_dvd_pow hq prime_32191 hd
                subst q
                change (14 : ZMod 392369146902877)^12188784036 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 308827 := Nat.prime_eq_prime_of_dvd_pow hq prime_308827 hd
                subst q
                change (14 : ZMod 392369146902877)^1270514388 ≠ 1
                reduce_mod_char
                decide

theorem prime_396109944105193 : Nat.Prime 396109944105193 := by
  apply lucas_primality 396109944105193 (5 : ZMod 396109944105193)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 396109944105193 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^2 * ((292549 : ℕ)^1 * ((18805489 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 396109944105193)^198054972052596 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 396109944105193)^132036648035064 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 292549 := Nat.prime_eq_prime_of_dvd_pow hq prime_292549 hd
          subst q
          change (5 : ZMod 396109944105193)^1353995208 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 18805489 := Nat.prime_eq_prime_of_dvd_pow hq prime_18805489 hd
          subst q
          change (5 : ZMod 396109944105193)^21063528 ≠ 1
          reduce_mod_char
          decide

theorem prime_404961208827907 : Nat.Prime 404961208827907 := by
  apply lucas_primality 404961208827907 (2 : ZMod 404961208827907)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 404961208827907 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((75833 : ℕ)^1 * ((890028547 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 404961208827907)^202480604413953 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 404961208827907)^134987069609302 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 75833 := Nat.prime_eq_prime_of_dvd_pow hq prime_75833 hd
          subst q
          change (2 : ZMod 404961208827907)^5340171282 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 890028547 := Nat.prime_eq_prime_of_dvd_pow hq prime_890028547 hd
          subst q
          change (2 : ZMod 404961208827907)^454998 ≠ 1
          reduce_mod_char
          decide

theorem prime_410564909654017 : Nat.Prime 410564909654017 := by
  apply lucas_primality 410564909654017 (5 : ZMod 410564909654017)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 410564909654017 - 1 = (2 : ℕ)^13 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((37 : ℕ)^1 * ((67 : ℕ)^1 * ((151 : ℕ)^1 * ((3433 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 410564909654017)^205282454827008 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 410564909654017)^136854969884672 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (5 : ZMod 410564909654017)^31581916127232 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
            subst q
            change (5 : ZMod 410564909654017)^11096348909568 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
              subst q
              change (5 : ZMod 410564909654017)^6127834472448 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
                subst q
                change (5 : ZMod 410564909654017)^2718972911616 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 3433 := Nat.prime_eq_prime_of_dvd_pow hq prime_3433 hd
                subst q
                change (5 : ZMod 410564909654017)^119593623552 ≠ 1
                reduce_mod_char
                decide

theorem prime_413976684738037 : Nat.Prime 413976684738037 := by
  apply lucas_primality 413976684738037 (2 : ZMod 413976684738037)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 413976684738037 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((97 : ℕ)^1 * ((7258164751 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 413976684738037)^206988342369018 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 413976684738037)^137992228246012 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 413976684738037)^59139526391148 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
            subst q
            change (2 : ZMod 413976684738037)^4267800873588 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 7258164751 := Nat.prime_eq_prime_of_dvd_pow hq prime_7258164751 hd
            subst q
            change (2 : ZMod 413976684738037)^57036 ≠ 1
            reduce_mod_char
            decide

theorem prime_417913628078321 : Nat.Prime 417913628078321 := by
  apply lucas_primality 417913628078321 (12 : ZMod 417913628078321)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 417913628078321 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((31 : ℕ)^1 * ((727 : ℕ)^1 * ((4519 : ℕ)^1 * ((4663 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (12 : ZMod 417913628078321)^208956814039160 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (12 : ZMod 417913628078321)^83582725615664 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (12 : ZMod 417913628078321)^37992148007120 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
            subst q
            change (12 : ZMod 417913628078321)^13481084776720 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 727 := Nat.prime_eq_prime_of_dvd_pow hq prime_727 hd
              subst q
              change (12 : ZMod 417913628078321)^574846806160 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 4519 := Nat.prime_eq_prime_of_dvd_pow hq prime_4519 hd
                subst q
                change (12 : ZMod 417913628078321)^92479227280 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 4663 := Nat.prime_eq_prime_of_dvd_pow hq prime_4663 hd
                subst q
                change (12 : ZMod 417913628078321)^89623338640 ≠ 1
                reduce_mod_char
                decide

theorem prime_423158800039007 : Nat.Prime 423158800039007 := by
  apply lucas_primality 423158800039007 (5 : ZMod 423158800039007)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 423158800039007 - 1 = (2 : ℕ)^1 * ((31 : ℕ)^1 * ((131 : ℕ)^1 * ((1249 : ℕ)^1 * ((41713627 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 423158800039007)^211579400019503 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (5 : ZMod 423158800039007)^13650283872226 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
          subst q
          change (5 : ZMod 423158800039007)^3230219847626 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1249 := Nat.prime_eq_prime_of_dvd_pow hq prime_1249 hd
            subst q
            change (5 : ZMod 423158800039007)^338798078494 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 41713627 := Nat.prime_eq_prime_of_dvd_pow hq prime_41713627 hd
            subst q
            change (5 : ZMod 423158800039007)^10144378 ≠ 1
            reduce_mod_char
            decide

theorem prime_432510009765643 : Nat.Prime 432510009765643 := by
  apply lucas_primality 432510009765643 (2 : ZMod 432510009765643)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 432510009765643 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((79 : ℕ)^1 * ((131 : ℕ)^1 * ((163 : ℕ)^1 * ((769 : ℕ)^1 * ((18523 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 432510009765643)^216255004882821 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 432510009765643)^144170003255214 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (2 : ZMod 432510009765643)^5474810250198 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
            subst q
            change (2 : ZMod 432510009765643)^3301603127982 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 163 := Nat.prime_eq_prime_of_dvd_pow hq prime_163 hd
              subst q
              change (2 : ZMod 432510009765643)^2653435642734 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 769 := Nat.prime_eq_prime_of_dvd_pow hq prime_769 hd
                subst q
                change (2 : ZMod 432510009765643)^562431742218 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 18523 := Nat.prime_eq_prime_of_dvd_pow hq prime_18523 hd
                subst q
                change (2 : ZMod 432510009765643)^23349889854 ≠ 1
                reduce_mod_char
                decide

theorem prime_441728078160937 : Nat.Prime 441728078160937 := by
  apply lucas_primality 441728078160937 (5 : ZMod 441728078160937)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 441728078160937 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((2629333798577 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 441728078160937)^220864039080468 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 441728078160937)^147242692720312 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 441728078160937)^63104011165848 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2629333798577 := Nat.prime_eq_prime_of_dvd_pow hq prime_2629333798577 hd
          subst q
          change (5 : ZMod 441728078160937)^168 ≠ 1
          reduce_mod_char
          decide

theorem prime_442032795979781 : Nat.Prime 442032795979781 := by
  apply lucas_primality 442032795979781 (2 : ZMod 442032795979781)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 442032795979781 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((22101639798989 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 442032795979781)^221016397989890 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 442032795979781)^88406559195956 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 22101639798989 := Nat.prime_eq_prime_of_dvd_pow hq prime_22101639798989 hd
        subst q
        change (2 : ZMod 442032795979781)^20 ≠ 1
        reduce_mod_char
        decide

theorem prime_449416402916791 : Nat.Prime 449416402916791 := by
  apply lucas_primality 449416402916791 (7 : ZMod 449416402916791)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 449416402916791 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((2111 : ℕ)^1 * ((10847 : ℕ)^1 * ((654229 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 449416402916791)^224708201458395 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 449416402916791)^149805467638930 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (7 : ZMod 449416402916791)^89883280583358 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2111 := Nat.prime_eq_prime_of_dvd_pow hq prime_2111 hd
            subst q
            change (7 : ZMod 449416402916791)^212892658890 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 10847 := Nat.prime_eq_prime_of_dvd_pow hq prime_10847 hd
              subst q
              change (7 : ZMod 449416402916791)^41432322570 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 654229 := Nat.prime_eq_prime_of_dvd_pow hq prime_654229 hd
              subst q
              change (7 : ZMod 449416402916791)^686940510 ≠ 1
              reduce_mod_char
              decide

theorem prime_451729667968543 : Nat.Prime 451729667968543 := by
  apply lucas_primality 451729667968543 (3 : ZMod 451729667968543)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 451729667968543 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((25096092664919 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 451729667968543)^225864833984271 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 451729667968543)^150576555989514 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 25096092664919 := Nat.prime_eq_prime_of_dvd_pow hq prime_25096092664919 hd
        subst q
        change (3 : ZMod 451729667968543)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_461603162442329 : Nat.Prime 461603162442329 := by
  apply lucas_primality 461603162442329 (3 : ZMod 461603162442329)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 461603162442329 - 1 = (2 : ℕ)^3 * ((367 : ℕ)^1 * ((157221785573 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 461603162442329)^230801581221164 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 367 := Nat.prime_eq_prime_of_dvd_pow hq prime_367 hd
        subst q
        change (3 : ZMod 461603162442329)^1257774284584 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 157221785573 := Nat.prime_eq_prime_of_dvd_pow hq prime_157221785573 hd
        subst q
        change (3 : ZMod 461603162442329)^2936 ≠ 1
        reduce_mod_char
        decide

theorem prime_471655843734337 : Nat.Prime 471655843734337 := by
  apply lucas_primality 471655843734337 (5 : ZMod 471655843734337)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 471655843734337 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^1 * ((53 : ℕ)^1 * ((257 : ℕ)^1 * ((2063 : ℕ)^1 * ((87421 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 471655843734337)^235827921867168 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 471655843734337)^157218614578112 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (5 : ZMod 471655843734337)^8899166862912 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 257 := Nat.prime_eq_prime_of_dvd_pow hq prime_257 hd
            subst q
            change (5 : ZMod 471655843734337)^1835236746048 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 2063 := Nat.prime_eq_prime_of_dvd_pow hq prime_2063 hd
              subst q
              change (5 : ZMod 471655843734337)^228626196672 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 87421 := Nat.prime_eq_prime_of_dvd_pow hq prime_87421 hd
              subst q
              change (5 : ZMod 471655843734337)^5395223616 ≠ 1
              reduce_mod_char
              decide

theorem prime_481890304000037 : Nat.Prime 481890304000037 := by
  apply lucas_primality 481890304000037 (2 : ZMod 481890304000037)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 481890304000037 - 1 = (2 : ℕ)^2 * ((29 : ℕ)^1 * ((1453 : ℕ)^1 * ((2859068657 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 481890304000037)^240945152000018 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (2 : ZMod 481890304000037)^16616907034484 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1453 := Nat.prime_eq_prime_of_dvd_pow hq prime_1453 hd
          subst q
          change (2 : ZMod 481890304000037)^331651964212 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2859068657 := Nat.prime_eq_prime_of_dvd_pow hq prime_2859068657 hd
          subst q
          change (2 : ZMod 481890304000037)^168548 ≠ 1
          reduce_mod_char
          decide

theorem prime_490243350119723 : Nat.Prime 490243350119723 := by
  apply lucas_primality 490243350119723 (2 : ZMod 490243350119723)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 490243350119723 - 1 = (2 : ℕ)^1 * ((37 : ℕ)^1 * ((6624910136753 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 490243350119723)^245121675059861 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (2 : ZMod 490243350119723)^13249820273506 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 6624910136753 := Nat.prime_eq_prime_of_dvd_pow hq prime_6624910136753 hd
        subst q
        change (2 : ZMod 490243350119723)^74 ≠ 1
        reduce_mod_char
        decide

theorem prime_492309163417717 : Nat.Prime 492309163417717 := by
  apply lucas_primality 492309163417717 (5 : ZMod 492309163417717)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 492309163417717 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((577 : ℕ)^1 * ((15217 : ℕ)^1 * ((1557509 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 492309163417717)^246154581708858 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 492309163417717)^164103054472572 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 577 := Nat.prime_eq_prime_of_dvd_pow hq prime_577 hd
          subst q
          change (5 : ZMod 492309163417717)^853222120308 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 15217 := Nat.prime_eq_prime_of_dvd_pow hq prime_15217 hd
            subst q
            change (5 : ZMod 492309163417717)^32352576948 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1557509 := Nat.prime_eq_prime_of_dvd_pow hq prime_1557509 hd
            subst q
            change (5 : ZMod 492309163417717)^316087524 ≠ 1
            reduce_mod_char
            decide

theorem prime_502915070389847 : Nat.Prime 502915070389847 := by
  apply lucas_primality 502915070389847 (5 : ZMod 502915070389847)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 502915070389847 - 1 = (2 : ℕ)^1 * ((97 : ℕ)^1 * ((2592345723659 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 502915070389847)^251457535194923 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
        subst q
        change (5 : ZMod 502915070389847)^5184691447318 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 2592345723659 := Nat.prime_eq_prime_of_dvd_pow hq prime_2592345723659 hd
        subst q
        change (5 : ZMod 502915070389847)^194 ≠ 1
        reduce_mod_char
        decide

theorem prime_504720186407159 : Nat.Prime 504720186407159 := by
  apply lucas_primality 504720186407159 (7 : ZMod 504720186407159)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 504720186407159 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((569 : ℕ)^1 * ((131701 : ℕ)^1 * ((146417 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 504720186407159)^252360093203579 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (7 : ZMod 504720186407159)^21944355930746 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 569 := Nat.prime_eq_prime_of_dvd_pow hq prime_569 hd
          subst q
          change (7 : ZMod 504720186407159)^887030204582 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 131701 := Nat.prime_eq_prime_of_dvd_pow hq prime_131701 hd
            subst q
            change (7 : ZMod 504720186407159)^3832318558 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 146417 := Nat.prime_eq_prime_of_dvd_pow hq prime_146417 hd
            subst q
            change (7 : ZMod 504720186407159)^3447141974 ≠ 1
            reduce_mod_char
            decide

theorem prime_513710701744979 : Nat.Prime 513710701744979 := by
  apply lucas_primality 513710701744979 (2 : ZMod 513710701744979)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 513710701744979 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((293 : ℕ)^1 * ((51567024869 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 513710701744979)^256855350872489 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 513710701744979)^30218276573234 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 293 := Nat.prime_eq_prime_of_dvd_pow hq prime_293 hd
          subst q
          change (2 : ZMod 513710701744979)^1753278845546 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 51567024869 := Nat.prime_eq_prime_of_dvd_pow hq prime_51567024869 hd
          subst q
          change (2 : ZMod 513710701744979)^9962 ≠ 1
          reduce_mod_char
          decide

theorem prime_519887451519727 : Nat.Prime 519887451519727 := by
  apply lucas_primality 519887451519727 (5 : ZMod 519887451519727)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 519887451519727 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((4283 : ℕ)^1 * ((1190038711 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 519887451519727)^259943725759863 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 519887451519727)^173295817173242 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (5 : ZMod 519887451519727)^30581614795278 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 4283 := Nat.prime_eq_prime_of_dvd_pow hq prime_4283 hd
            subst q
            change (5 : ZMod 519887451519727)^121383948522 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1190038711 := Nat.prime_eq_prime_of_dvd_pow hq prime_1190038711 hd
            subst q
            change (5 : ZMod 519887451519727)^436866 ≠ 1
            reduce_mod_char
            decide

theorem prime_524698762940423 : Nat.Prime 524698762940423 := by
  apply lucas_primality 524698762940423 (5 : ZMod 524698762940423)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 524698762940423 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((166273 : ℕ)^1 * ((225403301 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 524698762940423)^262349381470211 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (5 : ZMod 524698762940423)^74956966134346 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 166273 := Nat.prime_eq_prime_of_dvd_pow hq prime_166273 hd
          subst q
          change (5 : ZMod 524698762940423)^3155646214 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 225403301 := Nat.prime_eq_prime_of_dvd_pow hq prime_225403301 hd
          subst q
          change (5 : ZMod 524698762940423)^2327822 ≠ 1
          reduce_mod_char
          decide

theorem prime_535342029468773 : Nat.Prime 535342029468773 := by
  apply lucas_primality 535342029468773 (2 : ZMod 535342029468773)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 535342029468773 - 1 = (2 : ℕ)^2 * ((37 : ℕ)^1 * ((3617175874789 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 535342029468773)^267671014734386 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
        subst q
        change (2 : ZMod 535342029468773)^14468703499156 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3617175874789 := Nat.prime_eq_prime_of_dvd_pow hq prime_3617175874789 hd
        subst q
        change (2 : ZMod 535342029468773)^148 ≠ 1
        reduce_mod_char
        decide

theorem prime_535881988265629 : Nat.Prime 535881988265629 := by
  apply lucas_primality 535881988265629 (6 : ZMod 535881988265629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 535881988265629 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5760961 : ℕ)^1 * ((7751629 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 535881988265629)^267940994132814 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 535881988265629)^178627329421876 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5760961 := Nat.prime_eq_prime_of_dvd_pow hq prime_5760961 hd
          subst q
          change (6 : ZMod 535881988265629)^93019548 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7751629 := Nat.prime_eq_prime_of_dvd_pow hq prime_7751629 hd
          subst q
          change (6 : ZMod 535881988265629)^69131532 ≠ 1
          reduce_mod_char
          decide

theorem prime_547016213249021 : Nat.Prime 547016213249021 := by
  apply lucas_primality 547016213249021 (2 : ZMod 547016213249021)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 547016213249021 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((53 : ℕ)^1 * ((34877 : ℕ)^1 * ((14796371 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 547016213249021)^273508106624510 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 547016213249021)^109403242649804 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (2 : ZMod 547016213249021)^10321060627340 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 34877 := Nat.prime_eq_prime_of_dvd_pow hq prime_34877 hd
            subst q
            change (2 : ZMod 547016213249021)^15684153260 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 14796371 := Nat.prime_eq_prime_of_dvd_pow hq prime_14796371 hd
            subst q
            change (2 : ZMod 547016213249021)^36969620 ≠ 1
            reduce_mod_char
            decide

theorem prime_547263141046357 : Nat.Prime 547263141046357 := by
  apply lucas_primality 547263141046357 (2 : ZMod 547263141046357)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 547263141046357 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((863 : ℕ)^1 * ((7549290143 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 547263141046357)^273631570523178 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 547263141046357)^182421047015452 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 547263141046357)^78180448720908 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 863 := Nat.prime_eq_prime_of_dvd_pow hq prime_863 hd
            subst q
            change (2 : ZMod 547263141046357)^634140372012 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 7549290143 := Nat.prime_eq_prime_of_dvd_pow hq prime_7549290143 hd
            subst q
            change (2 : ZMod 547263141046357)^72492 ≠ 1
            reduce_mod_char
            decide

theorem prime_558845013849439 : Nat.Prime 558845013849439 := by
  apply lucas_primality 558845013849439 (3 : ZMod 558845013849439)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 558845013849439 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((1109 : ℕ)^1 * ((59341 : ℕ)^1 * ((1415317 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 558845013849439)^279422506924719 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 558845013849439)^186281671283146 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1109 := Nat.prime_eq_prime_of_dvd_pow hq prime_1109 hd
          subst q
          change (3 : ZMod 558845013849439)^503917956582 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 59341 := Nat.prime_eq_prime_of_dvd_pow hq prime_59341 hd
            subst q
            change (3 : ZMod 558845013849439)^9417519318 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1415317 := Nat.prime_eq_prime_of_dvd_pow hq prime_1415317 hd
            subst q
            change (3 : ZMod 558845013849439)^394855014 ≠ 1
            reduce_mod_char
            decide

theorem prime_565616225023249 : Nat.Prime 565616225023249 := by
  apply lucas_primality 565616225023249 (17 : ZMod 565616225023249)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 565616225023249 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((827 : ℕ)^1 * ((4507 : ℕ)^1 * ((451637 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 565616225023249)^282808112511624 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 565616225023249)^188538741674416 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (17 : ZMod 565616225023249)^80802317860464 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 827 := Nat.prime_eq_prime_of_dvd_pow hq prime_827 hd
            subst q
            change (17 : ZMod 565616225023249)^683937394224 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 4507 := Nat.prime_eq_prime_of_dvd_pow hq prime_4507 hd
              subst q
              change (17 : ZMod 565616225023249)^125497276464 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 451637 := Nat.prime_eq_prime_of_dvd_pow hq prime_451637 hd
              subst q
              change (17 : ZMod 565616225023249)^1252369104 ≠ 1
              reduce_mod_char
              decide

theorem prime_570630428688391 : Nat.Prime 570630428688391 := by
  apply lucas_primality 570630428688391 (3 : ZMod 570630428688391)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 570630428688391 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((12491 : ℕ)^1 * ((217539649 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 570630428688391)^285315214344195 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 570630428688391)^190210142896130 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 570630428688391)^114126085737678 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (3 : ZMod 570630428688391)^81518632669770 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 12491 := Nat.prime_eq_prime_of_dvd_pow hq prime_12491 hd
              subst q
              change (3 : ZMod 570630428688391)^45683326290 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 217539649 := Nat.prime_eq_prime_of_dvd_pow hq prime_217539649 hd
              subst q
              change (3 : ZMod 570630428688391)^2623110 ≠ 1
              reduce_mod_char
              decide

theorem prime_582622237229771 : Nat.Prime 582622237229771 := by
  apply lucas_primality 582622237229771 (2 : ZMod 582622237229771)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 582622237229771 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((577 : ℕ)^1 * ((195077 : ℕ)^1 * ((517613 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 582622237229771)^291311118614885 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 582622237229771)^116524447445954 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 577 := Nat.prime_eq_prime_of_dvd_pow hq prime_577 hd
          subst q
          change (2 : ZMod 582622237229771)^1009743912010 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 195077 := Nat.prime_eq_prime_of_dvd_pow hq prime_195077 hd
            subst q
            change (2 : ZMod 582622237229771)^2986627010 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 517613 := Nat.prime_eq_prime_of_dvd_pow hq prime_517613 hd
            subst q
            change (2 : ZMod 582622237229771)^1125594290 ≠ 1
            reduce_mod_char
            decide

theorem prime_594823321000019 : Nat.Prime 594823321000019 := by
  apply lucas_primality 594823321000019 (6 : ZMod 594823321000019)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 594823321000019 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((211 : ℕ)^1 * ((138403 : ℕ)^1 * ((925843 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 594823321000019)^297411660500009 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (6 : ZMod 594823321000019)^54074847363638 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 211 := Nat.prime_eq_prime_of_dvd_pow hq prime_211 hd
          subst q
          change (6 : ZMod 594823321000019)^2819067872038 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 138403 := Nat.prime_eq_prime_of_dvd_pow hq prime_138403 hd
            subst q
            change (6 : ZMod 594823321000019)^4297763206 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 925843 := Nat.prime_eq_prime_of_dvd_pow hq prime_925843 hd
            subst q
            change (6 : ZMod 594823321000019)^642466726 ≠ 1
            reduce_mod_char
            decide

theorem prime_607236591593257 : Nat.Prime 607236591593257 := by
  apply lucas_primality 607236591593257 (5 : ZMod 607236591593257)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 607236591593257 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((353 : ℕ)^1 * ((71675707223 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 607236591593257)^303618295796628 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 607236591593257)^202412197197752 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 353 := Nat.prime_eq_prime_of_dvd_pow hq prime_353 hd
          subst q
          change (5 : ZMod 607236591593257)^1720216973352 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 71675707223 := Nat.prime_eq_prime_of_dvd_pow hq prime_71675707223 hd
          subst q
          change (5 : ZMod 607236591593257)^8472 ≠ 1
          reduce_mod_char
          decide

theorem prime_619864990879751 : Nat.Prime 619864990879751 := by
  apply lucas_primality 619864990879751 (13 : ZMod 619864990879751)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 619864990879751 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^3 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((23189 : ℕ)^1 * ((1388623 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 619864990879751)^309932495439875 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (13 : ZMod 619864990879751)^123972998175950 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (13 : ZMod 619864990879751)^88552141554250 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (13 : ZMod 619864990879751)^56351362807250 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 23189 := Nat.prime_eq_prime_of_dvd_pow hq prime_23189 hd
              subst q
              change (13 : ZMod 619864990879751)^26730992750 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1388623 := Nat.prime_eq_prime_of_dvd_pow hq prime_1388623 hd
              subst q
              change (13 : ZMod 619864990879751)^446388250 ≠ 1
              reduce_mod_char
              decide

theorem prime_632711491215073 : Nat.Prime 632711491215073 := by
  apply lucas_primality 632711491215073 (5 : ZMod 632711491215073)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 632711491215073 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((31 : ℕ)^1 * ((15173 : ℕ)^1 * ((14012039 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 632711491215073)^316355745607536 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 632711491215073)^210903830405024 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (5 : ZMod 632711491215073)^20410048103712 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 15173 := Nat.prime_eq_prime_of_dvd_pow hq prime_15173 hd
            subst q
            change (5 : ZMod 632711491215073)^41699828064 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 14012039 := Nat.prime_eq_prime_of_dvd_pow hq prime_14012039 hd
            subst q
            change (5 : ZMod 632711491215073)^45154848 ≠ 1
            reduce_mod_char
            decide

theorem prime_645779095649869 : Nat.Prime 645779095649869 := by
  apply lucas_primality 645779095649869 (2 : ZMod 645779095649869)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 645779095649869 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((42187 : ℕ)^1 * ((1275628147 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 645779095649869)^322889547824934 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 645779095649869)^215259698549956 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 42187 := Nat.prime_eq_prime_of_dvd_pow hq prime_42187 hd
          subst q
          change (2 : ZMod 645779095649869)^15307537764 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1275628147 := Nat.prime_eq_prime_of_dvd_pow hq prime_1275628147 hd
          subst q
          change (2 : ZMod 645779095649869)^506244 ≠ 1
          reduce_mod_char
          decide

theorem prime_659070838140647 : Nat.Prime 659070838140647 := by
  apply lucas_primality 659070838140647 (5 : ZMod 659070838140647)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 659070838140647 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((1531 : ℕ)^1 * ((133769 : ℕ)^1 * ((69959 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 659070838140647)^329535419070323 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (5 : ZMod 659070838140647)^28655253832202 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1531 := Nat.prime_eq_prime_of_dvd_pow hq prime_1531 hd
          subst q
          change (5 : ZMod 659070838140647)^430483891666 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 133769 := Nat.prime_eq_prime_of_dvd_pow hq prime_133769 hd
            subst q
            change (5 : ZMod 659070838140647)^4926932534 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 69959 := Nat.prime_eq_prime_of_dvd_pow hq prime_69959 hd
            subst q
            change (5 : ZMod 659070838140647)^9420815594 ≠ 1
            reduce_mod_char
            decide

theorem prime_672589783760911 : Nat.Prime 672589783760911 := by
  apply lucas_primality 672589783760911 (14 : ZMod 672589783760911)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 672589783760911 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((3823 : ℕ)^1 * ((27241 : ℕ)^1 * ((215279 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (14 : ZMod 672589783760911)^336294891880455 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (14 : ZMod 672589783760911)^224196594586970 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (14 : ZMod 672589783760911)^134517956752182 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3823 := Nat.prime_eq_prime_of_dvd_pow hq prime_3823 hd
            subst q
            change (14 : ZMod 672589783760911)^175932457170 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 27241 := Nat.prime_eq_prime_of_dvd_pow hq prime_27241 hd
              subst q
              change (14 : ZMod 672589783760911)^24690348510 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 215279 := Nat.prime_eq_prime_of_dvd_pow hq prime_215279 hd
              subst q
              change (14 : ZMod 672589783760911)^3124270290 ≠ 1
              reduce_mod_char
              decide

theorem prime_686339028913387 : Nat.Prime 686339028913387 := by
  apply lucas_primality 686339028913387 (5 : ZMod 686339028913387)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 686339028913387 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((251 : ℕ)^1 * ((331 : ℕ)^1 * ((28573 : ℕ)^1 * ((48187 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 686339028913387)^343169514456693 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 686339028913387)^228779676304462 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 251 := Nat.prime_eq_prime_of_dvd_pow hq prime_251 hd
          subst q
          change (5 : ZMod 686339028913387)^2734418441886 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 331 := Nat.prime_eq_prime_of_dvd_pow hq prime_331 hd
            subst q
            change (5 : ZMod 686339028913387)^2073531809406 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 28573 := Nat.prime_eq_prime_of_dvd_pow hq prime_28573 hd
              subst q
              change (5 : ZMod 686339028913387)^24020544882 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 48187 := Nat.prime_eq_prime_of_dvd_pow hq prime_48187 hd
              subst q
              change (5 : ZMod 686339028913387)^14243240478 ≠ 1
              reduce_mod_char
              decide

theorem prime_700321701542501 : Nat.Prime 700321701542501 := by
  apply lucas_primality 700321701542501 (3 : ZMod 700321701542501)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 700321701542501 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^4 * ((280128680617 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 700321701542501)^350160850771250 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 700321701542501)^140064340308500 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 280128680617 := Nat.prime_eq_prime_of_dvd_pow hq prime_280128680617 hd
        subst q
        change (3 : ZMod 700321701542501)^2500 ≠ 1
        reduce_mod_char
        decide

theorem prime_705019561361221 : Nat.Prime 705019561361221 := by
  apply lucas_primality 705019561361221 (2 : ZMod 705019561361221)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 705019561361221 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((53 : ℕ)^1 * ((2039 : ℕ)^1 * ((3863 : ℕ)^1 * ((4021 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 705019561361221)^352509780680610 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 705019561361221)^235006520453740 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 705019561361221)^141003912272244 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (2 : ZMod 705019561361221)^100717080194460 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
              subst q
              change (2 : ZMod 705019561361221)^13302255874740 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 2039 := Nat.prime_eq_prime_of_dvd_pow hq prime_2039 hd
                subst q
                change (2 : ZMod 705019561361221)^345767317980 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 3863 := Nat.prime_eq_prime_of_dvd_pow hq prime_3863 hd
                  subst q
                  change (2 : ZMod 705019561361221)^182505710940 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 4021 := Nat.prime_eq_prime_of_dvd_pow hq prime_4021 hd
                  subst q
                  change (2 : ZMod 705019561361221)^175334384820 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_706426655801353 : Nat.Prime 706426655801353 := by
  apply lucas_primality 706426655801353 (10 : ZMod 706426655801353)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 706426655801353 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((29434443991723 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 706426655801353)^353213327900676 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 706426655801353)^235475551933784 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 29434443991723 := Nat.prime_eq_prime_of_dvd_pow hq prime_29434443991723 hd
        subst q
        change (10 : ZMod 706426655801353)^24 ≠ 1
        reduce_mod_char
        decide

theorem prime_714540961348229 : Nat.Prime 714540961348229 := by
  apply lucas_primality 714540961348229 (2 : ZMod 714540961348229)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 714540961348229 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((31 : ℕ)^1 * ((67 : ℕ)^1 * ((73 : ℕ)^1 * ((103 : ℕ)^1 * ((1237 : ℕ)^1 * ((1321 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 714540961348229)^357270480674114 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 714540961348229)^102077280192604 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (2 : ZMod 714540961348229)^23049708430588 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
            subst q
            change (2 : ZMod 714540961348229)^10664790467884 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
              subst q
              change (2 : ZMod 714540961348229)^9788232347236 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
                subst q
                change (2 : ZMod 714540961348229)^6937290886876 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 1237 := Nat.prime_eq_prime_of_dvd_pow hq prime_1237 hd
                  subst q
                  change (2 : ZMod 714540961348229)^577640227444 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 1321 := Nat.prime_eq_prime_of_dvd_pow hq prime_1321 hd
                  subst q
                  change (2 : ZMod 714540961348229)^540909130468 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_729000000000023 : Nat.Prime 729000000000023 := by
  apply lucas_primality 729000000000023 (5 : ZMod 729000000000023)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 729000000000023 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^1 * ((97 : ℕ)^1 * ((163379650381 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 729000000000023)^364500000000011 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (5 : ZMod 729000000000023)^31695652173914 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
          subst q
          change (5 : ZMod 729000000000023)^7515463917526 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 163379650381 := Nat.prime_eq_prime_of_dvd_pow hq prime_163379650381 hd
          subst q
          change (5 : ZMod 729000000000023)^4462 ≠ 1
          reduce_mod_char
          decide

theorem prime_743702041351849 : Nat.Prime 743702041351849 := by
  apply lucas_primality 743702041351849 (7 : ZMod 743702041351849)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 743702041351849 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((83 : ℕ)^1 * ((709 : ℕ)^1 * ((526578841 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 743702041351849)^371851020675924 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 743702041351849)^247900680450616 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
          subst q
          change (7 : ZMod 743702041351849)^8960265558456 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 709 := Nat.prime_eq_prime_of_dvd_pow hq prime_709 hd
            subst q
            change (7 : ZMod 743702041351849)^1048945051272 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 526578841 := Nat.prime_eq_prime_of_dvd_pow hq prime_526578841 hd
            subst q
            change (7 : ZMod 743702041351849)^1412328 ≠ 1
            reduce_mod_char
            decide

theorem prime_751785954026467 : Nat.Prime 751785954026467 := by
  apply lucas_primality 751785954026467 (2 : ZMod 751785954026467)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 751785954026467 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((113 : ℕ)^1 * ((28867 : ℕ)^1 * ((38411641 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 751785954026467)^375892977013233 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 751785954026467)^250595318008822 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
          subst q
          change (2 : ZMod 751785954026467)^6652973044482 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 28867 := Nat.prime_eq_prime_of_dvd_pow hq prime_28867 hd
            subst q
            change (2 : ZMod 751785954026467)^26043092598 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 38411641 := Nat.prime_eq_prime_of_dvd_pow hq prime_38411641 hd
            subst q
            change (2 : ZMod 751785954026467)^19571826 ≠ 1
            reduce_mod_char
            decide

theorem prime_753135963918889 : Nat.Prime 753135963918889 := by
  apply lucas_primality 753135963918889 (7 : ZMod 753135963918889)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 753135963918889 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((2546293 : ℕ)^1 * ((1120369 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 753135963918889)^376567981959444 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 753135963918889)^251045321306296 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (7 : ZMod 753135963918889)^68466905810808 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2546293 := Nat.prime_eq_prime_of_dvd_pow hq prime_2546293 hd
            subst q
            change (7 : ZMod 753135963918889)^295777416 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1120369 := Nat.prime_eq_prime_of_dvd_pow hq prime_1120369 hd
            subst q
            change (7 : ZMod 753135963918889)^672221352 ≠ 1
            reduce_mod_char
            decide

theorem prime_758650341657737 : Nat.Prime 758650341657737 := by
  apply lucas_primality 758650341657737 (5 : ZMod 758650341657737)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 758650341657737 - 1 = (2 : ℕ)^3 * ((11 : ℕ)^1 * ((137 : ℕ)^1 * ((353 : ℕ)^1 * ((523 : ℕ)^1 * ((340849 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 758650341657737)^379325170828868 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 758650341657737)^68968212877976 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
          subst q
          change (5 : ZMod 758650341657737)^5537593734728 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 353 := Nat.prime_eq_prime_of_dvd_pow hq prime_353 hd
            subst q
            change (5 : ZMod 758650341657737)^2149151109512 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 523 := Nat.prime_eq_prime_of_dvd_pow hq prime_523 hd
              subst q
              change (5 : ZMod 758650341657737)^1450574267032 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 340849 := Nat.prime_eq_prime_of_dvd_pow hq prime_340849 hd
              subst q
              change (5 : ZMod 758650341657737)^2225766664 ≠ 1
              reduce_mod_char
              decide

theorem prime_773848189788133 : Nat.Prime 773848189788133 := by
  apply lucas_primality 773848189788133 (5 : ZMod 773848189788133)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 773848189788133 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((73 : ℕ)^1 * ((103 : ℕ)^1 * ((85717 : ℕ)^1 * ((100057 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 773848189788133)^386924094894066 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 773848189788133)^257949396596044 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
          subst q
          change (5 : ZMod 773848189788133)^10600660134084 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 103 := Nat.prime_eq_prime_of_dvd_pow hq prime_103 hd
            subst q
            change (5 : ZMod 773848189788133)^7513089221244 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 85717 := Nat.prime_eq_prime_of_dvd_pow hq prime_85717 hd
              subst q
              change (5 : ZMod 773848189788133)^9027942996 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 100057 := Nat.prime_eq_prime_of_dvd_pow hq prime_100057 hd
              subst q
              change (5 : ZMod 773848189788133)^7734073476 ≠ 1
              reduce_mod_char
              decide

theorem prime_789101106720193 : Nat.Prime 789101106720193 := by
  apply lucas_primality 789101106720193 (5 : ZMod 789101106720193)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 789101106720193 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((191 : ℕ)^1 * ((6967 : ℕ)^1 * ((147073 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 789101106720193)^394550553360096 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 789101106720193)^263033702240064 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 789101106720193)^112728729531456 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 191 := Nat.prime_eq_prime_of_dvd_pow hq prime_191 hd
            subst q
            change (5 : ZMod 789101106720193)^4131419406912 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 6967 := Nat.prime_eq_prime_of_dvd_pow hq prime_6967 hd
              subst q
              change (5 : ZMod 789101106720193)^113262682176 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 147073 := Nat.prime_eq_prime_of_dvd_pow hq prime_147073 hd
              subst q
              change (5 : ZMod 789101106720193)^5365370304 ≠ 1
              reduce_mod_char
              decide

theorem prime_789298907447299 : Nat.Prime 789298907447299 := by
  apply lucas_primality 789298907447299 (7 : ZMod 789298907447299)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 789298907447299 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((43 : ℕ)^1 * ((3059298090881 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 789298907447299)^394649453723649 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 789298907447299)^263099635815766 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (7 : ZMod 789298907447299)^18355788545286 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3059298090881 := Nat.prime_eq_prime_of_dvd_pow hq prime_3059298090881 hd
          subst q
          change (7 : ZMod 789298907447299)^258 ≠ 1
          reduce_mod_char
          decide

theorem prime_805005849390653 : Nat.Prime 805005849390653 := by
  apply lucas_primality 805005849390653 (2 : ZMod 805005849390653)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 805005849390653 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((37 : ℕ)^1 * ((1789 : ℕ)^1 * ((2539 : ℕ)^1 * ((13159 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 805005849390653)^402502924695326 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 805005849390653)^115000835627236 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 805005849390653)^61923526876204 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
            subst q
            change (2 : ZMod 805005849390653)^21756914848396 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1789 := Nat.prime_eq_prime_of_dvd_pow hq prime_1789 hd
              subst q
              change (2 : ZMod 805005849390653)^449975321068 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 2539 := Nat.prime_eq_prime_of_dvd_pow hq prime_2539 hd
                subst q
                change (2 : ZMod 805005849390653)^317056262068 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 13159 := Nat.prime_eq_prime_of_dvd_pow hq prime_13159 hd
                subst q
                change (2 : ZMod 805005849390653)^61175305828 ≠ 1
                reduce_mod_char
                decide

theorem prime_811832234395393 : Nat.Prime 811832234395393 := by
  apply lucas_primality 811832234395393 (10 : ZMod 811832234395393)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 811832234395393 - 1 = (2 : ℕ)^8 * ((3 : ℕ)^2 * ((7 : ℕ)^1 * ((17 : ℕ)^1 * ((37 : ℕ)^1 * ((43 : ℕ)^1 * ((733 : ℕ)^1 * ((2539 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 811832234395393)^405916117197696 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 811832234395393)^270610744798464 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (10 : ZMod 811832234395393)^115976033485056 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (10 : ZMod 811832234395393)^47754837317376 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
              subst q
              change (10 : ZMod 811832234395393)^21941411740416 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
                subst q
                change (10 : ZMod 811832234395393)^18879819404544 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 733 := Nat.prime_eq_prime_of_dvd_pow hq prime_733 hd
                  subst q
                  change (10 : ZMod 811832234395393)^1107547386624 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 2539 := Nat.prime_eq_prime_of_dvd_pow hq prime_2539 hd
                  subst q
                  change (10 : ZMod 811832234395393)^319744873728 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_819366202428481 : Nat.Prime 819366202428481 := by
  apply lucas_primality 819366202428481 (37 : ZMod 819366202428481)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 819366202428481 - 1 = (2 : ℕ)^6 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((19 : ℕ)^1 * ((97 : ℕ)^1 * ((2083 : ℕ)^1 * ((3529 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (37 : ZMod 819366202428481)^409683101214240 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (37 : ZMod 819366202428481)^273122067476160 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (37 : ZMod 819366202428481)^163873240485696 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (37 : ZMod 819366202428481)^117052314632640 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
              subst q
              change (37 : ZMod 819366202428481)^43124536969920 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
                subst q
                change (37 : ZMod 819366202428481)^8447074251840 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 2083 := Nat.prime_eq_prime_of_dvd_pow hq prime_2083 hd
                  subst q
                  change (37 : ZMod 819366202428481)^393358714560 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 3529 := Nat.prime_eq_prime_of_dvd_pow hq prime_3529 hd
                  subst q
                  change (37 : ZMod 819366202428481)^232180845120 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_819812400099023 : Nat.Prime 819812400099023 := by
  apply lucas_primality 819812400099023 (5 : ZMod 819812400099023)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 819812400099023 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((2683 : ℕ)^1 * ((13889004847 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 819812400099023)^409906200049511 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (5 : ZMod 819812400099023)^74528400009002 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2683 := Nat.prime_eq_prime_of_dvd_pow hq prime_2683 hd
          subst q
          change (5 : ZMod 819812400099023)^305558106634 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 13889004847 := Nat.prime_eq_prime_of_dvd_pow hq prime_13889004847 hd
          subst q
          change (5 : ZMod 819812400099023)^59026 ≠ 1
          reduce_mod_char
          decide

theorem prime_820972403643493 : Nat.Prime 820972403643493 := by
  apply lucas_primality 820972403643493 (2 : ZMod 820972403643493)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 820972403643493 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((37 : ℕ)^1 * ((53 : ℕ)^1 * ((11629163177 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 820972403643493)^410486201821746 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 820972403643493)^273657467881164 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (2 : ZMod 820972403643493)^22188443341716 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
            subst q
            change (2 : ZMod 820972403643493)^15490045351764 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 11629163177 := Nat.prime_eq_prime_of_dvd_pow hq prime_11629163177 hd
            subst q
            change (2 : ZMod 820972403643493)^70596 ≠ 1
            reduce_mod_char
            decide

theorem prime_837201991720267 : Nat.Prime 837201991720267 := by
  apply lucas_primality 837201991720267 (2 : ZMod 837201991720267)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 837201991720267 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((53 : ℕ)^1 * ((619 : ℕ)^1 * ((1417722491 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 837201991720267)^418600995860133 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 837201991720267)^279067330573422 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (2 : ZMod 837201991720267)^15796263994722 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 619 := Nat.prime_eq_prime_of_dvd_pow hq prime_619 hd
            subst q
            change (2 : ZMod 837201991720267)^1352507256414 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1417722491 := Nat.prime_eq_prime_of_dvd_pow hq prime_1417722491 hd
            subst q
            change (2 : ZMod 837201991720267)^590526 ≠ 1
            reduce_mod_char
            decide

theorem prime_853698068844557 : Nat.Prime 853698068844557 := by
  apply lucas_primality 853698068844557 (2 : ZMod 853698068844557)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 853698068844557 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((545023 : ℕ)^1 * ((30122161 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 853698068844557)^426849034422278 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 853698068844557)^65669082218812 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 545023 := Nat.prime_eq_prime_of_dvd_pow hq prime_545023 hd
          subst q
          change (2 : ZMod 853698068844557)^1566352372 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 30122161 := Nat.prime_eq_prime_of_dvd_pow hq prime_30122161 hd
          subst q
          change (2 : ZMod 853698068844557)^28341196 ≠ 1
          reduce_mod_char
          decide

theorem prime_864628346563349 : Nat.Prime 864628346563349 := by
  apply lucas_primality 864628346563349 (2 : ZMod 864628346563349)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 864628346563349 - 1 = (2 : ℕ)^2 * ((12373 : ℕ)^1 * ((17470062769 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 864628346563349)^432314173281674 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 12373 := Nat.prime_eq_prime_of_dvd_pow hq prime_12373 hd
        subst q
        change (2 : ZMod 864628346563349)^69880251076 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 17470062769 := Nat.prime_eq_prime_of_dvd_pow hq prime_17470062769 hd
        subst q
        change (2 : ZMod 864628346563349)^49492 ≠ 1
        reduce_mod_char
        decide

theorem prime_870464124169657 : Nat.Prime 870464124169657 := by
  apply lucas_primality 870464124169657 (7 : ZMod 870464124169657)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 870464124169657 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((167 : ℕ)^1 * ((317 : ℕ)^1 * ((685115671 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 870464124169657)^435232062084828 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 870464124169657)^290154708056552 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
          subst q
          change (7 : ZMod 870464124169657)^5212360024968 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 317 := Nat.prime_eq_prime_of_dvd_pow hq prime_317 hd
            subst q
            change (7 : ZMod 870464124169657)^2745943609368 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 685115671 := Nat.prime_eq_prime_of_dvd_pow hq prime_685115671 hd
            subst q
            change (7 : ZMod 870464124169657)^1270536 ≠ 1
            reduce_mod_char
            decide

theorem prime_877393534262257 : Nat.Prime 877393534262257 := by
  apply lucas_primality 877393534262257 (5 : ZMod 877393534262257)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 877393534262257 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^3 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((349 : ℕ)^1 * ((31120291 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 877393534262257)^438696767131128 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 877393534262257)^292464511420752 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 877393534262257)^79763048569296 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (5 : ZMod 877393534262257)^51611384368368 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 349 := Nat.prime_eq_prime_of_dvd_pow hq prime_349 hd
              subst q
              change (5 : ZMod 877393534262257)^2514021588144 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 31120291 := Nat.prime_eq_prime_of_dvd_pow hq prime_31120291 hd
              subst q
              change (5 : ZMod 877393534262257)^28193616 ≠ 1
              reduce_mod_char
              decide

theorem prime_887503681000051 : Nat.Prime 887503681000051 := by
  apply lucas_primality 887503681000051 (2 : ZMod 887503681000051)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 887503681000051 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((1009 : ℕ)^1 * ((5863915963 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 887503681000051)^443751840500025 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 887503681000051)^295834560333350 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 887503681000051)^177500736200010 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1009 := Nat.prime_eq_prime_of_dvd_pow hq prime_1009 hd
            subst q
            change (2 : ZMod 887503681000051)^879587394450 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 5863915963 := Nat.prime_eq_prime_of_dvd_pow hq prime_5863915963 hd
            subst q
            change (2 : ZMod 887503681000051)^151350 ≠ 1
            reduce_mod_char
            decide

theorem prime_904820297013449 : Nat.Prime 904820297013449 := by
  apply lucas_primality 904820297013449 (3 : ZMod 904820297013449)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 904820297013449 - 1 = (2 : ℕ)^3 * ((3581 : ℕ)^1 * ((31584065101 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 904820297013449)^452410148506724 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3581 := Nat.prime_eq_prime_of_dvd_pow hq prime_3581 hd
        subst q
        change (3 : ZMod 904820297013449)^252672520808 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 31584065101 := Nat.prime_eq_prime_of_dvd_pow hq prime_31584065101 hd
        subst q
        change (3 : ZMod 904820297013449)^28648 ≠ 1
        reduce_mod_char
        decide

theorem prime_909895980587771 : Nat.Prime 909895980587771 := by
  apply lucas_primality 909895980587771 (2 : ZMod 909895980587771)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 909895980587771 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((11 : ℕ)^1 * ((8271781641707 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 909895980587771)^454947990293885 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 909895980587771)^181979196117554 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (2 : ZMod 909895980587771)^82717816417070 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 8271781641707 := Nat.prime_eq_prime_of_dvd_pow hq prime_8271781641707 hd
          subst q
          change (2 : ZMod 909895980587771)^110 ≠ 1
          reduce_mod_char
          decide

theorem prime_922377569831413 : Nat.Prime 922377569831413 := by
  apply lucas_primality 922377569831413 (6 : ZMod 922377569831413)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 922377569831413 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((31 : ℕ)^1 * ((5381 : ℕ)^1 * ((460789741 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 922377569831413)^461188784915706 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 922377569831413)^307459189943804 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (6 : ZMod 922377569831413)^29754115155852 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 5381 := Nat.prime_eq_prime_of_dvd_pow hq prime_5381 hd
            subst q
            change (6 : ZMod 922377569831413)^171413783652 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 460789741 := Nat.prime_eq_prime_of_dvd_pow hq prime_460789741 hd
            subst q
            change (6 : ZMod 922377569831413)^2001732 ≠ 1
            reduce_mod_char
            decide

theorem prime_922417564483589 : Nat.Prime 922417564483589 := by
  apply lucas_primality 922417564483589 (2 : ZMod 922417564483589)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 922417564483589 - 1 = (2 : ℕ)^2 * ((29 : ℕ)^1 * ((653 : ℕ)^1 * ((5153 : ℕ)^1 * ((2363177 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 922417564483589)^461208782241794 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
        subst q
        change (2 : ZMod 922417564483589)^31807502223572 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 653 := Nat.prime_eq_prime_of_dvd_pow hq prime_653 hd
          subst q
          change (2 : ZMod 922417564483589)^1412584325396 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 5153 := Nat.prime_eq_prime_of_dvd_pow hq prime_5153 hd
            subst q
            change (2 : ZMod 922417564483589)^179005931396 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2363177 := Nat.prime_eq_prime_of_dvd_pow hq prime_2363177 hd
            subst q
            change (2 : ZMod 922417564483589)^390329444 ≠ 1
            reduce_mod_char
            decide

theorem prime_940299110504297 : Nat.Prime 940299110504297 := by
  apply lucas_primality 940299110504297 (3 : ZMod 940299110504297)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 940299110504297 - 1 = (2 : ℕ)^3 * ((503 : ℕ)^1 * ((233672741179 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 940299110504297)^470149555252148 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 503 := Nat.prime_eq_prime_of_dvd_pow hq prime_503 hd
        subst q
        change (3 : ZMod 940299110504297)^1869381929432 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 233672741179 := Nat.prime_eq_prime_of_dvd_pow hq prime_233672741179 hd
        subst q
        change (3 : ZMod 940299110504297)^4024 ≠ 1
        reduce_mod_char
        decide

theorem prime_958468597212803 : Nat.Prime 958468597212803 := by
  apply lucas_primality 958468597212803 (2 : ZMod 958468597212803)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 958468597212803 - 1 = (2 : ℕ)^1 * ((13 : ℕ)^1 * ((36864176815877 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 958468597212803)^479234298606401 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 958468597212803)^73728353631754 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 36864176815877 := Nat.prime_eq_prime_of_dvd_pow hq prime_36864176815877 hd
        subst q
        change (2 : ZMod 958468597212803)^26 ≠ 1
        reduce_mod_char
        decide

theorem prime_976929722015699 : Nat.Prime 976929722015699 := by
  apply lucas_primality 976929722015699 (2 : ZMod 976929722015699)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 976929722015699 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((59 : ℕ)^1 * ((752642312801 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 976929722015699)^488464861007849 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 976929722015699)^88811792910518 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (2 : ZMod 976929722015699)^16558130881622 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 752642312801 := Nat.prime_eq_prime_of_dvd_pow hq prime_752642312801 hd
          subst q
          change (2 : ZMod 976929722015699)^1298 ≠ 1
          reduce_mod_char
          decide

theorem prime_980608702354051 : Nat.Prime 980608702354051 := by
  apply lucas_primality 980608702354051 (11 : ZMod 980608702354051)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 980608702354051 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((84901186351 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 980608702354051)^490304351177025 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 980608702354051)^326869567451350 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 980608702354051)^196121740470810 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
            subst q
            change (11 : ZMod 980608702354051)^140086957479150 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
              subst q
              change (11 : ZMod 980608702354051)^89146245668550 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 84901186351 := Nat.prime_eq_prime_of_dvd_pow hq prime_84901186351 hd
              subst q
              change (11 : ZMod 980608702354051)^11550 ≠ 1
              reduce_mod_char
              decide

theorem prime_995686217814031 : Nat.Prime 995686217814031 := by
  apply lucas_primality 995686217814031 (6 : ZMod 995686217814031)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 995686217814031 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((13877 : ℕ)^1 * ((2391694213 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 995686217814031)^497843108907015 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 995686217814031)^331895405938010 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 995686217814031)^199137243562806 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13877 := Nat.prime_eq_prime_of_dvd_pow hq prime_13877 hd
            subst q
            change (6 : ZMod 995686217814031)^71750826390 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2391694213 := Nat.prime_eq_prime_of_dvd_pow hq prime_2391694213 hd
            subst q
            change (6 : ZMod 995686217814031)^416310 ≠ 1
            reduce_mod_char
            decide

theorem prime_1014741853230173 : Nat.Prime 1014741853230173 := by
  apply lucas_primality 1014741853230173 (2 : ZMod 1014741853230173)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1014741853230173 - 1 = (2 : ℕ)^2 * ((225499 : ℕ)^1 * ((1124995957 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1014741853230173)^507370926615086 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 225499 := Nat.prime_eq_prime_of_dvd_pow hq prime_225499 hd
        subst q
        change (2 : ZMod 1014741853230173)^4499983828 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 1124995957 := Nat.prime_eq_prime_of_dvd_pow hq prime_1124995957 hd
        subst q
        change (2 : ZMod 1014741853230173)^901996 ≠ 1
        reduce_mod_char
        decide

theorem prime_1034100432834629 : Nat.Prime 1034100432834629 := by
  apply lucas_primality 1034100432834629 (2 : ZMod 1034100432834629)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1034100432834629 - 1 = (2 : ℕ)^2 * ((569 : ℕ)^1 * ((454349926553 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1034100432834629)^517050216417314 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 569 := Nat.prime_eq_prime_of_dvd_pow hq prime_569 hd
        subst q
        change (2 : ZMod 1034100432834629)^1817399706212 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 454349926553 := Nat.prime_eq_prime_of_dvd_pow hq prime_454349926553 hd
        subst q
        change (2 : ZMod 1034100432834629)^2276 ≠ 1
        reduce_mod_char
        decide

theorem prime_1053765797374159 : Nat.Prime 1053765797374159 := by
  apply lucas_primality 1053765797374159 (3 : ZMod 1053765797374159)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1053765797374159 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((619 : ℕ)^1 * ((6277 : ℕ)^1 * ((4109201 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1053765797374159)^526882898687079 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1053765797374159)^351255265791386 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (3 : ZMod 1053765797374159)^95796890670378 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 619 := Nat.prime_eq_prime_of_dvd_pow hq prime_619 hd
            subst q
            change (3 : ZMod 1053765797374159)^1702368008682 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 6277 := Nat.prime_eq_prime_of_dvd_pow hq prime_6277 hd
              subst q
              change (3 : ZMod 1053765797374159)^167877297654 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 4109201 := Nat.prime_eq_prime_of_dvd_pow hq prime_4109201 hd
              subst q
              change (3 : ZMod 1053765797374159)^256440558 ≠ 1
              reduce_mod_char
              decide

theorem prime_1073741824000033 : Nat.Prime 1073741824000033 := by
  apply lucas_primality 1073741824000033 (7 : ZMod 1073741824000033)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1073741824000033 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((43 : ℕ)^1 * ((8369 : ℕ)^1 * ((2825491 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1073741824000033)^536870912000016 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 1073741824000033)^357913941333344 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (7 : ZMod 1073741824000033)^97612893090912 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (7 : ZMod 1073741824000033)^24970740093024 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 8369 := Nat.prime_eq_prime_of_dvd_pow hq prime_8369 hd
              subst q
              change (7 : ZMod 1073741824000033)^128299895328 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 2825491 := Nat.prime_eq_prime_of_dvd_pow hq prime_2825491 hd
              subst q
              change (7 : ZMod 1073741824000033)^380019552 ≠ 1
              reduce_mod_char
              decide

theorem prime_1094032426498043 : Nat.Prime 1094032426498043 := by
  apply lucas_primality 1094032426498043 (2 : ZMod 1094032426498043)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1094032426498043 - 1 = (2 : ℕ)^1 * ((547016213249021 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1094032426498043)^547016213249021 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 547016213249021 := Nat.prime_eq_prime_of_dvd_pow hq prime_547016213249021 hd
      subst q
      change (2 : ZMod 1094032426498043)^2 ≠ 1
      reduce_mod_char
      decide

theorem prime_1097296211423077 : Nat.Prime 1097296211423077 := by
  apply lucas_primality 1097296211423077 (2 : ZMod 1097296211423077)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1097296211423077 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^2 * ((1866150019427 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1097296211423077)^548648105711538 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1097296211423077)^365765403807692 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 1097296211423077)^156756601631868 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 1866150019427 := Nat.prime_eq_prime_of_dvd_pow hq prime_1866150019427 hd
          subst q
          change (2 : ZMod 1097296211423077)^588 ≠ 1
          reduce_mod_char
          decide

theorem prime_1114641555517507 : Nat.Prime 1114641555517507 := by
  apply lucas_primality 1114641555517507 (2 : ZMod 1114641555517507)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1114641555517507 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((41 : ℕ)^1 * ((43 : ℕ)^1 * ((59 : ℕ)^1 * ((6427 : ℕ)^1 * ((277889 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1114641555517507)^557320777758753 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1114641555517507)^371547185172502 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (2 : ZMod 1114641555517507)^27186379402866 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (2 : ZMod 1114641555517507)^25921896639942 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
              subst q
              change (2 : ZMod 1114641555517507)^18892229754534 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 6427 := Nat.prime_eq_prime_of_dvd_pow hq prime_6427 hd
                subst q
                change (2 : ZMod 1114641555517507)^173431080678 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 277889 := Nat.prime_eq_prime_of_dvd_pow hq prime_277889 hd
                subst q
                change (2 : ZMod 1114641555517507)^4011103554 ≠ 1
                reduce_mod_char
                decide

theorem prime_1135573198803301 : Nat.Prime 1135573198803301 := by
  apply lucas_primality 1135573198803301 (2 : ZMod 1135573198803301)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1135573198803301 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((3785243996011 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1135573198803301)^567786599401650 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1135573198803301)^378524399601100 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 1135573198803301)^227114639760660 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3785243996011 := Nat.prime_eq_prime_of_dvd_pow hq prime_3785243996011 hd
          subst q
          change (2 : ZMod 1135573198803301)^300 ≠ 1
          reduce_mod_char
          decide

theorem prime_1137774425704471 : Nat.Prime 1137774425704471 := by
  apply lucas_primality 1137774425704471 (3 : ZMod 1137774425704471)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1137774425704471 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((5 : ℕ)^1 * ((4213979354461 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1137774425704471)^568887212852235 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1137774425704471)^379258141901490 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 1137774425704471)^227554885140894 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 4213979354461 := Nat.prime_eq_prime_of_dvd_pow hq prime_4213979354461 hd
          subst q
          change (3 : ZMod 1137774425704471)^270 ≠ 1
          reduce_mod_char
          decide

theorem prime_1144250857502101 : Nat.Prime 1144250857502101 := by
  apply lucas_primality 1144250857502101 (2 : ZMod 1144250857502101)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1144250857502101 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^2 * ((23 : ℕ)^1 * ((193 : ℕ)^1 * ((811 : ℕ)^1 * ((353161 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1144250857502101)^572125428751050 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1144250857502101)^381416952500700 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 1144250857502101)^228850171500420 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (2 : ZMod 1144250857502101)^49750037282700 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 193 := Nat.prime_eq_prime_of_dvd_pow hq prime_193 hd
              subst q
              change (2 : ZMod 1144250857502101)^5928760919700 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 811 := Nat.prime_eq_prime_of_dvd_pow hq prime_811 hd
                subst q
                change (2 : ZMod 1144250857502101)^1410913511100 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 353161 := Nat.prime_eq_prime_of_dvd_pow hq prime_353161 hd
                subst q
                change (2 : ZMod 1144250857502101)^3240026100 ≠ 1
                reduce_mod_char
                decide

theorem prime_1156831381426291 : Nat.Prime 1156831381426291 := by
  apply lucas_primality 1156831381426291 (2 : ZMod 1156831381426291)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1156831381426291 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((113 : ℕ)^1 * ((991 : ℕ)^1 * ((8861 : ℕ)^1 * ((38861 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1156831381426291)^578415690713145 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1156831381426291)^385610460475430 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 1156831381426291)^231366276285258 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 113 := Nat.prime_eq_prime_of_dvd_pow hq prime_113 hd
            subst q
            change (2 : ZMod 1156831381426291)^10237445853330 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 991 := Nat.prime_eq_prime_of_dvd_pow hq prime_991 hd
              subst q
              change (2 : ZMod 1156831381426291)^1167337418190 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 8861 := Nat.prime_eq_prime_of_dvd_pow hq prime_8861 hd
                subst q
                change (2 : ZMod 1156831381426291)^130553140890 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 38861 := Nat.prime_eq_prime_of_dvd_pow hq prime_38861 hd
                subst q
                change (2 : ZMod 1156831381426291)^29768440890 ≠ 1
                reduce_mod_char
                decide

theorem prime_1178420166015691 : Nat.Prime 1178420166015691 := by
  apply lucas_primality 1178420166015691 (3 : ZMod 1178420166015691)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1178420166015691 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((111919 : ℕ)^1 * ((26998009 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1178420166015691)^589210083007845 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1178420166015691)^392806722005230 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 1178420166015691)^235684033203138 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (3 : ZMod 1178420166015691)^90647705078130 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 111919 := Nat.prime_eq_prime_of_dvd_pow hq prime_111919 hd
              subst q
              change (3 : ZMod 1178420166015691)^10529223510 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 26998009 := Nat.prime_eq_prime_of_dvd_pow hq prime_26998009 hd
              subst q
              change (3 : ZMod 1178420166015691)^43648410 ≠ 1
              reduce_mod_char
              decide

theorem prime_1200343652992657 : Nat.Prime 1200343652992657 := by
  apply lucas_primality 1200343652992657 (7 : ZMod 1200343652992657)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1200343652992657 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^2 * ((22067 : ℕ)^1 * ((377745947 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1200343652992657)^600171826496328 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (7 : ZMod 1200343652992657)^400114550997552 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 22067 := Nat.prime_eq_prime_of_dvd_pow hq prime_22067 hd
          subst q
          change (7 : ZMod 1200343652992657)^54395416368 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 377745947 := Nat.prime_eq_prime_of_dvd_pow hq prime_377745947 hd
          subst q
          change (7 : ZMod 1200343652992657)^3177648 ≠ 1
          reduce_mod_char
          decide

theorem prime_1222605980803121 : Nat.Prime 1222605980803121 := by
  apply lucas_primality 1222605980803121 (6 : ZMod 1222605980803121)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1222605980803121 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((15282574760039 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 1222605980803121)^611302990401560 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 1222605980803121)^244521196160624 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 15282574760039 := Nat.prime_eq_prime_of_dvd_pow hq prime_15282574760039 hd
        subst q
        change (6 : ZMod 1222605980803121)^80 ≠ 1
        reduce_mod_char
        decide

theorem prime_1233888381237301 : Nat.Prime 1233888381237301 := by
  apply lucas_primality 1233888381237301 (2 : ZMod 1233888381237301)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1233888381237301 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((2237 : ℕ)^1 * ((1838605843 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1233888381237301)^616944190618650 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1233888381237301)^411296127079100 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 1233888381237301)^246777676247460 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2237 := Nat.prime_eq_prime_of_dvd_pow hq prime_2237 hd
            subst q
            change (2 : ZMod 1233888381237301)^551581752900 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1838605843 := Nat.prime_eq_prime_of_dvd_pow hq prime_1838605843 hd
            subst q
            change (2 : ZMod 1233888381237301)^671100 ≠ 1
            reduce_mod_char
            decide

theorem prime_1245211326152711 : Nat.Prime 1245211326152711 := by
  apply lucas_primality 1245211326152711 (13 : ZMod 1245211326152711)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1245211326152711 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((827 : ℕ)^1 * ((53353 : ℕ)^1 * ((403163 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (13 : ZMod 1245211326152711)^622605663076355 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (13 : ZMod 1245211326152711)^249042265230542 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (13 : ZMod 1245211326152711)^177887332307530 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 827 := Nat.prime_eq_prime_of_dvd_pow hq prime_827 hd
            subst q
            change (13 : ZMod 1245211326152711)^1505696887730 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 53353 := Nat.prime_eq_prime_of_dvd_pow hq prime_53353 hd
              subst q
              change (13 : ZMod 1245211326152711)^23339106070 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 403163 := Nat.prime_eq_prime_of_dvd_pow hq prime_403163 hd
              subst q
              change (13 : ZMod 1245211326152711)^3088605170 ≠ 1
              reduce_mod_char
              decide

theorem prime_1258210937500003 : Nat.Prime 1258210937500003 := by
  apply lucas_primality 1258210937500003 (3 : ZMod 1258210937500003)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1258210937500003 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((53 : ℕ)^1 * ((205703 : ℕ)^1 * ((6411571 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1258210937500003)^629105468750001 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1258210937500003)^419403645833334 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
          subst q
          change (3 : ZMod 1258210937500003)^23739829009434 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 205703 := Nat.prime_eq_prime_of_dvd_pow hq prime_205703 hd
            subst q
            change (3 : ZMod 1258210937500003)^6116638734 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 6411571 := Nat.prime_eq_prime_of_dvd_pow hq prime_6411571 hd
            subst q
            change (3 : ZMod 1258210937500003)^196240662 ≠ 1
            reduce_mod_char
            decide

theorem prime_1268163904241617 : Nat.Prime 1268163904241617 := by
  apply lucas_primality 1268163904241617 (5 : ZMod 1268163904241617)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1268163904241617 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((2377 : ℕ)^1 * ((11114884871 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1268163904241617)^634081952120808 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1268163904241617)^422721301413872 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 2377 := Nat.prime_eq_prime_of_dvd_pow hq prime_2377 hd
          subst q
          change (5 : ZMod 1268163904241617)^533514473808 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 11114884871 := Nat.prime_eq_prime_of_dvd_pow hq prime_11114884871 hd
          subst q
          change (5 : ZMod 1268163904241617)^114096 ≠ 1
          reduce_mod_char
          decide

theorem prime_1291467969000029 : Nat.Prime 1291467969000029 := by
  apply lucas_primality 1291467969000029 (2 : ZMod 1291467969000029)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1291467969000029 - 1 = (2 : ℕ)^2 * ((107 : ℕ)^1 * ((213791 : ℕ)^1 * ((14114011 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1291467969000029)^645733984500014 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 107 := Nat.prime_eq_prime_of_dvd_pow hq prime_107 hd
        subst q
        change (2 : ZMod 1291467969000029)^12069794102804 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 213791 := Nat.prime_eq_prime_of_dvd_pow hq prime_213791 hd
          subst q
          change (2 : ZMod 1291467969000029)^6040796708 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 14114011 := Nat.prime_eq_prime_of_dvd_pow hq prime_14114011 hd
          subst q
          change (2 : ZMod 1291467969000029)^91502548 ≠ 1
          reduce_mod_char
          decide

theorem prime_1315127813325581 : Nat.Prime 1315127813325581 := by
  apply lucas_primality 1315127813325581 (7 : ZMod 1315127813325581)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1315127813325581 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((4217 : ℕ)^1 * ((15593168287 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1315127813325581)^657563906662790 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 1315127813325581)^263025562665116 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 4217 := Nat.prime_eq_prime_of_dvd_pow hq prime_4217 hd
          subst q
          change (7 : ZMod 1315127813325581)^311863365740 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 15593168287 := Nat.prime_eq_prime_of_dvd_pow hq prime_15593168287 hd
          subst q
          change (7 : ZMod 1315127813325581)^84340 ≠ 1
          reduce_mod_char
          decide

theorem prime_1319169840365383 : Nat.Prime 1319169840365383 := by
  apply lucas_primality 1319169840365383 (3 : ZMod 1319169840365383)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1319169840365383 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((17 : ℕ)^1 * ((19 : ℕ)^1 * ((38569 : ℕ)^1 * ((17648531 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1319169840365383)^659584920182691 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1319169840365383)^439723280121794 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (3 : ZMod 1319169840365383)^77598225903846 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (3 : ZMod 1319169840365383)^69429991598178 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 38569 := Nat.prime_eq_prime_of_dvd_pow hq prime_38569 hd
              subst q
              change (3 : ZMod 1319169840365383)^34202853078 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 17648531 := Nat.prime_eq_prime_of_dvd_pow hq prime_17648531 hd
              subst q
              change (3 : ZMod 1319169840365383)^74746722 ≠ 1
              reduce_mod_char
              decide

theorem prime_1339147769319457 : Nat.Prime 1339147769319457 := by
  apply lucas_primality 1339147769319457 (5 : ZMod 1339147769319457)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1339147769319457 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((13949455930411 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1339147769319457)^669573884659728 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1339147769319457)^446382589773152 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 13949455930411 := Nat.prime_eq_prime_of_dvd_pow hq prime_13949455930411 hd
        subst q
        change (5 : ZMod 1339147769319457)^96 ≠ 1
        reduce_mod_char
        decide

theorem prime_1363532208525371 : Nat.Prime 1363532208525371 := by
  apply lucas_primality 1363532208525371 (6 : ZMod 1363532208525371)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1363532208525371 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((13 : ℕ)^1 * ((853 : ℕ)^1 * ((937 : ℕ)^1 * ((13123009 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 1363532208525371)^681766104262685 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 1363532208525371)^272706441705074 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (6 : ZMod 1363532208525371)^104887092963490 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 853 := Nat.prime_eq_prime_of_dvd_pow hq prime_853 hd
            subst q
            change (6 : ZMod 1363532208525371)^1598513726290 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 937 := Nat.prime_eq_prime_of_dvd_pow hq prime_937 hd
              subst q
              change (6 : ZMod 1363532208525371)^1455210468010 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 13123009 := Nat.prime_eq_prime_of_dvd_pow hq prime_13123009 hd
              subst q
              change (6 : ZMod 1363532208525371)^103903930 ≠ 1
              reduce_mod_char
              decide

theorem prime_1388285542167637 : Nat.Prime 1388285542167637 := by
  apply lucas_primality 1388285542167637 (2 : ZMod 1388285542167637)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1388285542167637 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((16527208835329 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1388285542167637)^694142771083818 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1388285542167637)^462761847389212 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 1388285542167637)^198326506023948 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 16527208835329 := Nat.prime_eq_prime_of_dvd_pow hq prime_16527208835329 hd
          subst q
          change (2 : ZMod 1388285542167637)^84 ≠ 1
          reduce_mod_char
          decide

theorem prime_1413412221390647 : Nat.Prime 1413412221390647 := by
  apply lucas_primality 1413412221390647 (5 : ZMod 1413412221390647)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1413412221390647 - 1 = (2 : ℕ)^1 * ((41 : ℕ)^1 * ((250073 : ℕ)^1 * ((68926811 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1413412221390647)^706706110695323 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
        subst q
        change (5 : ZMod 1413412221390647)^34473468814406 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 250073 := Nat.prime_eq_prime_of_dvd_pow hq prime_250073 hd
          subst q
          change (5 : ZMod 1413412221390647)^5651998502 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 68926811 := Nat.prime_eq_prime_of_dvd_pow hq prime_68926811 hd
          subst q
          change (5 : ZMod 1413412221390647)^20505986 ≠ 1
          reduce_mod_char
          decide

theorem prime_1438916737499159 : Nat.Prime 1438916737499159 := by
  apply lucas_primality 1438916737499159 (7 : ZMod 1438916737499159)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1438916737499159 - 1 = (2 : ℕ)^1 * ((131 : ℕ)^1 * ((1381 : ℕ)^1 * ((3976863589 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 1438916737499159)^719458368749579 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 131 := Nat.prime_eq_prime_of_dvd_pow hq prime_131 hd
        subst q
        change (7 : ZMod 1438916737499159)^10984097232818 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1381 := Nat.prime_eq_prime_of_dvd_pow hq prime_1381 hd
          subst q
          change (7 : ZMod 1438916737499159)^1041938260318 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 3976863589 := Nat.prime_eq_prime_of_dvd_pow hq prime_3976863589 hd
          subst q
          change (7 : ZMod 1438916737499159)^361822 ≠ 1
          reduce_mod_char
          decide

theorem prime_1464803622199013 : Nat.Prime 1464803622199013 := by
  apply lucas_primality 1464803622199013 (2 : ZMod 1464803622199013)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1464803622199013 - 1 = (2 : ℕ)^2 * ((67 : ℕ)^1 * ((11059 : ℕ)^1 * ((19843 : ℕ)^1 * ((24907 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1464803622199013)^732401811099506 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 67 := Nat.prime_eq_prime_of_dvd_pow hq prime_67 hd
        subst q
        change (2 : ZMod 1464803622199013)^21862740629836 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11059 := Nat.prime_eq_prime_of_dvd_pow hq prime_11059 hd
          subst q
          change (2 : ZMod 1464803622199013)^132453533068 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19843 := Nat.prime_eq_prime_of_dvd_pow hq prime_19843 hd
            subst q
            change (2 : ZMod 1464803622199013)^73819665484 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 24907 := Nat.prime_eq_prime_of_dvd_pow hq prime_24907 hd
            subst q
            change (2 : ZMod 1464803622199013)^58810921516 ≠ 1
            reduce_mod_char
            decide

theorem prime_1470014369141767 : Nat.Prime 1470014369141767 := by
  apply lucas_primality 1470014369141767 (3 : ZMod 1470014369141767)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1470014369141767 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((35000342122423 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1470014369141767)^735007184570883 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1470014369141767)^490004789713922 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 1470014369141767)^210002052734538 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 35000342122423 := Nat.prime_eq_prime_of_dvd_pow hq prime_35000342122423 hd
          subst q
          change (3 : ZMod 1470014369141767)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_1479042112125521 : Nat.Prime 1479042112125521 := by
  apply lucas_primality 1479042112125521 (3 : ZMod 1479042112125521)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1479042112125521 - 1 = (2 : ℕ)^4 * ((5 : ℕ)^1 * ((41 : ℕ)^1 * ((83 : ℕ)^1 * ((21407 : ℕ)^1 * ((253789 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1479042112125521)^739521056062760 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 1479042112125521)^295808422425104 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
          subst q
          change (3 : ZMod 1479042112125521)^36074197856720 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 83 := Nat.prime_eq_prime_of_dvd_pow hq prime_83 hd
            subst q
            change (3 : ZMod 1479042112125521)^17819784483440 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 21407 := Nat.prime_eq_prime_of_dvd_pow hq prime_21407 hd
              subst q
              change (3 : ZMod 1479042112125521)^69091517360 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 253789 := Nat.prime_eq_prime_of_dvd_pow hq prime_253789 hd
              subst q
              change (3 : ZMod 1479042112125521)^5827841680 ≠ 1
              reduce_mod_char
              decide

theorem prime_1491077447838821 : Nat.Prime 1491077447838821 := by
  apply lucas_primality 1491077447838821 (2 : ZMod 1491077447838821)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1491077447838821 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((29 : ℕ)^1 * ((2570823185929 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1491077447838821)^745538723919410 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 1491077447838821)^298215489567764 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (2 : ZMod 1491077447838821)^51416463718580 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2570823185929 := Nat.prime_eq_prime_of_dvd_pow hq prime_2570823185929 hd
          subst q
          change (2 : ZMod 1491077447838821)^580 ≠ 1
          reduce_mod_char
          decide

theorem prime_1517742827651983 : Nat.Prime 1517742827651983 := by
  apply lucas_primality 1517742827651983 (3 : ZMod 1517742827651983)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1517742827651983 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((457 : ℕ)^1 * ((553516713221 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1517742827651983)^758871413825991 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1517742827651983)^505914275883994 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 457 := Nat.prime_eq_prime_of_dvd_pow hq prime_457 hd
          subst q
          change (3 : ZMod 1517742827651983)^3321100279326 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 553516713221 := Nat.prime_eq_prime_of_dvd_pow hq prime_553516713221 hd
          subst q
          change (3 : ZMod 1517742827651983)^2742 ≠ 1
          reduce_mod_char
          decide

theorem prime_1532738134524803 : Nat.Prime 1532738134524803 := by
  apply lucas_primality 1532738134524803 (2 : ZMod 1532738134524803)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1532738134524803 - 1 = (2 : ℕ)^1 * ((97 : ℕ)^1 * ((7900712033633 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1532738134524803)^766369067262401 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
        subst q
        change (2 : ZMod 1532738134524803)^15801424067266 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 7900712033633 := Nat.prime_eq_prime_of_dvd_pow hq prime_7900712033633 hd
        subst q
        change (2 : ZMod 1532738134524803)^194 ≠ 1
        reduce_mod_char
        decide

theorem prime_1544804416000033 : Nat.Prime 1544804416000033 := by
  apply lucas_primality 1544804416000033 (5 : ZMod 1544804416000033)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1544804416000033 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((11 : ℕ)^1 * ((43 : ℕ)^1 * ((137 : ℕ)^1 * ((433 : ℕ)^1 * ((587 : ℕ)^1 * ((977 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1544804416000033)^772402208000016 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1544804416000033)^514934805333344 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
          subst q
          change (5 : ZMod 1544804416000033)^140436765090912 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (5 : ZMod 1544804416000033)^35925684093024 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
              subst q
              change (5 : ZMod 1544804416000033)^11275944642336 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 433 := Nat.prime_eq_prime_of_dvd_pow hq prime_433 hd
                subst q
                change (5 : ZMod 1544804416000033)^3567677635104 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 587 := Nat.prime_eq_prime_of_dvd_pow hq prime_587 hd
                  subst q
                  change (5 : ZMod 1544804416000033)^2631694064736 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 977 := Nat.prime_eq_prime_of_dvd_pow hq prime_977 hd
                  subst q
                  change (5 : ZMod 1544804416000033)^1581171357216 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_1572266908616077 : Nat.Prime 1572266908616077 := by
  apply lucas_primality 1572266908616077 (2 : ZMod 1572266908616077)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1572266908616077 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((43674080794891 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1572266908616077)^786133454308038 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1572266908616077)^524088969538692 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 43674080794891 := Nat.prime_eq_prime_of_dvd_pow hq prime_43674080794891 hd
        subst q
        change (2 : ZMod 1572266908616077)^36 ≠ 1
        reduce_mod_char
        decide

theorem prime_1588833114143897 : Nat.Prime 1588833114143897 := by
  apply lucas_primality 1588833114143897 (3 : ZMod 1588833114143897)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1588833114143897 - 1 = (2 : ℕ)^3 * ((23 : ℕ)^1 * ((31 : ℕ)^1 * ((43 : ℕ)^1 * ((229 : ℕ)^1 * ((277 : ℕ)^1 * ((102121 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1588833114143897)^794416557071948 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (3 : ZMod 1588833114143897)^69079700614952 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (3 : ZMod 1588833114143897)^51252681101416 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
            subst q
            change (3 : ZMod 1588833114143897)^36949607305672 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 229 := Nat.prime_eq_prime_of_dvd_pow hq prime_229 hd
              subst q
              change (3 : ZMod 1588833114143897)^6938135869624 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 277 := Nat.prime_eq_prime_of_dvd_pow hq prime_277 hd
                subst q
                change (3 : ZMod 1588833114143897)^5735859617848 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 102121 := Nat.prime_eq_prime_of_dvd_pow hq prime_102121 hd
                subst q
                change (3 : ZMod 1588833114143897)^15558338776 ≠ 1
                reduce_mod_char
                decide

theorem prime_1600135042849381 : Nat.Prime 1600135042849381 := by
  apply lucas_primality 1600135042849381 (2 : ZMod 1600135042849381)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1600135042849381 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^2 * ((5 : ℕ)^1 * ((8889639126941 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1600135042849381)^800067521424690 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1600135042849381)^533378347616460 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (2 : ZMod 1600135042849381)^320027008569876 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 8889639126941 := Nat.prime_eq_prime_of_dvd_pow hq prime_8889639126941 hd
          subst q
          change (2 : ZMod 1600135042849381)^180 ≠ 1
          reduce_mod_char
          decide

theorem prime_1628413597910497 : Nat.Prime 1628413597910497 := by
  apply lucas_primality 1628413597910497 (5 : ZMod 1628413597910497)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1628413597910497 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((16962641644901 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1628413597910497)^814206798955248 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1628413597910497)^542804532636832 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 16962641644901 := Nat.prime_eq_prime_of_dvd_pow hq prime_16962641644901 hd
        subst q
        change (5 : ZMod 1628413597910497)^96 ≠ 1
        reduce_mod_char
        decide

theorem prime_1657107395117117 : Nat.Prime 1657107395117117 := by
  apply lucas_primality 1657107395117117 (2 : ZMod 1657107395117117)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1657107395117117 - 1 = (2 : ℕ)^2 * ((47 : ℕ)^1 * ((151 : ℕ)^1 * ((58373516807 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1657107395117117)^828553697558558 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
        subst q
        change (2 : ZMod 1657107395117117)^35257604151428 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
          subst q
          change (2 : ZMod 1657107395117117)^10974221159716 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 58373516807 := Nat.prime_eq_prime_of_dvd_pow hq prime_58373516807 hd
          subst q
          change (2 : ZMod 1657107395117117)^28388 ≠ 1
          reduce_mod_char
          decide

theorem prime_1662353759742917 : Nat.Prime 1662353759742917 := by
  apply lucas_primality 1662353759742917 (2 : ZMod 1662353759742917)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1662353759742917 - 1 = (2 : ℕ)^2 * ((19 : ℕ)^1 * ((153623 : ℕ)^1 * ((142381517 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1662353759742917)^831176879871458 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
        subst q
        change (2 : ZMod 1662353759742917)^87492303144364 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 153623 := Nat.prime_eq_prime_of_dvd_pow hq prime_153623 hd
          subst q
          change (2 : ZMod 1662353759742917)^10820995292 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 142381517 := Nat.prime_eq_prime_of_dvd_pow hq prime_142381517 hd
          subst q
          change (2 : ZMod 1662353759742917)^11675348 ≠ 1
          reduce_mod_char
          decide

theorem prime_1686221298140653 : Nat.Prime 1686221298140653 := by
  apply lucas_primality 1686221298140653 (2 : ZMod 1686221298140653)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1686221298140653 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((13 : ℕ)^1 * ((31 : ℕ)^1 * ((37 : ℕ)^1 * ((109 : ℕ)^1 * ((1063 : ℕ)^1 * ((1291 : ℕ)^1)))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1686221298140653)^843110649070326 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1686221298140653)^562073766046884 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 1686221298140653)^240888756877236 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
            subst q
            change (2 : ZMod 1686221298140653)^129709330626204 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
              subst q
              change (2 : ZMod 1686221298140653)^54394235423892 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
                subst q
                change (2 : ZMod 1686221298140653)^45573548598396 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 109 := Nat.prime_eq_prime_of_dvd_pow hq prime_109 hd
                  subst q
                  change (2 : ZMod 1686221298140653)^15469920166428 ≠ 1
                  reduce_mod_char
                  decide
                · rcases hq.dvd_mul.mp hd with hd | hd
                  · have heq : q = 1063 := Nat.prime_eq_prime_of_dvd_pow hq prime_1063 hd
                    subst q
                    change (2 : ZMod 1686221298140653)^1586285322804 ≠ 1
                    reduce_mod_char
                    decide
                  · have heq : q = 1291 := Nat.prime_eq_prime_of_dvd_pow hq prime_1291 hd
                    subst q
                    change (2 : ZMod 1686221298140653)^1306135784772 ≠ 1
                    reduce_mod_char
                    decide

theorem prime_1715760213253699 : Nat.Prime 1715760213253699 := by
  apply lucas_primality 1715760213253699 (2 : ZMod 1715760213253699)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1715760213253699 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((285960035542283 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1715760213253699)^857880106626849 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 1715760213253699)^571920071084566 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 285960035542283 := Nat.prime_eq_prime_of_dvd_pow hq prime_285960035542283 hd
        subst q
        change (2 : ZMod 1715760213253699)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_1745729089577951 : Nat.Prime 1745729089577951 := by
  apply lucas_primality 1745729089577951 (11 : ZMod 1745729089577951)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1745729089577951 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^2 * ((691 : ℕ)^1 * ((2293 : ℕ)^1 * ((2357 : ℕ)^1 * ((9349 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 1745729089577951)^872864544788975 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (11 : ZMod 1745729089577951)^349145817915590 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 691 := Nat.prime_eq_prime_of_dvd_pow hq prime_691 hd
          subst q
          change (11 : ZMod 1745729089577951)^2526380737450 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2293 := Nat.prime_eq_prime_of_dvd_pow hq prime_2293 hd
            subst q
            change (11 : ZMod 1745729089577951)^761329738150 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 2357 := Nat.prime_eq_prime_of_dvd_pow hq prime_2357 hd
              subst q
              change (11 : ZMod 1745729089577951)^740657229350 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 9349 := Nat.prime_eq_prime_of_dvd_pow hq prime_9349 hd
              subst q
              change (11 : ZMod 1745729089577951)^186728964550 ≠ 1
              reduce_mod_char
              decide

theorem prime_1776132919332899 : Nat.Prime 1776132919332899 := by
  apply lucas_primality 1776132919332899 (2 : ZMod 1776132919332899)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1776132919332899 - 1 = (2 : ℕ)^1 * ((7 : ℕ)^1 * ((61 : ℕ)^1 * ((2341 : ℕ)^1 * ((888415607 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1776132919332899)^888066459666449 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 1776132919332899)^253733274190414 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (2 : ZMod 1776132919332899)^29116933103818 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 2341 := Nat.prime_eq_prime_of_dvd_pow hq prime_2341 hd
            subst q
            change (2 : ZMod 1776132919332899)^758706928378 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 888415607 := Nat.prime_eq_prime_of_dvd_pow hq prime_888415607 hd
            subst q
            change (2 : ZMod 1776132919332899)^1999214 ≠ 1
            reduce_mod_char
            decide

theorem prime_1806976738085473 : Nat.Prime 1806976738085473 := by
  apply lucas_primality 1806976738085473 (5 : ZMod 1806976738085473)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1806976738085473 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^3 * ((409289 : ℕ)^1 * ((5109857 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1806976738085473)^903488369042736 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1806976738085473)^602325579361824 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 409289 := Nat.prime_eq_prime_of_dvd_pow hq prime_409289 hd
          subst q
          change (5 : ZMod 1806976738085473)^4414916448 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 5109857 := Nat.prime_eq_prime_of_dvd_pow hq prime_5109857 hd
          subst q
          change (5 : ZMod 1806976738085473)^353625696 ≠ 1
          reduce_mod_char
          decide

theorem prime_1838265625000039 : Nat.Prime 1838265625000039 := by
  apply lucas_primality 1838265625000039 (3 : ZMod 1838265625000039)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1838265625000039 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((23 : ℕ)^1 * ((137 : ℕ)^1 * ((14947 : ℕ)^1 * ((500393 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1838265625000039)^919132812500019 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 1838265625000039)^612755208333346 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (3 : ZMod 1838265625000039)^141405048076926 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (3 : ZMod 1838265625000039)^79924592391306 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
              subst q
              change (3 : ZMod 1838265625000039)^13417997262774 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 14947 := Nat.prime_eq_prime_of_dvd_pow hq prime_14947 hd
                subst q
                change (3 : ZMod 1838265625000039)^122985590754 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 500393 := Nat.prime_eq_prime_of_dvd_pow hq prime_500393 hd
                subst q
                change (3 : ZMod 1838265625000039)^3673643766 ≠ 1
                reduce_mod_char
                decide

theorem prime_1870004703089603 : Nat.Prime 1870004703089603 := by
  apply lucas_primality 1870004703089603 (2 : ZMod 1870004703089603)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1870004703089603 - 1 = (2 : ℕ)^1 * ((229 : ℕ)^1 * ((269 : ℕ)^1 * ((3469 : ℕ)^1 * ((4375429 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1870004703089603)^935002351544801 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 229 := Nat.prime_eq_prime_of_dvd_pow hq prime_229 hd
        subst q
        change (2 : ZMod 1870004703089603)^8165959402138 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 269 := Nat.prime_eq_prime_of_dvd_pow hq prime_269 hd
          subst q
          change (2 : ZMod 1870004703089603)^6951690346058 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 3469 := Nat.prime_eq_prime_of_dvd_pow hq prime_3469 hd
            subst q
            change (2 : ZMod 1870004703089603)^539061603658 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 4375429 := Nat.prime_eq_prime_of_dvd_pow hq prime_4375429 hd
            subst q
            change (2 : ZMod 1870004703089603)^427387738 ≠ 1
            reduce_mod_char
            decide

theorem prime_1902199139467307 : Nat.Prime 1902199139467307 := by
  apply lucas_primality 1902199139467307 (2 : ZMod 1902199139467307)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1902199139467307 - 1 = (2 : ℕ)^1 * ((23 : ℕ)^2 * ((4283 : ℕ)^1 * ((419780479 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1902199139467307)^951099569733653 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
        subst q
        change (2 : ZMod 1902199139467307)^82704310411622 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 4283 := Nat.prime_eq_prime_of_dvd_pow hq prime_4283 hd
          subst q
          change (2 : ZMod 1902199139467307)^444127746782 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 419780479 := Nat.prime_eq_prime_of_dvd_pow hq prime_419780479 hd
          subst q
          change (2 : ZMod 1902199139467307)^4531414 ≠ 1
          reduce_mod_char
          decide

theorem prime_1934854145598533 : Nat.Prime 1934854145598533 := by
  apply lucas_primality 1934854145598533 (2 : ZMod 1934854145598533)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1934854145598533 - 1 = (2 : ℕ)^2 * ((748807 : ℕ)^1 * ((645978919 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 1934854145598533)^967427072799266 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 748807 := Nat.prime_eq_prime_of_dvd_pow hq prime_748807 hd
        subst q
        change (2 : ZMod 1934854145598533)^2583915676 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 645978919 := Nat.prime_eq_prime_of_dvd_pow hq prime_645978919 hd
        subst q
        change (2 : ZMod 1934854145598533)^2995228 ≠ 1
        reduce_mod_char
        decide

theorem prime_1953827205882353 : Nat.Prime 1953827205882353 := by
  apply lucas_primality 1953827205882353 (3 : ZMod 1953827205882353)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1953827205882353 - 1 = (2 : ℕ)^4 * ((43 : ℕ)^1 * ((137 : ℕ)^1 * ((157 : ℕ)^1 * ((397 : ℕ)^1 * ((332573 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 1953827205882353)^976913602941176 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
        subst q
        change (3 : ZMod 1953827205882353)^45437841997264 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
          subst q
          change (3 : ZMod 1953827205882353)^14261512451696 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 157 := Nat.prime_eq_prime_of_dvd_pow hq prime_157 hd
            subst q
            change (3 : ZMod 1953827205882353)^12444759273136 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 397 := Nat.prime_eq_prime_of_dvd_pow hq prime_397 hd
              subst q
              change (3 : ZMod 1953827205882353)^4921479108016 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 332573 := Nat.prime_eq_prime_of_dvd_pow hq prime_332573 hd
              subst q
              change (3 : ZMod 1953827205882353)^5874882224 ≠ 1
              reduce_mod_char
              decide

theorem prime_1967974977554503 : Nat.Prime 1967974977554503 := by
  apply lucas_primality 1967974977554503 (5 : ZMod 1967974977554503)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1967974977554503 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((46856547084631 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 1967974977554503)^983987488777251 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 1967974977554503)^655991659184834 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 1967974977554503)^281139282507786 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 46856547084631 := Nat.prime_eq_prime_of_dvd_pow hq prime_46856547084631 hd
          subst q
          change (5 : ZMod 1967974977554503)^42 ≠ 1
          reduce_mod_char
          decide

theorem prime_2001566936265649 : Nat.Prime 2001566936265649 := by
  apply lucas_primality 2001566936265649 (17 : ZMod 2001566936265649)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2001566936265649 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((31 : ℕ)^1 * ((459691 : ℕ)^1 * ((2926181 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (17 : ZMod 2001566936265649)^1000783468132824 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (17 : ZMod 2001566936265649)^667188978755216 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (17 : ZMod 2001566936265649)^64566675363408 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 459691 := Nat.prime_eq_prime_of_dvd_pow hq prime_459691 hd
            subst q
            change (17 : ZMod 2001566936265649)^4354157328 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 2926181 := Nat.prime_eq_prime_of_dvd_pow hq prime_2926181 hd
            subst q
            change (17 : ZMod 2001566936265649)^684020208 ≠ 1
            reduce_mod_char
            decide

theorem prime_2035635367776319 : Nat.Prime 2035635367776319 := by
  apply lucas_primality 2035635367776319 (3 : ZMod 2035635367776319)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2035635367776319 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^3 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((523 : ℕ)^1 * ((1151 : ℕ)^1 * ((813277 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2035635367776319)^1017817683888159 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 2035635367776319)^678545122592106 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 2035635367776319)^290805052539474 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (3 : ZMod 2035635367776319)^185057760706938 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 523 := Nat.prime_eq_prime_of_dvd_pow hq prime_523 hd
              subst q
              change (3 : ZMod 2035635367776319)^3892228236666 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 1151 := Nat.prime_eq_prime_of_dvd_pow hq prime_1151 hd
                subst q
                change (3 : ZMod 2035635367776319)^1768579815618 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 813277 := Nat.prime_eq_prime_of_dvd_pow hq prime_813277 hd
                subst q
                change (3 : ZMod 2035635367776319)^2503003734 ≠ 1
                reduce_mod_char
                decide

theorem prime_2065049910713099 : Nat.Prime 2065049910713099 := by
  apply lucas_primality 2065049910713099 (2 : ZMod 2065049910713099)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2065049910713099 - 1 = (2 : ℕ)^1 * ((17 : ℕ)^1 * ((1259 : ℕ)^1 * ((48242066783 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2065049910713099)^1032524955356549 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 2065049910713099)^121473524159594 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 1259 := Nat.prime_eq_prime_of_dvd_pow hq prime_1259 hd
          subst q
          change (2 : ZMod 2065049910713099)^1640230270622 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 48242066783 := Nat.prime_eq_prime_of_dvd_pow hq prime_48242066783 hd
          subst q
          change (2 : ZMod 2065049910713099)^42806 ≠ 1
          reduce_mod_char
          decide

theorem prime_2070185663499853 : Nat.Prime 2070185663499853 := by
  apply lucas_primality 2070185663499853 (5 : ZMod 2070185663499853)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2070185663499853 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((3001 : ℕ)^1 * ((57485995321 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2070185663499853)^1035092831749926 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 2070185663499853)^690061887833284 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 3001 := Nat.prime_eq_prime_of_dvd_pow hq prime_3001 hd
          subst q
          change (5 : ZMod 2070185663499853)^689831943852 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 57485995321 := Nat.prime_eq_prime_of_dvd_pow hq prime_57485995321 hd
          subst q
          change (5 : ZMod 2070185663499853)^36012 ≠ 1
          reduce_mod_char
          decide

theorem prime_2105223260474947 : Nat.Prime 2105223260474947 := by
  apply lucas_primality 2105223260474947 (2 : ZMod 2105223260474947)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2105223260474947 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((350870543412491 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2105223260474947)^1052611630237473 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2105223260474947)^701741086824982 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 350870543412491 := Nat.prime_eq_prime_of_dvd_pow hq prime_350870543412491 hd
        subst q
        change (2 : ZMod 2105223260474947)^6 ≠ 1
        reduce_mod_char
        decide

theorem prime_2140753641621857 : Nat.Prime 2140753641621857 := by
  apply lucas_primality 2140753641621857 (3 : ZMod 2140753641621857)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2140753641621857 - 1 = (2 : ℕ)^5 * ((31 : ℕ)^1 * ((167 : ℕ)^1 * ((19403 : ℕ)^1 * ((665993 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2140753641621857)^1070376820810928 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
        subst q
        change (3 : ZMod 2140753641621857)^69056569084576 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 167 := Nat.prime_eq_prime_of_dvd_pow hq prime_167 hd
          subst q
          change (3 : ZMod 2140753641621857)^12818884081568 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19403 := Nat.prime_eq_prime_of_dvd_pow hq prime_19403 hd
            subst q
            change (3 : ZMod 2140753641621857)^110331064352 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 665993 := Nat.prime_eq_prime_of_dvd_pow hq prime_665993 hd
            subst q
            change (3 : ZMod 2140753641621857)^3214378592 ≠ 1
            reduce_mod_char
            decide

theorem prime_2176782336000007 : Nat.Prime 2176782336000007 := by
  apply lucas_primality 2176782336000007 (3 : ZMod 2176782336000007)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2176782336000007 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((85733 : ℕ)^1 * ((604529771 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2176782336000007)^1088391168000003 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 2176782336000007)^725594112000002 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 2176782336000007)^310968905142858 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 85733 := Nat.prime_eq_prime_of_dvd_pow hq prime_85733 hd
            subst q
            change (3 : ZMod 2176782336000007)^25390250382 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 604529771 := Nat.prime_eq_prime_of_dvd_pow hq prime_604529771 hd
            subst q
            change (3 : ZMod 2176782336000007)^3600786 ≠ 1
            reduce_mod_char
            decide

theorem prime_2182164376177633 : Nat.Prime 2182164376177633 := by
  apply lucas_primality 2182164376177633 (15 : ZMod 2182164376177633)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2182164376177633 - 1 = (2 : ℕ)^5 * ((3 : ℕ)^1 * ((7 : ℕ)^3 * ((11 : ℕ)^1 * ((19 : ℕ)^2 * ((127 : ℕ)^1 * ((331 : ℕ)^1 * ((397 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (15 : ZMod 2182164376177633)^1091082188088816 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (15 : ZMod 2182164376177633)^727388125392544 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (15 : ZMod 2182164376177633)^311737768025376 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (15 : ZMod 2182164376177633)^198378579652512 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
              subst q
              change (15 : ZMod 2182164376177633)^114850756640928 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 127 := Nat.prime_eq_prime_of_dvd_pow hq prime_127 hd
                subst q
                change (15 : ZMod 2182164376177633)^17182396662816 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 331 := Nat.prime_eq_prime_of_dvd_pow hq prime_331 hd
                  subst q
                  change (15 : ZMod 2182164376177633)^6592641619872 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 397 := Nat.prime_eq_prime_of_dvd_pow hq prime_397 hd
                  subst q
                  change (15 : ZMod 2182164376177633)^5496635708256 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_2213314919066189 : Nat.Prime 2213314919066189 := by
  apply lucas_primality 2213314919066189 (3 : ZMod 2213314919066189)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2213314919066189 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((31 : ℕ)^1 * ((37 : ℕ)^1 * ((331 : ℕ)^1 * ((397 : ℕ)^1 * ((499 : ℕ)^1 * ((1051 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2213314919066189)^1106657459533094 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (3 : ZMod 2213314919066189)^316187845580884 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (3 : ZMod 2213314919066189)^71397255453748 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
            subst q
            change (3 : ZMod 2213314919066189)^59819322136924 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 331 := Nat.prime_eq_prime_of_dvd_pow hq prime_331 hd
              subst q
              change (3 : ZMod 2213314919066189)^6686752021348 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 397 := Nat.prime_eq_prime_of_dvd_pow hq prime_397 hd
                subst q
                change (3 : ZMod 2213314919066189)^5575100551804 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 499 := Nat.prime_eq_prime_of_dvd_pow hq prime_499 hd
                  subst q
                  change (3 : ZMod 2213314919066189)^4435500839812 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 1051 := Nat.prime_eq_prime_of_dvd_pow hq prime_1051 hd
                  subst q
                  change (3 : ZMod 2213314919066189)^2105913338788 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_2250357012933187 : Nat.Prime 2250357012933187 := by
  apply lucas_primality 2250357012933187 (2 : ZMod 2250357012933187)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2250357012933187 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((43 : ℕ)^1 * ((15809 : ℕ)^1 * ((551730913 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2250357012933187)^1125178506466593 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2250357012933187)^750119004311062 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 43 := Nat.prime_eq_prime_of_dvd_pow hq prime_43 hd
          subst q
          change (2 : ZMod 2250357012933187)^52333884021702 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 15809 := Nat.prime_eq_prime_of_dvd_pow hq prime_15809 hd
            subst q
            change (2 : ZMod 2250357012933187)^142346575554 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 551730913 := Nat.prime_eq_prime_of_dvd_pow hq prime_551730913 hd
            subst q
            change (2 : ZMod 2250357012933187)^4078722 ≠ 1
            reduce_mod_char
            decide

theorem prime_2287914286629689 : Nat.Prime 2287914286629689 := by
  apply lucas_primality 2287914286629689 (3 : ZMod 2287914286629689)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2287914286629689 - 1 = (2 : ℕ)^3 * ((15510347 : ℕ)^1 * ((18438613 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2287914286629689)^1143957143314844 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 15510347 := Nat.prime_eq_prime_of_dvd_pow hq prime_15510347 hd
        subst q
        change (3 : ZMod 2287914286629689)^147508904 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 18438613 := Nat.prime_eq_prime_of_dvd_pow hq prime_18438613 hd
        subst q
        change (3 : ZMod 2287914286629689)^124082776 ≠ 1
        reduce_mod_char
        decide

theorem prime_2295792799700033 : Nat.Prime 2295792799700033 := by
  apply lucas_primality 2295792799700033 (3 : ZMod 2295792799700033)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2295792799700033 - 1 = (2 : ℕ)^6 * ((1129 : ℕ)^1 * ((141511 : ℕ)^1 * ((224527 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2295792799700033)^1147896399850016 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 1129 := Nat.prime_eq_prime_of_dvd_pow hq prime_1129 hd
        subst q
        change (3 : ZMod 2295792799700033)^2033474579008 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 141511 := Nat.prime_eq_prime_of_dvd_pow hq prime_141511 hd
          subst q
          change (3 : ZMod 2295792799700033)^16223422912 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 224527 := Nat.prime_eq_prime_of_dvd_pow hq prime_224527 hd
          subst q
          change (3 : ZMod 2295792799700033)^10225018816 ≠ 1
          reduce_mod_char
          decide

theorem prime_2325992456360009 : Nat.Prime 2325992456360009 := by
  apply lucas_primality 2325992456360009 (3 : ZMod 2325992456360009)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2325992456360009 - 1 = (2 : ℕ)^3 * ((73 : ℕ)^1 * ((39107 : ℕ)^1 * ((101845291 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2325992456360009)^1162996228180004 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 73 := Nat.prime_eq_prime_of_dvd_pow hq prime_73 hd
        subst q
        change (3 : ZMod 2325992456360009)^31862910361096 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 39107 := Nat.prime_eq_prime_of_dvd_pow hq prime_39107 hd
          subst q
          change (3 : ZMod 2325992456360009)^59477649944 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 101845291 := Nat.prime_eq_prime_of_dvd_pow hq prime_101845291 hd
          subst q
          change (3 : ZMod 2325992456360009)^22838488 ≠ 1
          reduce_mod_char
          decide

theorem prime_2331164160168421 : Nat.Prime 2331164160168421 := by
  apply lucas_primality 2331164160168421 (6 : ZMod 2331164160168421)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2331164160168421 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((19 : ℕ)^2 * ((53 : ℕ)^1 * ((317 : ℕ)^1 * ((2287 : ℕ)^1 * ((2801 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 2331164160168421)^1165582080084210 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 2331164160168421)^777054720056140 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 2331164160168421)^466232832033684 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 19 := Nat.prime_eq_prime_of_dvd_pow hq prime_19 hd
            subst q
            change (6 : ZMod 2331164160168421)^122692850535180 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 53 := Nat.prime_eq_prime_of_dvd_pow hq prime_53 hd
              subst q
              change (6 : ZMod 2331164160168421)^43984229437140 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 317 := Nat.prime_eq_prime_of_dvd_pow hq prime_317 hd
                subst q
                change (6 : ZMod 2331164160168421)^7353830158260 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 2287 := Nat.prime_eq_prime_of_dvd_pow hq prime_2287 hd
                  subst q
                  change (6 : ZMod 2331164160168421)^1019310957660 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 2801 := Nat.prime_eq_prime_of_dvd_pow hq prime_2801 hd
                  subst q
                  change (6 : ZMod 2331164160168421)^832261392420 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_2364597285765643 : Nat.Prime 2364597285765643 := by
  apply lucas_primality 2364597285765643 (11 : ZMod 2364597285765643)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2364597285765643 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^2 * ((131366515875869 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 2364597285765643)^1182298642882821 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 2364597285765643)^788199095255214 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 131366515875869 := Nat.prime_eq_prime_of_dvd_pow hq prime_131366515875869 hd
        subst q
        change (11 : ZMod 2364597285765643)^18 ≠ 1
        reduce_mod_char
        decide

theorem prime_2403734586186823 : Nat.Prime 2403734586186823 := by
  apply lucas_primality 2403734586186823 (5 : ZMod 2403734586186823)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2403734586186823 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((59 : ℕ)^1 * ((389 : ℕ)^1 * ((467 : ℕ)^1 * ((5339723 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2403734586186823)^1201867293093411 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 2403734586186823)^801244862062274 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (5 : ZMod 2403734586186823)^343390655169546 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
            subst q
            change (5 : ZMod 2403734586186823)^40741264172658 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 389 := Nat.prime_eq_prime_of_dvd_pow hq prime_389 hd
              subst q
              change (5 : ZMod 2403734586186823)^6179266288398 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 467 := Nat.prime_eq_prime_of_dvd_pow hq prime_467 hd
                subst q
                change (5 : ZMod 2403734586186823)^5147183268066 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 5339723 := Nat.prime_eq_prime_of_dvd_pow hq prime_5339723 hd
                subst q
                change (5 : ZMod 2403734586186823)^450160914 ≠ 1
                reduce_mod_char
                decide

theorem prime_2441226577797401 : Nat.Prime 2441226577797401 := by
  apply lucas_primality 2441226577797401 (3 : ZMod 2441226577797401)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2441226577797401 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^2 * ((29 : ℕ)^1 * ((79 : ℕ)^1 * ((5327862457 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2441226577797401)^1220613288898700 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 2441226577797401)^488245315559480 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (3 : ZMod 2441226577797401)^84180226820600 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
            subst q
            change (3 : ZMod 2441226577797401)^30901602250600 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 5327862457 := Nat.prime_eq_prime_of_dvd_pow hq prime_5327862457 hd
            subst q
            change (3 : ZMod 2441226577797401)^458200 ≠ 1
            reduce_mod_char
            decide

theorem prime_2443410216924907 : Nat.Prime 2443410216924907 := by
  apply lucas_primality 2443410216924907 (5 : ZMod 2443410216924907)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2443410216924907 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((23 : ℕ)^1 * ((79 : ℕ)^1 * ((10253 : ℕ)^1 * ((21859451 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 2443410216924907)^1221705108462453 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 2443410216924907)^814470072308302 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
          subst q
          change (5 : ZMod 2443410216924907)^106235226822822 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
            subst q
            change (5 : ZMod 2443410216924907)^30929243252214 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 10253 := Nat.prime_eq_prime_of_dvd_pow hq prime_10253 hd
              subst q
              change (5 : ZMod 2443410216924907)^238311734802 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 21859451 := Nat.prime_eq_prime_of_dvd_pow hq prime_21859451 hd
              subst q
              change (5 : ZMod 2443410216924907)^111778206 ≠ 1
              reduce_mod_char
              decide

theorem prime_2449367942477539 : Nat.Prime 2449367942477539 := by
  apply lucas_primality 2449367942477539 (3 : ZMod 2449367942477539)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2449367942477539 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((37 : ℕ)^1 * ((137 : ℕ)^1 * ((57349 : ℕ)^1 * ((1404283 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2449367942477539)^1224683971238769 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 2449367942477539)^816455980825846 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 37 := Nat.prime_eq_prime_of_dvd_pow hq prime_37 hd
          subst q
          change (3 : ZMod 2449367942477539)^66199133580474 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 137 := Nat.prime_eq_prime_of_dvd_pow hq prime_137 hd
            subst q
            change (3 : ZMod 2449367942477539)^17878598120274 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 57349 := Nat.prime_eq_prime_of_dvd_pow hq prime_57349 hd
              subst q
              change (3 : ZMod 2449367942477539)^42709863162 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 1404283 := Nat.prime_eq_prime_of_dvd_pow hq prime_1404283 hd
              subst q
              change (3 : ZMod 2449367942477539)^1744212486 ≠ 1
              reduce_mod_char
              decide

theorem prime_2483630085505031 : Nat.Prime 2483630085505031 := by
  apply lucas_primality 2483630085505031 (7 : ZMod 2483630085505031)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2483630085505031 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((11 : ℕ)^1 * ((4057 : ℕ)^1 * ((795044027 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (7 : ZMod 2483630085505031)^1241815042752515 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (7 : ZMod 2483630085505031)^496726017101006 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (7 : ZMod 2483630085505031)^354804297929290 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
            subst q
            change (7 : ZMod 2483630085505031)^225784553227730 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 4057 := Nat.prime_eq_prime_of_dvd_pow hq prime_4057 hd
              subst q
              change (7 : ZMod 2483630085505031)^612183900790 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 795044027 := Nat.prime_eq_prime_of_dvd_pow hq prime_795044027 hd
              subst q
              change (7 : ZMod 2483630085505031)^3123890 ≠ 1
              reduce_mod_char
              decide

theorem prime_2524400147941307 : Nat.Prime 2524400147941307 := by
  apply lucas_primality 2524400147941307 (2 : ZMod 2524400147941307)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2524400147941307 - 1 = (2 : ℕ)^1 * ((101 : ℕ)^1 * ((12497030435353 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2524400147941307)^1262200073970653 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
        subst q
        change (2 : ZMod 2524400147941307)^24994060870706 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 12497030435353 := Nat.prime_eq_prime_of_dvd_pow hq prime_12497030435353 hd
        subst q
        change (2 : ZMod 2524400147941307)^202 ≠ 1
        reduce_mod_char
        decide

theorem prime_2565726409000019 : Nat.Prime 2565726409000019 := by
  apply lucas_primality 2565726409000019 (2 : ZMod 2565726409000019)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2565726409000019 - 1 = (2 : ℕ)^1 * ((11 : ℕ)^1 * ((17 : ℕ)^1 * ((443 : ℕ)^1 * ((1721 : ℕ)^1 * ((8998169 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2565726409000019)^1282863204500009 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 11 := Nat.prime_eq_prime_of_dvd_pow hq prime_11 hd
        subst q
        change (2 : ZMod 2565726409000019)^233247855363638 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 2565726409000019)^150925082882354 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 443 := Nat.prime_eq_prime_of_dvd_pow hq prime_443 hd
            subst q
            change (2 : ZMod 2565726409000019)^5791707469526 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1721 := Nat.prime_eq_prime_of_dvd_pow hq prime_1721 hd
              subst q
              change (2 : ZMod 2565726409000019)^1490834636258 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 8998169 := Nat.prime_eq_prime_of_dvd_pow hq prime_8998169 hd
              subst q
              change (2 : ZMod 2565726409000019)^285138722 ≠ 1
              reduce_mod_char
              decide

theorem prime_2607614922465733 : Nat.Prime 2607614922465733 := by
  apply lucas_primality 2607614922465733 (2 : ZMod 2607614922465733)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2607614922465733 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((10433 : ℕ)^1 * ((20828260667 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2607614922465733)^1303807461232866 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2607614922465733)^869204974155244 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 10433 := Nat.prime_eq_prime_of_dvd_pow hq prime_10433 hd
          subst q
          change (2 : ZMod 2607614922465733)^249939128004 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 20828260667 := Nat.prime_eq_prime_of_dvd_pow hq prime_20828260667 hd
          subst q
          change (2 : ZMod 2607614922465733)^125196 ≠ 1
          reduce_mod_char
          decide

theorem prime_2614581651726601 : Nat.Prime 2614581651726601 := by
  apply lucas_primality 2614581651726601 (11 : ZMod 2614581651726601)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2614581651726601 - 1 = (2 : ℕ)^3 * ((3 : ℕ)^1 * ((5 : ℕ)^2 * ((17 : ℕ)^1 * ((61 : ℕ)^1 * ((97 : ℕ)^1 * ((571 : ℕ)^1 * ((75869 : ℕ)^1))))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (11 : ZMod 2614581651726601)^1307290825863300 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (11 : ZMod 2614581651726601)^871527217242200 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (11 : ZMod 2614581651726601)^522916330345320 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (11 : ZMod 2614581651726601)^153798920689800 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
              subst q
              change (11 : ZMod 2614581651726601)^42861994290600 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 97 := Nat.prime_eq_prime_of_dvd_pow hq prime_97 hd
                subst q
                change (11 : ZMod 2614581651726601)^26954450017800 ≠ 1
                reduce_mod_char
                decide
              · rcases hq.dvd_mul.mp hd with hd | hd
                · have heq : q = 571 := Nat.prime_eq_prime_of_dvd_pow hq prime_571 hd
                  subst q
                  change (11 : ZMod 2614581651726601)^4578952104600 ≠ 1
                  reduce_mod_char
                  decide
                · have heq : q = 75869 := Nat.prime_eq_prime_of_dvd_pow hq prime_75869 hd
                  subst q
                  change (11 : ZMod 2614581651726601)^34461791400 ≠ 1
                  reduce_mod_char
                  decide

theorem prime_2650071791407109 : Nat.Prime 2650071791407109 := by
  apply lucas_primality 2650071791407109 (2 : ZMod 2650071791407109)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2650071791407109 - 1 = (2 : ℕ)^2 * ((17 : ℕ)^1 * ((98929 : ℕ)^1 * ((393935489 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2650071791407109)^1325035895703554 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
        subst q
        change (2 : ZMod 2650071791407109)^155886575965124 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 98929 := Nat.prime_eq_prime_of_dvd_pow hq prime_98929 hd
          subst q
          change (2 : ZMod 2650071791407109)^26787613252 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 393935489 := Nat.prime_eq_prime_of_dvd_pow hq prime_393935489 hd
          subst q
          change (2 : ZMod 2650071791407109)^6727172 ≠ 1
          reduce_mod_char
          decide

theorem prime_2693103168443717 : Nat.Prime 2693103168443717 := by
  apply lucas_primality 2693103168443717 (2 : ZMod 2693103168443717)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2693103168443717 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((79 : ℕ)^1 * ((139 : ℕ)^1 * ((1009 : ℕ)^1 * ((1747 : ℕ)^1 * ((4969 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2693103168443717)^1346551584221858 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 2693103168443717)^384729024063388 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 79 := Nat.prime_eq_prime_of_dvd_pow hq prime_79 hd
          subst q
          change (2 : ZMod 2693103168443717)^34089913524604 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 139 := Nat.prime_eq_prime_of_dvd_pow hq prime_139 hd
            subst q
            change (2 : ZMod 2693103168443717)^19374842938444 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 1009 := Nat.prime_eq_prime_of_dvd_pow hq prime_1009 hd
              subst q
              change (2 : ZMod 2693103168443717)^2669081435524 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 1747 := Nat.prime_eq_prime_of_dvd_pow hq prime_1747 hd
                subst q
                change (2 : ZMod 2693103168443717)^1541558768428 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 4969 := Nat.prime_eq_prime_of_dvd_pow hq prime_4969 hd
                subst q
                change (2 : ZMod 2693103168443717)^541980915364 ≠ 1
                reduce_mod_char
                decide

theorem prime_2709302035245031 : Nat.Prime 2709302035245031 := by
  apply lucas_primality 2709302035245031 (6 : ZMod 2709302035245031)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2709302035245031 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^4 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((196753960439 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 2709302035245031)^1354651017622515 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 2709302035245031)^903100678415010 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 2709302035245031)^541860407049006 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (6 : ZMod 2709302035245031)^159370707955590 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 196753960439 := Nat.prime_eq_prime_of_dvd_pow hq prime_196753960439 hd
            subst q
            change (6 : ZMod 2709302035245031)^13770 ≠ 1
            reduce_mod_char
            decide

theorem prime_2735415594194071 : Nat.Prime 2735415594194071 := by
  apply lucas_primality 2735415594194071 (3 : ZMod 2735415594194071)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2735415594194071 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((9430877 : ℕ)^1 * ((9668297 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2735415594194071)^1367707797097035 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 2735415594194071)^911805198064690 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 2735415594194071)^547083118838814 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 9430877 := Nat.prime_eq_prime_of_dvd_pow hq prime_9430877 hd
            subst q
            change (3 : ZMod 2735415594194071)^290048910 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 9668297 := Nat.prime_eq_prime_of_dvd_pow hq prime_9668297 hd
            subst q
            change (3 : ZMod 2735415594194071)^282926310 ≠ 1
            reduce_mod_char
            decide

theorem prime_2736715256013391 : Nat.Prime 2736715256013391 := by
  apply lucas_primality 2736715256013391 (3 : ZMod 2736715256013391)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2736715256013391 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((59 : ℕ)^1 * ((1546166811307 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2736715256013391)^1368357628006695 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 2736715256013391)^912238418671130 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 2736715256013391)^547343051202678 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
            subst q
            change (3 : ZMod 2736715256013391)^46385004339210 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 1546166811307 := Nat.prime_eq_prime_of_dvd_pow hq prime_1546166811307 hd
            subst q
            change (3 : ZMod 2736715256013391)^1770 ≠ 1
            reduce_mod_char
            decide

theorem prime_2780914306640681 : Nat.Prime 2780914306640681 := by
  apply lucas_primality 2780914306640681 (3 : ZMod 2780914306640681)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2780914306640681 - 1 = (2 : ℕ)^3 * ((5 : ℕ)^1 * ((7 : ℕ)^1 * ((59 : ℕ)^1 * ((168336217109 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 2780914306640681)^1390457153320340 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (3 : ZMod 2780914306640681)^556182861328136 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (3 : ZMod 2780914306640681)^397273472377240 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
            subst q
            change (3 : ZMod 2780914306640681)^47134140790520 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 168336217109 := Nat.prime_eq_prime_of_dvd_pow hq prime_168336217109 hd
            subst q
            change (3 : ZMod 2780914306640681)^16520 ≠ 1
            reduce_mod_char
            decide

theorem prime_2825706623205413 : Nat.Prime 2825706623205413 := by
  apply lucas_primality 2825706623205413 (2 : ZMod 2825706623205413)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2825706623205413 - 1 = (2 : ℕ)^2 * ((706426655801353 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2825706623205413)^1412853311602706 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 706426655801353 := Nat.prime_eq_prime_of_dvd_pow hq prime_706426655801353 hd
      subst q
      change (2 : ZMod 2825706623205413)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_2871098559212693 : Nat.Prime 2871098559212693 := by
  apply lucas_primality 2871098559212693 (2 : ZMod 2871098559212693)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2871098559212693 - 1 = (2 : ℕ)^2 * ((189691 : ℕ)^1 * ((3783915103 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2871098559212693)^1435549279606346 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 189691 := Nat.prime_eq_prime_of_dvd_pow hq prime_189691 hd
        subst q
        change (2 : ZMod 2871098559212693)^15135660412 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 3783915103 := Nat.prime_eq_prime_of_dvd_pow hq prime_3783915103 hd
        subst q
        change (2 : ZMod 2871098559212693)^758764 ≠ 1
        reduce_mod_char
        decide

theorem prime_2875623967691989 : Nat.Prime 2875623967691989 := by
  apply lucas_primality 2875623967691989 (10 : ZMod 2875623967691989)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2875623967691989 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((34057 : ℕ)^1 * ((7036301807 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (10 : ZMod 2875623967691989)^1437811983845994 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (10 : ZMod 2875623967691989)^958541322563996 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 34057 := Nat.prime_eq_prime_of_dvd_pow hq prime_34057 hd
          subst q
          change (10 : ZMod 2875623967691989)^84435621684 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 7036301807 := Nat.prime_eq_prime_of_dvd_pow hq prime_7036301807 hd
          subst q
          change (10 : ZMod 2875623967691989)^408684 ≠ 1
          reduce_mod_char
          decide

theorem prime_2917096519063147 : Nat.Prime 2917096519063147 := by
  apply lucas_primality 2917096519063147 (2 : ZMod 2917096519063147)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2917096519063147 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((41 : ℕ)^1 * ((26557 : ℕ)^1 * ((63787949 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 2917096519063147)^1458548259531573 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 2917096519063147)^972365506354382 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (2 : ZMod 2917096519063147)^416728074151878 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 41 := Nat.prime_eq_prime_of_dvd_pow hq prime_41 hd
            subst q
            change (2 : ZMod 2917096519063147)^71148695586906 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 26557 := Nat.prime_eq_prime_of_dvd_pow hq prime_26557 hd
              subst q
              change (2 : ZMod 2917096519063147)^109842848178 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 63787949 := Nat.prime_eq_prime_of_dvd_pow hq prime_63787949 hd
              subst q
              change (2 : ZMod 2917096519063147)^45731154 ≠ 1
              reduce_mod_char
              decide

theorem prime_2963706958323731 : Nat.Prime 2963706958323731 := by
  apply lucas_primality 2963706958323731 (6 : ZMod 2963706958323731)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2963706958323731 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((101 : ℕ)^1 * ((2934363325073 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 2963706958323731)^1481853479161865 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (6 : ZMod 2963706958323731)^592741391664746 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 101 := Nat.prime_eq_prime_of_dvd_pow hq prime_101 hd
          subst q
          change (6 : ZMod 2963706958323731)^29343633250730 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 2934363325073 := Nat.prime_eq_prime_of_dvd_pow hq prime_2934363325073 hd
          subst q
          change (6 : ZMod 2963706958323731)^1010 ≠ 1
          reduce_mod_char
          decide

theorem prime_3010936384000157 : Nat.Prime 3010936384000157 := by
  apply lucas_primality 3010936384000157 (2 : ZMod 3010936384000157)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3010936384000157 - 1 = (2 : ℕ)^2 * ((293 : ℕ)^1 * ((24953 : ℕ)^1 * ((102955891 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3010936384000157)^1505468192000078 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 293 := Nat.prime_eq_prime_of_dvd_pow hq prime_293 hd
        subst q
        change (2 : ZMod 3010936384000157)^10276233392492 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 24953 := Nat.prime_eq_prime_of_dvd_pow hq prime_24953 hd
          subst q
          change (2 : ZMod 3010936384000157)^120664304252 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 102955891 := Nat.prime_eq_prime_of_dvd_pow hq prime_102955891 hd
          subst q
          change (2 : ZMod 3010936384000157)^29244916 ≠ 1
          reduce_mod_char
          decide

theorem prime_3058791354808313 : Nat.Prime 3058791354808313 := by
  apply lucas_primality 3058791354808313 (3 : ZMod 3058791354808313)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3058791354808313 - 1 = (2 : ℕ)^3 * ((382348919351039 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3058791354808313)^1529395677404156 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 382348919351039 := Nat.prime_eq_prime_of_dvd_pow hq prime_382348919351039 hd
      subst q
      change (3 : ZMod 3058791354808313)^8 ≠ 1
      reduce_mod_char
      decide

theorem prime_3107278481449157 : Nat.Prime 3107278481449157 := by
  apply lucas_primality 3107278481449157 (2 : ZMod 3107278481449157)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3107278481449157 - 1 = (2 : ℕ)^2 * ((7 : ℕ)^1 * ((17 : ℕ)^1 * ((1804963 : ℕ)^1 * ((3616637 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3107278481449157)^1553639240724578 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
        subst q
        change (2 : ZMod 3107278481449157)^443896925921308 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
          subst q
          change (2 : ZMod 3107278481449157)^182781087144068 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 1804963 := Nat.prime_eq_prime_of_dvd_pow hq prime_1804963 hd
            subst q
            change (2 : ZMod 3107278481449157)^1721519212 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 3616637 := Nat.prime_eq_prime_of_dvd_pow hq prime_3616637 hd
            subst q
            change (2 : ZMod 3107278481449157)^859162388 ≠ 1
            reduce_mod_char
            decide

theorem prime_3133708715890637 : Nat.Prime 3133708715890637 := by
  apply lucas_primality 3133708715890637 (2 : ZMod 3133708715890637)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3133708715890637 - 1 = (2 : ℕ)^2 * ((13 : ℕ)^1 * ((31 : ℕ)^1 * ((47 : ℕ)^1 * ((41361447599 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3133708715890637)^1566854357945318 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
        subst q
        change (2 : ZMod 3133708715890637)^241054516606972 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 31 := Nat.prime_eq_prime_of_dvd_pow hq prime_31 hd
          subst q
          change (2 : ZMod 3133708715890637)^101087377931956 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 47 := Nat.prime_eq_prime_of_dvd_pow hq prime_47 hd
            subst q
            change (2 : ZMod 3133708715890637)^66674653529588 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 41361447599 := Nat.prime_eq_prime_of_dvd_pow hq prime_41361447599 hd
            subst q
            change (2 : ZMod 3133708715890637)^75764 ≠ 1
            reduce_mod_char
            decide

theorem prime_3156404426880773 : Nat.Prime 3156404426880773 := by
  apply lucas_primality 3156404426880773 (2 : ZMod 3156404426880773)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3156404426880773 - 1 = (2 : ℕ)^2 * ((789101106720193 : ℕ)^1) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3156404426880773)^1578202213440386 ≠ 1
      reduce_mod_char
      decide
    · have heq : q = 789101106720193 := Nat.prime_eq_prime_of_dvd_pow hq prime_789101106720193 hd
      subst q
      change (2 : ZMod 3156404426880773)^4 ≠ 1
      reduce_mod_char
      decide

theorem prime_3206175906594821 : Nat.Prime 3206175906594821 := by
  apply lucas_primality 3206175906594821 (2 : ZMod 3206175906594821)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3206175906594821 - 1 = (2 : ℕ)^2 * ((5 : ℕ)^1 * ((29 : ℕ)^1 * ((5527889494129 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3206175906594821)^1603087953297410 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 3206175906594821)^641235181318964 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 29 := Nat.prime_eq_prime_of_dvd_pow hq prime_29 hd
          subst q
          change (2 : ZMod 3206175906594821)^110557789882580 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 5527889494129 := Nat.prime_eq_prime_of_dvd_pow hq prime_5527889494129 hd
          subst q
          change (2 : ZMod 3206175906594821)^580 ≠ 1
          reduce_mod_char
          decide

theorem prime_3256599688890631 : Nat.Prime 3256599688890631 := by
  apply lucas_primality 3256599688890631 (15 : ZMod 3256599688890631)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3256599688890631 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((5081 : ℕ)^1 * ((52189 : ℕ)^1 * ((409369 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (15 : ZMod 3256599688890631)^1628299844445315 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (15 : ZMod 3256599688890631)^1085533229630210 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (15 : ZMod 3256599688890631)^651319937778126 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 5081 := Nat.prime_eq_prime_of_dvd_pow hq prime_5081 hd
            subst q
            change (15 : ZMod 3256599688890631)^640936762230 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 52189 := Nat.prime_eq_prime_of_dvd_pow hq prime_52189 hd
              subst q
              change (15 : ZMod 3256599688890631)^62400116670 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 409369 := Nat.prime_eq_prime_of_dvd_pow hq prime_409369 hd
              subst q
              change (15 : ZMod 3256599688890631)^7955169270 ≠ 1
              reduce_mod_char
              decide

theorem prime_3307682595151939 : Nat.Prime 3307682595151939 := by
  apply lucas_primality 3307682595151939 (2 : ZMod 3307682595151939)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3307682595151939 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((59 : ℕ)^1 * ((9931 : ℕ)^1 * ((940865587 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3307682595151939)^1653841297575969 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3307682595151939)^1102560865050646 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 59 := Nat.prime_eq_prime_of_dvd_pow hq prime_59 hd
          subst q
          change (2 : ZMod 3307682595151939)^56062416866982 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 9931 := Nat.prime_eq_prime_of_dvd_pow hq prime_9931 hd
            subst q
            change (2 : ZMod 3307682595151939)^333066417798 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 940865587 := Nat.prime_eq_prime_of_dvd_pow hq prime_940865587 hd
            subst q
            change (2 : ZMod 3307682595151939)^3515574 ≠ 1
            reduce_mod_char
            decide

theorem prime_3359431500123631 : Nat.Prime 3359431500123631 := by
  apply lucas_primality 3359431500123631 (3 : ZMod 3359431500123631)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3359431500123631 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((23 : ℕ)^1 * ((332567 : ℕ)^1 * ((14639881 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (3 : ZMod 3359431500123631)^1679715750061815 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (3 : ZMod 3359431500123631)^1119810500041210 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (3 : ZMod 3359431500123631)^671886300024726 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23 := Nat.prime_eq_prime_of_dvd_pow hq prime_23 hd
            subst q
            change (3 : ZMod 3359431500123631)^146062239135810 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 332567 := Nat.prime_eq_prime_of_dvd_pow hq prime_332567 hd
              subst q
              change (3 : ZMod 3359431500123631)^10101517890 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 14639881 := Nat.prime_eq_prime_of_dvd_pow hq prime_14639881 hd
              subst q
              change (3 : ZMod 3359431500123631)^229471230 ≠ 1
              reduce_mod_char
              decide

theorem prime_3367738284728717 : Nat.Prime 3367738284728717 := by
  apply lucas_primality 3367738284728717 (2 : ZMod 3367738284728717)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3367738284728717 - 1 = (2 : ℕ)^2 * ((2976671 : ℕ)^1 * ((282844349 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3367738284728717)^1683869142364358 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 2976671 := Nat.prime_eq_prime_of_dvd_pow hq prime_2976671 hd
        subst q
        change (2 : ZMod 3367738284728717)^1131377396 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 282844349 := Nat.prime_eq_prime_of_dvd_pow hq prime_282844349 hd
        subst q
        change (2 : ZMod 3367738284728717)^11906684 ≠ 1
        reduce_mod_char
        decide

theorem prime_3373029086240113 : Nat.Prime 3373029086240113 := by
  apply lucas_primality 3373029086240113 (5 : ZMod 3373029086240113)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3373029086240113 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((5405495330513 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3373029086240113)^1686514543120056 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 3373029086240113)^1124343028746704 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (5 : ZMod 3373029086240113)^259463775864624 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 5405495330513 := Nat.prime_eq_prime_of_dvd_pow hq prime_5405495330513 hd
          subst q
          change (5 : ZMod 3373029086240113)^624 ≠ 1
          reduce_mod_char
          decide

theorem prime_3411853332189277 : Nat.Prime 3411853332189277 := by
  apply lucas_primality 3411853332189277 (2 : ZMod 3411853332189277)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3411853332189277 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((13 : ℕ)^1 * ((71 : ℕ)^1 * ((70327 : ℕ)^1 * ((4380113 : ℕ)^1))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3411853332189277)^1705926666094638 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (2 : ZMod 3411853332189277)^1137284444063092 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 13 := Nat.prime_eq_prime_of_dvd_pow hq prime_13 hd
          subst q
          change (2 : ZMod 3411853332189277)^262450256322252 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 71 := Nat.prime_eq_prime_of_dvd_pow hq prime_71 hd
            subst q
            change (2 : ZMod 3411853332189277)^48054272284356 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 70327 := Nat.prime_eq_prime_of_dvd_pow hq prime_70327 hd
              subst q
              change (2 : ZMod 3411853332189277)^48514131588 ≠ 1
              reduce_mod_char
              decide
            · have heq : q = 4380113 := Nat.prime_eq_prime_of_dvd_pow hq prime_4380113 hd
              subst q
              change (2 : ZMod 3411853332189277)^778941852 ≠ 1
              reduce_mod_char
              decide

theorem prime_3464955073649171 : Nat.Prime 3464955073649171 := by
  apply lucas_primality 3464955073649171 (2 : ZMod 3464955073649171)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3464955073649171 - 1 = (2 : ℕ)^1 * ((5 : ℕ)^1 * ((61 : ℕ)^1 * ((37657 : ℕ)^1 * ((150841921 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (2 : ZMod 3464955073649171)^1732477536824585 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
        subst q
        change (2 : ZMod 3464955073649171)^692991014729834 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 61 := Nat.prime_eq_prime_of_dvd_pow hq prime_61 hd
          subst q
          change (2 : ZMod 3464955073649171)^56802542190970 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 37657 := Nat.prime_eq_prime_of_dvd_pow hq prime_37657 hd
            subst q
            change (2 : ZMod 3464955073649171)^92013571810 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 150841921 := Nat.prime_eq_prime_of_dvd_pow hq prime_150841921 hd
            subst q
            change (2 : ZMod 3464955073649171)^22970770 ≠ 1
            reduce_mod_char
            decide

theorem prime_3504444348291541 : Nat.Prime 3504444348291541 := by
  apply lucas_primality 3504444348291541 (6 : ZMod 3504444348291541)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3504444348291541 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^1 * ((5 : ℕ)^1 * ((17 : ℕ)^1 * ((263 : ℕ)^1 * ((63577 : ℕ)^1 * ((205477 : ℕ)^1)))))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (6 : ZMod 3504444348291541)^1752222174145770 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (6 : ZMod 3504444348291541)^1168148116097180 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 5 := Nat.prime_eq_prime_of_dvd_pow hq prime_5 hd
          subst q
          change (6 : ZMod 3504444348291541)^700888869658308 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 17 := Nat.prime_eq_prime_of_dvd_pow hq prime_17 hd
            subst q
            change (6 : ZMod 3504444348291541)^206143785193620 ≠ 1
            reduce_mod_char
            decide
          · rcases hq.dvd_mul.mp hd with hd | hd
            · have heq : q = 263 := Nat.prime_eq_prime_of_dvd_pow hq prime_263 hd
              subst q
              change (6 : ZMod 3504444348291541)^13324883453580 ≠ 1
              reduce_mod_char
              decide
            · rcases hq.dvd_mul.mp hd with hd | hd
              · have heq : q = 63577 := Nat.prime_eq_prime_of_dvd_pow hq prime_63577 hd
                subst q
                change (6 : ZMod 3504444348291541)^55121260020 ≠ 1
                reduce_mod_char
                decide
              · have heq : q = 205477 := Nat.prime_eq_prime_of_dvd_pow hq prime_205477 hd
                subst q
                change (6 : ZMod 3504444348291541)^17055166020 ≠ 1
                reduce_mod_char
                decide

theorem prime_3518743761000049 : Nat.Prime 3518743761000049 := by
  apply lucas_primality 3518743761000049 (19 : ZMod 3518743761000049)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3518743761000049 - 1 = (2 : ℕ)^4 * ((3 : ℕ)^1 * ((7 : ℕ)^1 * ((10472451669643 : ℕ)^1))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (19 : ZMod 3518743761000049)^1759371880500024 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (19 : ZMod 3518743761000049)^1172914587000016 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 7 := Nat.prime_eq_prime_of_dvd_pow hq prime_7 hd
          subst q
          change (19 : ZMod 3518743761000049)^502677680142864 ≠ 1
          reduce_mod_char
          decide
        · have heq : q = 10472451669643 := Nat.prime_eq_prime_of_dvd_pow hq prime_10472451669643 hd
          subst q
          change (19 : ZMod 3518743761000049)^336 ≠ 1
          reduce_mod_char
          decide

theorem prime_3569166425248267 : Nat.Prime 3569166425248267 := by
  apply lucas_primality 3569166425248267 (5 : ZMod 3569166425248267)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3569166425248267 - 1 = (2 : ℕ)^1 * ((3 : ℕ)^1 * ((151 : ℕ)^1 * ((23603 : ℕ)^1 * ((166905787 : ℕ)^1)))) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (5 : ZMod 3569166425248267)^1784583212624133 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (5 : ZMod 3569166425248267)^1189722141749422 ≠ 1
        reduce_mod_char
        decide
      · rcases hq.dvd_mul.mp hd with hd | hd
        · have heq : q = 151 := Nat.prime_eq_prime_of_dvd_pow hq prime_151 hd
          subst q
          change (5 : ZMod 3569166425248267)^23636863743366 ≠ 1
          reduce_mod_char
          decide
        · rcases hq.dvd_mul.mp hd with hd | hd
          · have heq : q = 23603 := Nat.prime_eq_prime_of_dvd_pow hq prime_23603 hd
            subst q
            change (5 : ZMod 3569166425248267)^151216643022 ≠ 1
            reduce_mod_char
            decide
          · have heq : q = 166905787 := Nat.prime_eq_prime_of_dvd_pow hq prime_166905787 hd
            subst q
            change (5 : ZMod 3569166425248267)^21384318 ≠ 1
            reduce_mod_char
            decide

theorem prime_3573226485213877 : Nat.Prime 3573226485213877 := by
  apply lucas_primality 3573226485213877 (29 : ZMod 3573226485213877)
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3573226485213877 - 1 = (2 : ℕ)^2 * ((3 : ℕ)^3 * ((33085430418647 : ℕ)^1)) := by norm_num
    rw [hfac] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have heq : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq prime_2 hd
      subst q
      change (29 : ZMod 3573226485213877)^1786613242606938 ≠ 1
      reduce_mod_char
      decide
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have heq : q = 3 := Nat.prime_eq_prime_of_dvd_pow hq prime_3 hd
        subst q
        change (29 : ZMod 3573226485213877)^1191075495071292 ≠ 1
        reduce_mod_char
        decide
      · have heq : q = 33085430418647 := Nat.prime_eq_prime_of_dvd_pow hq prime_33085430418647 hd
        subst q
        change (29 : ZMod 3573226485213877)^108 ≠ 1
        reduce_mod_char
        decide

end LegendreK6.Pratt
