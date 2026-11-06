import LegendreK6.M2Pilot.Enclosures.Height013
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height013
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 416 ≤ i.val) (hhi : i.val < 448) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (416 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_416.trans
      change ((3534652748949 / 70368744177664 : ℚ) : ℝ) ≤ ((14138610995796 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_416.trans
      change ((117937604663891 / 17592186044416 : ℚ) : ℝ) ≤ ((1887001674622256 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (417 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_417.trans
      change ((13789409788611 / 281474976710656 : ℚ) : ℝ) ≤ ((13789409788611 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_417.trans
      change ((1891524350303743 / 281474976710656 : ℚ) : ℝ) ≤ ((1891524350303743 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (418 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_418.trans
      change ((6724413573305 / 140737488355328 : ℚ) : ℝ) ≤ ((13448827146610 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_418.trans
      change ((948023485413687 / 140737488355328 : ℚ) : ℝ) ≤ ((1896046970827374 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (419 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_419.trans
      change ((13116650514009 / 281474976710656 : ℚ) : ℝ) ≤ ((13116650514009 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_419.trans
      change ((1900569536241951 / 281474976710656 : ℚ) : ℝ) ≤ ((1900569536241951 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (420 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_420.trans
      change ((12792672573169 / 281474976710656 : ℚ) : ℝ) ≤ ((12792672573169 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_420.trans
      change ((1905092046596211 / 281474976710656 : ℚ) : ℝ) ≤ ((1905092046596211 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (421 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_421.trans
      change ((12476691115613 / 281474976710656 : ℚ) : ℝ) ≤ ((12476691115613 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_421.trans
      change ((1909614501938825 / 281474976710656 : ℚ) : ℝ) ≤ ((1909614501938825 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (422 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_422.trans
      change ((6084254458105 / 140737488355328 : ℚ) : ℝ) ≤ ((12168508916210 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_422.trans
      change ((1914136902318403 / 281474976710656 : ℚ) : ℝ) ≤ ((1914136902318403 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (423 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_423.trans
      change ((11867933610465 / 281474976710656 : ℚ) : ℝ) ≤ ((11867933610465 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_423.trans
      change ((1918659247783485 / 281474976710656 : ℚ) : ℝ) ≤ ((1918659247783485 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (424 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_424.trans
      change ((11574777574821 / 281474976710656 : ℚ) : ℝ) ≤ ((11574777574821 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_424.trans
      change ((1923181538382553 / 281474976710656 : ℚ) : ℝ) ≤ ((1923181538382553 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (425 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_425.trans
      change ((5644428904955 / 140737488355328 : ℚ) : ℝ) ≤ ((11288857809910 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_425.trans
      change ((1927703774164019 / 281474976710656 : ℚ) : ℝ) ≤ ((1927703774164019 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (426 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_426.trans
      change ((11009995826675 / 281474976710656 : ℚ) : ℝ) ≤ ((11009995826675 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_426.trans
      change ((483056488794059 / 70368744177664 : ℚ) : ℝ) ≤ ((1932225955176236 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (427 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_427.trans
      change ((10738017535291 / 281474976710656 : ℚ) : ℝ) ≤ ((10738017535291 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_427.trans
      change ((1936748081467489 / 281474976710656 : ℚ) : ℝ) ≤ ((1936748081467489 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (428 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_428.trans
      change ((2618188284207 / 70368744177664 : ℚ) : ℝ) ≤ ((10472753136828 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_428.trans
      change ((970635076543001 / 140737488355328 : ℚ) : ℝ) ≤ ((1941270153086002 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (429 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_429.trans
      change ((2553509254393 / 70368744177664 : ℚ) : ℝ) ≤ ((10214037017572 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_429.trans
      change ((972896085039967 / 140737488355328 : ℚ) : ℝ) ≤ ((1945792170079934 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (430 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_430.trans
      change ((9961707645947 / 281474976710656 : ℚ) : ℝ) ≤ ((9961707645947 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_430.trans
      change ((487578533124345 / 70368744177664 : ℚ) : ℝ) ≤ ((1950314132497380 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (431 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_431.trans
      change ((9715607471979 / 281474976710656 : ℚ) : ℝ) ≤ ((9715607471979 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_431.trans
      change ((1954836040386373 / 281474976710656 : ℚ) : ℝ) ≤ ((1954836040386373 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (432 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_432.trans
      change ((9475582829229 / 281474976710656 : ℚ) : ℝ) ≤ ((9475582829229 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_432.trans
      change ((979678946897441 / 140737488355328 : ℚ) : ℝ) ≤ ((1959357893794882 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (433 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_433.trans
      change ((9241483839141 / 281474976710656 : ℚ) : ℝ) ≤ ((9241483839141 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_433.trans
      change ((1963879692770811 / 281474976710656 : ℚ) : ℝ) ≤ ((1963879692770811 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (434 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_434.trans
      change ((9013164317745 / 281474976710656 : ℚ) : ℝ) ≤ ((9013164317745 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_434.trans
      change ((1968401437362003 / 281474976710656 : ℚ) : ℝ) ≤ ((1968401437362003 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (435 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_435.trans
      change ((2197620421163 / 70368744177664 : ℚ) : ℝ) ≤ ((8790481684652 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_435.trans
      change ((1972923127616237 / 281474976710656 : ℚ) : ℝ) ≤ ((1972923127616237 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (436 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_436.trans
      change ((4286648437149 / 140737488355328 : ℚ) : ℝ) ≤ ((8573296874298 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_436.trans
      change ((1977444763581231 / 281474976710656 : ℚ) : ℝ) ≤ ((1977444763581231 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (437 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_437.trans
      change ((522592140585 / 17592186044416 : ℚ) : ℝ) ≤ ((8361474249360 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_437.trans
      change ((495491586326159 / 70368744177664 : ℚ) : ℝ) ≤ ((1981966345304636 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (438 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_438.trans
      change ((8154881516313 / 281474976710656 : ℚ) : ℝ) ≤ ((8154881516313 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_438.trans
      change ((1986487872834045 / 281474976710656 : ℚ) : ℝ) ≤ ((1986487872834045 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (439 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_439.trans
      change ((1988347410765 / 70368744177664 : ℚ) : ℝ) ≤ ((7953389643060 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_439.trans
      change ((248876168277123 / 35184372088832 : ℚ) : ℝ) ≤ ((1991009346216984 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (440 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_440.trans
      change ((7756872778593 / 281474976710656 : ℚ) : ℝ) ≤ ((7756872778593 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_440.trans
      change ((249441345687615 / 35184372088832 : ℚ) : ℝ) ≤ ((1995530765500920 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (441 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_441.trans
      change ((7565208174625 / 281474976710656 : ℚ) : ℝ) ≤ ((7565208174625 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_441.trans
      change ((2000052130733257 / 281474976710656 : ℚ) : ℝ) ≤ ((2000052130733257 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (442 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_442.trans
      change ((7378276109163 / 281474976710656 : ℚ) : ℝ) ≤ ((7378276109163 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_442.trans
      change ((1002286720980667 / 140737488355328 : ℚ) : ℝ) ≤ ((2004573441961334 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (443 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_443.trans
      change ((7195959811945 / 281474976710656 : ℚ) : ℝ) ≤ ((7195959811945 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_443.trans
      change ((125568418702027 / 17592186044416 : ℚ) : ℝ) ≤ ((2009094699232432 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (444 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_444.trans
      change ((7018145391731 / 281474976710656 : ℚ) : ℝ) ≤ ((7018145391731 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_444.trans
      change ((1006807951296883 / 140737488355328 : ℚ) : ℝ) ≤ ((2013615902593766 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (445 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_445.trans
      change ((3422360882685 / 140737488355328 : ℚ) : ℝ) ≤ ((6844721765370 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_445.trans
      change ((504534263023123 / 70368744177664 : ℚ) : ℝ) ≤ ((2018137052092492 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (446 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_446.trans
      change ((6675580588619 / 281474976710656 : ℚ) : ℝ) ≤ ((6675580588619 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_446.trans
      change ((1011329073887851 / 140737488355328 : ℚ) : ℝ) ≤ ((2022658147775702 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (447 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height013.height_factor_upper_447.trans
      change ((6510616188663 / 281474976710656 : ℚ) : ℝ) ≤ ((6510616188663 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height013.height_power_upper_447.trans
      change ((506794797422607 / 70368744177664 : ℚ) : ℝ) ≤ ((2027179189690428 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height013
