import LegendreK6.M2Pilot.Enclosures.Height014
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height014
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 448 ≤ i.val) (hhi : i.val < 480) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (448 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_448.trans
      change ((1587431374575 / 70368744177664 : ℚ) : ℝ) ≤ ((6349725498300 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_448.trans
      change ((253962522235455 / 35184372088832 : ℚ) : ℝ) ≤ ((2031700177883640 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (449 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_449.trans
      change ((1548201997935 / 70368744177664 : ℚ) : ℝ) ≤ ((6192807991740 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_449.trans
      change ((2036221112402245 / 281474976710656 : ℚ) : ℝ) ≤ ((2036221112402245 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (450 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_450.trans
      change ((1509941405497 / 70368744177664 : ℚ) : ℝ) ≤ ((6039765621988 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_450.trans
      change ((2040741993293091 / 281474976710656 : ℚ) : ℝ) ≤ ((2040741993293091 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (451 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_451.trans
      change ((5890502759773 / 281474976710656 : ℚ) : ℝ) ≤ ((5890502759773 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_451.trans
      change ((1022631410301481 / 140737488355328 : ℚ) : ℝ) ≤ ((2045262820602962 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (452 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_452.trans
      change ((5744926133971 / 281474976710656 : ℚ) : ℝ) ≤ ((5744926133971 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_452.trans
      change ((2049783594378583 / 281474976710656 : ℚ) : ℝ) ≤ ((2049783594378583 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (453 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_453.trans
      change ((1400736193375 / 70368744177664 : ℚ) : ℝ) ≤ ((5602944773500 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_453.trans
      change ((2054304314666617 / 281474976710656 : ℚ) : ℝ) ≤ ((2054304314666617 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (454 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_454.trans
      change ((5464469950649 / 281474976710656 : ℚ) : ℝ) ≤ ((5464469950649 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_454.trans
      change ((1029412490756833 / 140737488355328 : ℚ) : ℝ) ≤ ((2058824981513666 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (455 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_455.trans
      change ((1332353781449 / 70368744177664 : ℚ) : ℝ) ≤ ((5329415125796 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_455.trans
      change ((8059943730337 / 1099511627776 : ℚ) : ℝ) ≤ ((2063345594966272 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (456 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_456.trans
      change ((324855993343 / 17592186044416 : ℚ) : ℝ) ≤ ((5197695893488 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_456.trans
      change ((1033933077535457 / 140737488355328 : ℚ) : ℝ) ≤ ((2067866155070914 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (457 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_457.trans
      change ((39603358827 / 2199023255552 : ℚ) : ℝ) ≤ ((5069229929856 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_457.trans
      change ((2072386661874013 / 281474976710656 : ℚ) : ℝ) ≤ ((2072386661874013 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (458 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_458.trans
      change ((19312253677 / 1099511627776 : ℚ) : ℝ) ≤ ((4943936941312 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_458.trans
      change ((259613389427741 / 35184372088832 : ℚ) : ℝ) ≤ ((2076907115421928 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (459 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_459.trans
      change ((2410869307261 / 140737488355328 : ℚ) : ℝ) ≤ ((4821738614522 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_459.trans
      change ((1040713757880479 / 140737488355328 : ℚ) : ℝ) ≤ ((2081427515760958 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (460 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_460.trans
      change ((4702558567603 / 281474976710656 : ℚ) : ℝ) ≤ ((4702558567603 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_460.trans
      change ((521486965734335 / 70368744177664 : ℚ) : ℝ) ≤ ((2085947862937340 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (461 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_461.trans
      change ((4586322302523 / 281474976710656 : ℚ) : ℝ) ≤ ((4586322302523 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_461.trans
      change ((1045234078498627 / 140737488355328 : ℚ) : ℝ) ≤ ((2090468156997254 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (462 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_462.trans
      change ((1118239289669 / 70368744177664 : ℚ) : ℝ) ≤ ((4472957158676 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_462.trans
      change ((1047494198993409 / 140737488355328 : ℚ) : ℝ) ≤ ((2094988397986818 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (463 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_463.trans
      change ((2181196133799 / 140737488355328 : ℚ) : ℝ) ≤ ((4362392267598 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_463.trans
      change ((2099508585952089 / 281474976710656 : ℚ) : ℝ) ≤ ((2099508585952089 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (464 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_464.trans
      change ((4254558508795 / 281474976710656 : ℚ) : ℝ) ≤ ((4254558508795 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_464.trans
      change ((2104028720939065 / 281474976710656 : ℚ) : ℝ) ≤ ((2104028720939065 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (465 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_465.trans
      change ((4149388466669 / 281474976710656 : ℚ) : ℝ) ≤ ((4149388466669 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_465.trans
      change ((2108548802993685 / 281474976710656 : ℚ) : ℝ) ≤ ((2108548802993685 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (466 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_466.trans
      change ((4046816388491 / 281474976710656 : ℚ) : ℝ) ≤ ((4046816388491 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_466.trans
      change ((2113068832161827 / 281474976710656 : ℚ) : ℝ) ≤ ((2113068832161827 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (467 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_467.trans
      change ((986694535855 / 70368744177664 : ℚ) : ℝ) ≤ ((3946778143420 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_467.trans
      change ((2117588808489311 / 281474976710656 : ℚ) : ℝ) ≤ ((2117588808489311 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (468 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_468.trans
      change ((1924605591263 / 140737488355328 : ℚ) : ℝ) ≤ ((3849211182526 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_468.trans
      change ((2122108732021895 / 281474976710656 : ℚ) : ℝ) ≤ ((2122108732021895 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (469 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_469.trans
      change ((469256812475 / 35184372088832 : ℚ) : ℝ) ≤ ((3754054499800 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_469.trans
      change ((66457143837665 / 8796093022208 : ℚ) : ℝ) ≤ ((2126628602805280 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (470 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_470.trans
      change ((3661248594121 / 281474976710656 : ℚ) : ℝ) ≤ ((3661248594121 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_470.trans
      change ((1065574210442553 / 140737488355328 : ℚ) : ℝ) ≤ ((2131148420885106 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (471 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_471.trans
      change ((3570735432163 / 281474976710656 : ℚ) : ℝ) ≤ ((3570735432163 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_471.trans
      change ((1067834093153477 / 140737488355328 : ℚ) : ℝ) ≤ ((2135668186306954 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (472 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_472.trans
      change ((1741229206107 / 140737488355328 : ℚ) : ℝ) ≤ ((3482458412214 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_472.trans
      change ((535046974779087 / 70368744177664 : ℚ) : ℝ) ≤ ((2140187899116348 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (473 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_473.trans
      change ((3396362328889 / 281474976710656 : ℚ) : ℝ) ≤ ((3396362328889 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_473.trans
      change ((1072353779679375 / 140737488355328 : ℚ) : ℝ) ≤ ((2144707559358750 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (474 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_474.trans
      change ((3312393338705 / 281474976710656 : ℚ) : ℝ) ≤ ((3312393338705 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_474.trans
      change ((2149227167079565 / 281474976710656 : ℚ) : ℝ) ≤ ((2149227167079565 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (475 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_475.trans
      change ((3230498926511 / 281474976710656 : ℚ) : ℝ) ≤ ((3230498926511 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_475.trans
      change ((1076873361162069 / 140737488355328 : ℚ) : ℝ) ≤ ((2153746722324138 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (476 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_476.trans
      change ((3150627872745 / 281474976710656 : ℚ) : ℝ) ≤ ((3150627872745 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_476.trans
      change ((2158266225137757 / 281474976710656 : ℚ) : ℝ) ≤ ((2158266225137757 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (477 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_477.trans
      change ((3072730221491 / 281474976710656 : ℚ) : ℝ) ≤ ((3072730221491 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_477.trans
      change ((2162785675565649 / 281474976710656 : ℚ) : ℝ) ≤ ((2162785675565649 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (478 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_478.trans
      change ((187297328083 / 17592186044416 : ℚ) : ℝ) ≤ ((2996757249328 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_478.trans
      change ((1083652536826493 / 140737488355328 : ℚ) : ℝ) ≤ ((2167305073652986 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (479 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height014.height_factor_upper_479.trans
      change ((730665358737 / 70368744177664 : ℚ) : ℝ) ≤ ((2922661434948 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height014.height_power_upper_479.trans
      change ((2171824419444877 / 281474976710656 : ℚ) : ℝ) ≤ ((2171824419444877 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height014
