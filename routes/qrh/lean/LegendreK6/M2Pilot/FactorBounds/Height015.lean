import LegendreK6.M2Pilot.Enclosures.Height015
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height015
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 480 ≤ i.val) (hhi : i.val < 512) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (480 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_480.trans
      change ((2850396429515 / 281474976710656 : ℚ) : ℝ) ≤ ((2850396429515 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_480.trans
      change ((272042964123297 / 35184372088832 : ℚ) : ℝ) ≤ ((2176343712986376 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (481 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_481.trans
      change ((1389958513881 / 140737488355328 : ℚ) : ℝ) ≤ ((2779917027762 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_481.trans
      change ((2180862954322479 / 281474976710656 : ℚ) : ℝ) ≤ ((2180862954322479 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (482 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_482.trans
      change ((677794784949 / 70368744177664 : ℚ) : ℝ) ≤ ((2711179139796 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_482.trans
      change ((2185382143498121 / 281474976710656 : ℚ) : ℝ) ≤ ((2185382143498121 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (483 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_483.trans
      change ((165258735225 / 17592186044416 : ℚ) : ℝ) ≤ ((2644139763600 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_483.trans
      change ((2189901280558183 / 281474976710656 : ℚ) : ℝ) ≤ ((2189901280558183 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (484 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_484.trans
      change ((2578756958207 / 281474976710656 : ℚ) : ℝ) ≤ ((2578756958207 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_484.trans
      change ((548605091386871 / 70368744177664 : ℚ) : ℝ) ≤ ((2194420365547484 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (485 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_485.trans
      change ((1257494908771 / 140737488355328 : ℚ) : ℝ) ≤ ((2514989817542 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_485.trans
      change ((2198939398510789 / 281474976710656 : ℚ) : ℝ) ≤ ((2198939398510789 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (486 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_486.trans
      change ((2452798444907 / 281474976710656 : ℚ) : ℝ) ≤ ((2452798444907 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_486.trans
      change ((1101729189746401 / 140737488355328 : ℚ) : ℝ) ≤ ((2203458379492802 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (487 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_487.trans
      change ((2392143928085 / 281474976710656 : ℚ) : ℝ) ≤ ((2392143928085 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_487.trans
      change ((2207977308538171 / 281474976710656 : ℚ) : ℝ) ≤ ((2207977308538171 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (488 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_488.trans
      change ((2332988315075 / 281474976710656 : ℚ) : ℝ) ≤ ((2332988315075 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_488.trans
      change ((2212496185691487 / 281474976710656 : ℚ) : ℝ) ≤ ((2212496185691487 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (489 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_489.trans
      change ((284411823801 / 35184372088832 : ℚ) : ℝ) ≤ ((2275294590408 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_489.trans
      change ((2217015010997283 / 281474976710656 : ℚ) : ℝ) ≤ ((2217015010997283 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (490 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_490.trans
      change ((2219026652059 / 281474976710656 : ℚ) : ℝ) ≤ ((2219026652059 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_490.trans
      change ((1110766892250017 / 140737488355328 : ℚ) : ℝ) ≤ ((2221533784500034 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (491 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_491.trans
      change ((2164149288915 / 281474976710656 : ℚ) : ℝ) ≤ ((2164149288915 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_491.trans
      change ((34782070410065 / 4398046511104 : ℚ) : ℝ) ≤ ((2226052506244160 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (492 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_492.trans
      change ((1055314079407 / 140737488355328 : ℚ) : ℝ) ≤ ((2110628158814 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_492.trans
      change ((557642794068505 / 70368744177664 : ℚ) : ℝ) ≤ ((2230571176274020 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (493 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_493.trans
      change ((257303720889 / 35184372088832 : ℚ) : ℝ) ≤ ((2058429767112 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_493.trans
      change ((34923278041155 / 4398046511104 : ℚ) : ℝ) ≤ ((2235089794633920 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (494 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_494.trans
      change ((250940180723 / 35184372088832 : ℚ) : ℝ) ≤ ((2007521445784 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_494.trans
      change ((559902090342027 / 70368744177664 : ℚ) : ℝ) ≤ ((2239608361368108 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (495 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_495.trans
      change ((122366958315 / 17592186044416 : ℚ) : ℝ) ≤ ((1957871333040 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_495.trans
      change ((2244126876520773 / 281474976710656 : ℚ) : ℝ) ≤ ((2244126876520773 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (496 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_496.trans
      change ((954724176719 / 140737488355328 : ℚ) : ℝ) ≤ ((1909448353438 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_496.trans
      change ((2248645340136049 / 281474976710656 : ℚ) : ℝ) ≤ ((2248645340136049 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (497 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_497.trans
      change ((931111099249 / 140737488355328 : ℚ) : ℝ) ≤ ((1862222198498 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_497.trans
      change ((2253163752258015 / 281474976710656 : ℚ) : ℝ) ≤ ((2253163752258015 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (498 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_498.trans
      change ((1816163307781 / 281474976710656 : ℚ) : ℝ) ≤ ((1816163307781 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_498.trans
      change ((1128841056465345 / 140737488355328 : ℚ) : ℝ) ≤ ((2257682112930690 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (499 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_499.trans
      change ((442810712611 / 70368744177664 : ℚ) : ℝ) ≤ ((1771242850444 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_499.trans
      change ((282775052774755 / 35184372088832 : ℚ) : ℝ) ≤ ((2262200422198040 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (500 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_500.trans
      change ((1727432707243 / 281474976710656 : ℚ) : ℝ) ≤ ((1727432707243 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_500.trans
      change ((2266718680103971 / 281474976710656 : ℚ) : ℝ) ≤ ((2266718680103971 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (501 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_501.trans
      change ((842352726493 / 140737488355328 : ℚ) : ℝ) ≤ ((1684705452986 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_501.trans
      change ((2271236886692337 / 281474976710656 : ℚ) : ℝ) ≤ ((2271236886692337 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (502 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_502.trans
      change ((1643034339411 / 281474976710656 : ℚ) : ℝ) ≤ ((1643034339411 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_502.trans
      change ((568938760501733 / 70368744177664 : ℚ) : ℝ) ≤ ((2275755042006932 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (503 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_503.trans
      change ((801196639245 / 140737488355328 : ℚ) : ℝ) ≤ ((1602393278490 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_503.trans
      change ((2280273146091497 / 281474976710656 : ℚ) : ℝ) ≤ ((2280273146091497 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (504 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_504.trans
      change ((1562756826149 / 281474976710656 : ℚ) : ℝ) ≤ ((1562756826149 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_504.trans
      change ((1142395599494857 / 140737488355328 : ℚ) : ℝ) ≤ ((2284791198989714 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (505 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_505.trans
      change ((1524100166379 / 281474976710656 : ℚ) : ℝ) ≤ ((1524100166379 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_505.trans
      change ((572327300186303 / 70368744177664 : ℚ) : ℝ) ≤ ((2289309200745212 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (506 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_506.trans
      change ((1486399095745 / 281474976710656 : ℚ) : ℝ) ≤ ((1486399095745 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_506.trans
      change ((2293827151401563 / 281474976710656 : ℚ) : ℝ) ≤ ((2293827151401563 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (507 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_507.trans
      change ((1449630008281 / 281474976710656 : ℚ) : ℝ) ≤ ((1449630008281 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_507.trans
      change ((2298345051002283 / 281474976710656 : ℚ) : ℝ) ≤ ((2298345051002283 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (508 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_508.trans
      change ((1413769880743 / 281474976710656 : ℚ) : ℝ) ≤ ((1413769880743 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_508.trans
      change ((2302862899590833 / 281474976710656 : ℚ) : ℝ) ≤ ((2302862899590833 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (509 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_509.trans
      change ((1378796258245 / 281474976710656 : ℚ) : ℝ) ≤ ((1378796258245 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_509.trans
      change ((2307380697210619 / 281474976710656 : ℚ) : ℝ) ≤ ((2307380697210619 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (510 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_510.trans
      change ((168085905029 / 35184372088832 : ℚ) : ℝ) ≤ ((1344687240232 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_510.trans
      change ((1155949221952495 / 140737488355328 : ℚ) : ℝ) ≤ ((2311898443904990 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (511 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height015.height_factor_upper_511.trans
      change ((1311421466805 / 281474976710656 : ℚ) : ℝ) ≤ ((1311421466805 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height015.height_power_upper_511.trans
      change ((2316416139717241 / 281474976710656 : ℚ) : ℝ) ≤ ((2316416139717241 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height015
