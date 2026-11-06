import LegendreK6.M3Far.Enclosures.Sigma011
import LegendreK6.M3FarIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M3Far.FactorBounds.Sigma011
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 384) (hlo : 352 ≤ i.val) (hhi : i.val < 384) :
    sigmaFactor i ≤ sigmaDyadicFactor i ∧ sigmaPower i ≤ sigmaDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (352 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_352.trans
      change ((4305547 / 281474976710656 : ℚ) : ℝ) ≤ ((4305547 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_352.trans
      change ((2535810600997 / 35184372088832 : ℚ) : ℝ) ≤ ((20286484807976 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (353 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_353.trans
      change ((633175 / 35184372088832 : ℚ) : ℝ) ≤ ((5065400 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_353.trans
      change ((19669144610945 / 281474976710656 : ℚ) : ℝ) ≤ ((19669144610945 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (354 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_354.trans
      change ((5957053 / 281474976710656 : ℚ) : ℝ) ≤ ((5957053 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_354.trans
      change ((19050759845053 / 281474976710656 : ℚ) : ℝ) ≤ ((19050759845053 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (355 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_355.trans
      change ((875369 / 35184372088832 : ℚ) : ℝ) ≤ ((7002952 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_355.trans
      change ((18431327856865 / 281474976710656 : ℚ) : ℝ) ≤ ((18431327856865 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (356 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_356.trans
      change ((8229289 / 281474976710656 : ℚ) : ℝ) ≤ ((8229289 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_356.trans
      change ((1113177873997 / 17592186044416 : ℚ) : ℝ) ≤ ((17810845983952 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (357 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_357.trans
      change ((2416655 / 70368744177664 : ℚ) : ℝ) ≤ ((9666620 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_357.trans
      change ((8594655777425 / 140737488355328 : ℚ) : ℝ) ≤ ((17189311554850 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (358 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_358.trans
      change ((5675285 / 140737488355328 : ℚ) : ℝ) ≤ ((11350570 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_358.trans
      change ((8283360944513 / 140737488355328 : ℚ) : ℝ) ≤ ((16566721889026 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (359 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_359.trans
      change ((6661329 / 140737488355328 : ℚ) : ℝ) ≤ ((13322658 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_359.trans
      change ((15943074296837 / 281474976710656 : ℚ) : ℝ) ≤ ((15943074296837 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (360 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_360.trans
      change ((7815629 / 140737488355328 : ℚ) : ℝ) ≤ ((15631258 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_360.trans
      change ((3829591519873 / 70368744177664 : ℚ) : ℝ) ≤ ((15318366079492 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (361 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_361.trans
      change ((18332697 / 281474976710656 : ℚ) : ℝ) ≤ ((18332697 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_361.trans
      change ((14692594529011 / 281474976710656 : ℚ) : ℝ) ≤ ((14692594529011 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (362 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_362.trans
      change ((10746269 / 140737488355328 : ℚ) : ℝ) ≤ ((21492538 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_362.trans
      change ((3516439232047 / 70368744177664 : ℚ) : ℝ) ≤ ((14065756928188 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (363 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_363.trans
      change ((25187065 / 281474976710656 : ℚ) : ℝ) ≤ ((25187065 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_363.trans
      change ((1679731318819 / 35184372088832 : ℚ) : ℝ) ≤ ((13437850550552 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (364 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_364.trans
      change ((14752495 / 140737488355328 : ℚ) : ℝ) ≤ ((29504990 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_364.trans
      change ((6404436330163 / 140737488355328 : ℚ) : ℝ) ≤ ((12808872660326 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (365 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_365.trans
      change ((539835 / 4398046511104 : ℚ) : ℝ) ≤ ((34549440 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_365.trans
      change ((12178820512389 / 281474976710656 : ℚ) : ℝ) ≤ ((12178820512389 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (366 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_366.trans
      change ((2527515 / 17592186044416 : ℚ) : ℝ) ≤ ((40440240 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_366.trans
      change ((11547691352233 / 281474976710656 : ℚ) : ℝ) ≤ ((11547691352233 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (367 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_367.trans
      change ((47316561 / 281474976710656 : ℚ) : ℝ) ≤ ((47316561 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_367.trans
      change ((5457741207963 / 140737488355328 : ℚ) : ℝ) ≤ ((10915482415926 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (368 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_368.trans
      change ((27669985 / 140737488355328 : ℚ) : ℝ) ≤ ((55339970 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_368.trans
      change ((5141095465035 / 140737488355328 : ℚ) : ℝ) ≤ ((10282190930070 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (369 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_369.trans
      change ((64697947 / 281474976710656 : ℚ) : ℝ) ≤ ((64697947 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_369.trans
      change ((4823907055881 / 140737488355328 : ℚ) : ℝ) ≤ ((9647814111762 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (370 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_370.trans
      change ((4725497 / 17592186044416 : ℚ) : ℝ) ≤ ((75607952 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_370.trans
      change ((1126543646069 / 35184372088832 : ℚ) : ℝ) ≤ ((9012349168552 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (371 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_371.trans
      change ((44161051 / 140737488355328 : ℚ) : ℝ) ≤ ((88322102 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_371.trans
      change ((8375793298401 / 281474976710656 : ℚ) : ℝ) ≤ ((8375793298401 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (372 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_372.trans
      change ((25783141 / 70368744177664 : ℚ) : ℝ) ≤ ((103132564 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_372.trans
      change ((7738143689641 / 281474976710656 : ℚ) : ℝ) ≤ ((7738143689641 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (373 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_373.trans
      change ((30094441 / 70368744177664 : ℚ) : ℝ) ≤ ((120377764 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_373.trans
      change ((3549698760467 / 140737488355328 : ℚ) : ℝ) ≤ ((7099397520934 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (374 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_374.trans
      change ((35112385 / 70368744177664 : ℚ) : ℝ) ≤ ((140449540 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_374.trans
      change ((403721997577 / 17592186044416 : ℚ) : ℝ) ≤ ((6459551961232 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (375 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_375.trans
      change ((81900679 / 140737488355328 : ℚ) : ℝ) ≤ ((163801358 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_375.trans
      change ((2909302084865 / 140737488355328 : ℚ) : ℝ) ≤ ((5818604169730 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (376 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_376.trans
      change ((11934861 / 17592186044416 : ℚ) : ℝ) ≤ ((190957776 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_376.trans
      change ((5176551295829 / 281474976710656 : ℚ) : ℝ) ≤ ((5176551295829 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (377 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_377.trans
      change ((111262655 / 140737488355328 : ℚ) : ℝ) ≤ ((222525310 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_377.trans
      change ((4533390479091 / 281474976710656 : ℚ) : ℝ) ≤ ((4533390479091 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (378 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_378.trans
      change ((259204917 / 281474976710656 : ℚ) : ℝ) ≤ ((259204917 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_378.trans
      change ((1944559424599 / 140737488355328 : ℚ) : ℝ) ≤ ((3889118849198 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (379 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_379.trans
      change ((301806333 / 281474976710656 : ℚ) : ℝ) ≤ ((301806333 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_379.trans
      change ((810933381477 / 70368744177664 : ℚ) : ℝ) ≤ ((3243733525908 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (380 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_380.trans
      change ((87816131 / 70368744177664 : ℚ) : ℝ) ≤ ((351264524 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_380.trans
      change ((2597231619015 / 281474976710656 : ℚ) : ℝ) ≤ ((2597231619015 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (381 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_381.trans
      change ((408658555 / 281474976710656 : ℚ) : ℝ) ≤ ((408658555 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_381.trans
      change ((1949610228299 / 281474976710656 : ℚ) : ℝ) ≤ ((1949610228299 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (382 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_382.trans
      change ((59404153 / 35184372088832 : ℚ) : ℝ) ≤ ((475233224 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_382.trans
      change ((1300866443493 / 281474976710656 : ℚ) : ℝ) ≤ ((1300866443493 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (383 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_383.trans
      change ((276211927 / 140737488355328 : ℚ) : ℝ) ≤ ((552423854 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_383.trans
      change ((650997344229 / 281474976710656 : ℚ) : ℝ) ≤ ((650997344229 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M3Far.FactorBounds.Sigma011
