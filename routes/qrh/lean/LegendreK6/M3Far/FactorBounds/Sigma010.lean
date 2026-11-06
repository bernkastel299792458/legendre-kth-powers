import LegendreK6.M3Far.Enclosures.Sigma010
import LegendreK6.M3FarIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M3Far.FactorBounds.Sigma010
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 384) (hlo : 320 ≤ i.val) (hhi : i.val < 352) :
    sigmaFactor i ≤ sigmaDyadicFactor i ∧ sigmaPower i ≤ sigmaDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (320 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_320.trans
      change ((17267 / 281474976710656 : ℚ) : ℝ) ≤ ((17267 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_320.trans
      change ((39505259889215 / 281474976710656 : ℚ) : ℝ) ≤ ((39505259889215 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (321 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_321.trans
      change ((5139 / 70368744177664 : ℚ) : ℝ) ≤ ((20556 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_321.trans
      change ((19459998389873 / 140737488355328 : ℚ) : ℝ) ≤ ((38919996779746 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (322 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_322.trans
      change ((24463 / 281474976710656 : ℚ) : ℝ) ≤ ((24463 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_322.trans
      change ((38333769480639 / 281474976710656 : ℚ) : ℝ) ≤ ((38333769480639 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (323 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_323.trans
      change ((29103 / 281474976710656 : ℚ) : ℝ) ≤ ((29103 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_323.trans
      change ((37746575607255 / 281474976710656 : ℚ) : ℝ) ≤ ((37746575607255 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (324 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_324.trans
      change ((17305 / 140737488355328 : ℚ) : ℝ) ≤ ((34610 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_324.trans
      change ((9289603191771 / 70368744177664 : ℚ) : ℝ) ≤ ((37158412767084 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (325 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_325.trans
      change ((5143 / 35184372088832 : ℚ) : ℝ) ≤ ((41144 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_325.trans
      change ((36569278559711 / 281474976710656 : ℚ) : ℝ) ≤ ((36569278559711 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (326 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_326.trans
      change ((48895 / 281474976710656 : ℚ) : ℝ) ≤ ((48895 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_326.trans
      change ((17989585288395 / 140737488355328 : ℚ) : ℝ) ≤ ((35979170576790 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (327 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_327.trans
      change ((58085 / 281474976710656 : ℚ) : ℝ) ≤ ((58085 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_327.trans
      change ((17694043201001 / 140737488355328 : ℚ) : ℝ) ≤ ((35388086402002 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (328 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_328.trans
      change ((68977 / 281474976710656 : ℚ) : ℝ) ≤ ((68977 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_328.trans
      change ((34796023611031 / 281474976710656 : ℚ) : ℝ) ≤ ((34796023611031 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (329 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_329.trans
      change ((40941 / 140737488355328 : ℚ) : ℝ) ≤ ((81882 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_329.trans
      change ((34202979771525 / 281474976710656 : ℚ) : ℝ) ≤ ((34202979771525 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (330 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_330.trans
      change ((48583 / 140737488355328 : ℚ) : ℝ) ≤ ((97166 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_330.trans
      change ((4201119055383 / 35184372088832 : ℚ) : ℝ) ≤ ((33608952443064 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (331 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_331.trans
      change ((115261 / 281474976710656 : ℚ) : ℝ) ≤ ((115261 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_331.trans
      change ((33013939177129 / 281474976710656 : ℚ) : ℝ) ≤ ((33013939177129 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (332 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_332.trans
      change ((136675 / 281474976710656 : ℚ) : ℝ) ≤ ((136675 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_332.trans
      change ((4052242189633 / 35184372088832 : ℚ) : ℝ) ≤ ((32417937517064 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (333 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_333.trans
      change ((81005 / 140737488355328 : ℚ) : ℝ) ≤ ((162010 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_333.trans
      change ((15910472499023 / 140737488355328 : ℚ) : ℝ) ≤ ((31820944998046 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (334 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_334.trans
      change ((191969 / 281474976710656 : ℚ) : ℝ) ≤ ((191969 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_334.trans
      change ((31222959147051 / 281474976710656 : ℚ) : ℝ) ≤ ((31222959147051 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (335 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_335.trans
      change ((227385 / 281474976710656 : ℚ) : ℝ) ≤ ((227385 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_335.trans
      change ((15311988741407 / 140737488355328 : ℚ) : ℝ) ≤ ((30623977482814 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (336 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_336.trans
      change ((67309 / 70368744177664 : ℚ) : ℝ) ≤ ((269236 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_336.trans
      change ((7505999378951 / 70368744177664 : ℚ) : ℝ) ≤ ((30023997515804 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (337 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_337.trans
      change ((19917 / 17592186044416 : ℚ) : ℝ) ≤ ((318672 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_337.trans
      change ((29423016748181 / 281474976710656 : ℚ) : ℝ) ≤ ((29423016748181 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (338 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_338.trans
      change ((377045 / 281474976710656 : ℚ) : ℝ) ≤ ((377045 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_338.trans
      change ((3602629084221 / 35184372088832 : ℚ) : ℝ) ≤ ((28821032673768 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (339 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_339.trans
      change ((445945 / 281474976710656 : ℚ) : ℝ) ≤ ((445945 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_339.trans
      change ((28218042778011 / 281474976710656 : ℚ) : ℝ) ≤ ((28218042778011 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (340 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_340.trans
      change ((527239 / 281474976710656 : ℚ) : ℝ) ≤ ((527239 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_340.trans
      change ((27614044537947 / 281474976710656 : ℚ) : ℝ) ≤ ((27614044537947 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (341 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_341.trans
      change ((38945 / 17592186044416 : ℚ) : ℝ) ≤ ((623120 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_341.trans
      change ((27009035422167 / 281474976710656 : ℚ) : ℝ) ≤ ((27009035422167 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (342 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_342.trans
      change ((736161 / 281474976710656 : ℚ) : ℝ) ≤ ((736161 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_342.trans
      change ((13201506445391 / 140737488355328 : ℚ) : ℝ) ≤ ((26403012890782 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (343 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_343.trans
      change ((869383 / 281474976710656 : ℚ) : ℝ) ≤ ((869383 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_343.trans
      change ((25795974395389 / 281474976710656 : ℚ) : ℝ) ≤ ((25795974395389 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (344 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_344.trans
      change ((128291 / 35184372088832 : ℚ) : ℝ) ≤ ((1026328 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_344.trans
      change ((12593958689515 / 140737488355328 : ℚ) : ℝ) ≤ ((25187917379030 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (345 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_345.trans
      change ((302787 / 70368744177664 : ℚ) : ℝ) ≤ ((1211148 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_345.trans
      change ((12289419638081 / 140737488355328 : ℚ) : ℝ) ≤ ((24578839276162 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (346 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_346.trans
      change ((714355 / 140737488355328 : ℚ) : ℝ) ≤ ((1428710 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_346.trans
      change ((23968737512617 / 281474976710656 : ℚ) : ℝ) ≤ ((23968737512617 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (347 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_347.trans
      change ((842357 / 140737488355328 : ℚ) : ℝ) ≤ ((1684714 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_347.trans
      change ((23357609505567 / 281474976710656 : ℚ) : ℝ) ≤ ((23357609505567 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (348 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_348.trans
      change ((1985835 / 281474976710656 : ℚ) : ℝ) ≤ ((1985835 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_348.trans
      change ((355397697867 / 4398046511104 : ℚ) : ℝ) ≤ ((22745452663488 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (349 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_349.trans
      change ((1169943 / 140737488355328 : ℚ) : ℝ) ≤ ((2339886 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_349.trans
      change ((22132264386123 / 281474976710656 : ℚ) : ℝ) ≤ ((22132264386123 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (350 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_350.trans
      change ((2756007 / 281474976710656 : ℚ) : ℝ) ≤ ((2756007 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_350.trans
      change ((10759021032223 / 140737488355328 : ℚ) : ℝ) ≤ ((21518042064446 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (351 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_351.trans
      change ((405611 / 35184372088832 : ℚ) : ℝ) ≤ ((3244888 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_351.trans
      change ((20902783080623 / 281474976710656 : ℚ) : ℝ) ≤ ((20902783080623 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M3Far.FactorBounds.Sigma010
