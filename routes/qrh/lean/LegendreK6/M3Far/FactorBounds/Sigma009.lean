import LegendreK6.M3Far.Enclosures.Sigma009
import LegendreK6.M3FarIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M3Far.FactorBounds.Sigma009
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 384) (hlo : 288 ≤ i.val) (hhi : i.val < 320) :
    sigmaFactor i ≤ sigmaDyadicFactor i ∧ sigmaPower i ≤ sigmaDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (288 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_288.trans
      change ((49 / 281474976710656 : ℚ) : ℝ) ≤ ((49 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_288.trans
      change ((57738456761161 / 281474976710656 : ℚ) : ℝ) ≤ ((57738456761161 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (289 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_289.trans
      change ((59 / 281474976710656 : ℚ) : ℝ) ≤ ((59 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_289.trans
      change ((57182834081823 / 281474976710656 : ℚ) : ℝ) ≤ ((57182834081823 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (290 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_290.trans
      change ((71 / 281474976710656 : ℚ) : ℝ) ≤ ((71 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_290.trans
      change ((28313159776139 / 140737488355328 : ℚ) : ℝ) ≤ ((56626319552278 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (291 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_291.trans
      change ((85 / 281474976710656 : ℚ) : ℝ) ≤ ((85 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_291.trans
      change ((56068911023489 / 281474976710656 : ℚ) : ℝ) ≤ ((56068911023489 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (292 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_292.trans
      change ((51 / 140737488355328 : ℚ) : ℝ) ≤ ((102 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_292.trans
      change ((13877651584877 / 70368744177664 : ℚ) : ℝ) ≤ ((55510606339508 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (293 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_293.trans
      change ((61 / 140737488355328 : ℚ) : ℝ) ≤ ((122 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_293.trans
      change ((13737850834363 / 70368744177664 : ℚ) : ℝ) ≤ ((54951403337452 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (294 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_294.trans
      change ((147 / 281474976710656 : ℚ) : ℝ) ≤ ((147 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_294.trans
      change ((27195649923735 / 140737488355328 : ℚ) : ℝ) ≤ ((54391299847470 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (295 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_295.trans
      change ((11 / 17592186044416 : ℚ) : ℝ) ≤ ((176 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_295.trans
      change ((26915146846359 / 140737488355328 : ℚ) : ℝ) ≤ ((53830293692718 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (296 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_296.trans
      change ((211 / 281474976710656 : ℚ) : ℝ) ≤ ((211 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_296.trans
      change ((53268382689329 / 281474976710656 : ℚ) : ℝ) ≤ ((53268382689329 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (297 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_297.trans
      change ((127 / 140737488355328 : ℚ) : ℝ) ≤ ((254 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_297.trans
      change ((26352782323193 / 140737488355328 : ℚ) : ℝ) ≤ ((52705564646386 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (298 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_298.trans
      change ((19 / 17592186044416 : ℚ) : ℝ) ≤ ((304 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_298.trans
      change ((52141837365895 / 281474976710656 : ℚ) : ℝ) ≤ ((52141837365895 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (299 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_299.trans
      change ((365 / 281474976710656 : ℚ) : ℝ) ≤ ((365 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_299.trans
      change ((51577198642751 / 281474976710656 : ℚ) : ℝ) ≤ ((51577198642751 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (300 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_300.trans
      change ((219 / 140737488355328 : ℚ) : ℝ) ≤ ((438 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_300.trans
      change ((51011646264715 / 281474976710656 : ℚ) : ℝ) ≤ ((51011646264715 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (301 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_301.trans
      change ((525 / 281474976710656 : ℚ) : ℝ) ≤ ((525 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_301.trans
      change ((50445178012383 / 281474976710656 : ℚ) : ℝ) ≤ ((50445178012383 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (302 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_302.trans
      change ((629 / 281474976710656 : ℚ) : ℝ) ≤ ((629 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_302.trans
      change ((49877791659155 / 281474976710656 : ℚ) : ℝ) ≤ ((49877791659155 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (303 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_303.trans
      change ((753 / 281474976710656 : ℚ) : ℝ) ≤ ((753 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_303.trans
      change ((24654742485605 / 140737488355328 : ℚ) : ℝ) ≤ ((49309484971210 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (304 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_304.trans
      change ((451 / 140737488355328 : ℚ) : ℝ) ≤ ((902 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_304.trans
      change ((48740255707473 / 281474976710656 : ℚ) : ℝ) ≤ ((48740255707473 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (305 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_305.trans
      change ((1079 / 281474976710656 : ℚ) : ℝ) ≤ ((1079 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_305.trans
      change ((48170101619587 / 281474976710656 : ℚ) : ℝ) ≤ ((48170101619587 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (306 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_306.trans
      change ((1291 / 281474976710656 : ℚ) : ℝ) ≤ ((1291 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_306.trans
      change ((11899755112971 / 70368744177664 : ℚ) : ℝ) ≤ ((47599020451884 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (307 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_307.trans
      change ((1545 / 281474976710656 : ℚ) : ℝ) ≤ ((1545 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_307.trans
      change ((5878376242669 / 35184372088832 : ℚ) : ℝ) ≤ ((47027009941352 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (308 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_308.trans
      change ((231 / 35184372088832 : ℚ) : ℝ) ≤ ((1848 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_308.trans
      change ((46454067817611 / 281474976710656 : ℚ) : ℝ) ≤ ((46454067817611 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (309 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_309.trans
      change ((2209 / 281474976710656 : ℚ) : ℝ) ≤ ((2209 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_309.trans
      change ((22940095901439 / 140737488355328 : ℚ) : ℝ) ≤ ((45880191802878 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (310 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_310.trans
      change ((165 / 17592186044416 : ℚ) : ℝ) ≤ ((2640 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_310.trans
      change ((45305379611939 / 281474976710656 : ℚ) : ℝ) ≤ ((45305379611939 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (311 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_311.trans
      change ((3153 / 281474976710656 : ℚ) : ℝ) ≤ ((3153 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_311.trans
      change ((11182407238029 / 70368744177664 : ℚ) : ℝ) ≤ ((44729628952116 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (312 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_312.trans
      change ((1883 / 140737488355328 : ℚ) : ℝ) ≤ ((3766 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_312.trans
      change ((44152937523241 / 281474976710656 : ℚ) : ℝ) ≤ ((44152937523241 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (313 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_313.trans
      change ((281 / 17592186044416 : ℚ) : ℝ) ≤ ((4496 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_313.trans
      change ((21787651508811 / 140737488355328 : ℚ) : ℝ) ≤ ((43575303017622 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (314 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_314.trans
      change ((2683 / 140737488355328 : ℚ) : ℝ) ≤ ((5366 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_314.trans
      change ((42996723120013 / 281474976710656 : ℚ) : ℝ) ≤ ((42996723120013 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (315 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_315.trans
      change ((6401 / 281474976710656 : ℚ) : ℝ) ≤ ((6401 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_315.trans
      change ((42417195507585 / 281474976710656 : ℚ) : ℝ) ≤ ((42417195507585 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (316 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_316.trans
      change ((3817 / 140737488355328 : ℚ) : ℝ) ≤ ((7634 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_316.trans
      change ((20918358924945 / 140737488355328 : ℚ) : ℝ) ≤ ((41836717849890 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (317 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_317.trans
      change ((9101 / 281474976710656 : ℚ) : ℝ) ≤ ((9101 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_317.trans
      change ((10313821952209 / 70368744177664 : ℚ) : ℝ) ≤ ((41255287808836 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (318 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_318.trans
      change ((5423 / 140737488355328 : ℚ) : ℝ) ≤ ((10846 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_318.trans
      change ((20336451519325 / 140737488355328 : ℚ) : ℝ) ≤ ((40672903038650 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (319 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_319.trans
      change ((6461 / 140737488355328 : ℚ) : ℝ) ≤ ((12922 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_319.trans
      change ((40089561185851 / 281474976710656 : ℚ) : ℝ) ≤ ((40089561185851 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M3Far.FactorBounds.Sigma009
