import LegendreK6.M3FarDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M3Far.Enclosures.Sigma009
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sigma_factor_upper_288 : sigmaFactor (288 : Fin 384) ≤ ((49 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-1991 / 64 : ℚ) : ℝ) - Real.exp ((-63 / 2 : ℚ) : ℝ)) ≤ ((49 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_288 : sigmaPower (288 : Fin 384) ≤ ((57738456761161 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_289 : sigmaFactor (289 : Fin 384) ≤ ((59 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-1233993 / 39904 : ℚ) : ℝ) - Real.exp ((-2499161 / 79808 : ℚ) : ℝ)) ≤ ((59 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_289 : sigmaPower (289 : Fin 384) ≤ ((57182834081823 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_290 : sigmaFactor (290 : Fin 384) ≤ ((71 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-1225627 / 39872 : ℚ) : ℝ) - Real.exp ((-620601 / 19936 : ℚ) : ℝ)) ≤ ((71 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_290 : sigmaPower (290 : Fin 384) ≤ ((28313159776139 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_291 : sigmaFactor (291 : Fin 384) ≤ ((85 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-202881 / 6640 : ℚ) : ℝ) - Real.exp ((-821899 / 26560 : ℚ) : ℝ)) ≤ ((85 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_291 : sigmaPower (291 : Fin 384) ≤ ((56068911023489 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_292 : sigmaFactor (292 : Fin 384) ≤ ((51 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-604485 / 19904 : ℚ) : ℝ) - Real.exp ((-153065 / 4976 : ℚ) : ℝ)) ≤ ((51 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_292 : sigmaPower (292 : Fin 384) ≤ ((13877651584877 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_293 : sigmaFactor (293 : Fin 384) ≤ ((61 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-1200679 / 39776 : ℚ) : ℝ) - Real.exp ((-2432433 / 79552 : ℚ) : ℝ)) ≤ ((61 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_293 : sigmaPower (293 : Fin 384) ≤ ((13737850834363 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_294 : sigmaFactor (294 : Fin 384) ≤ ((147 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-397471 / 13248 : ℚ) : ℝ) - Real.exp ((-201323 / 6624 : ℚ) : ℝ)) ≤ ((147 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_294 : sigmaPower (294 : Fin 384) ≤ ((27195649923735 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_295 : sigmaFactor (295 : Fin 384) ≤ ((11 / 17592186044416 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-296043 / 9928 : ℚ) : ℝ) - Real.exp ((-2399369 / 79424 : ℚ) : ℝ)) ≤ ((11 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_295 : sigmaPower (295 : Fin 384) ≤ ((26915146846359 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_296 : sigmaFactor (296 : Fin 384) ≤ ((211 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-293989 / 9920 : ℚ) : ℝ) - Real.exp ((-37233 / 1240 : ℚ) : ℝ)) ≤ ((211 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_296 : sigmaPower (296 : Fin 384) ≤ ((53268382689329 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_297 : sigmaFactor (297 : Fin 384) ≤ ((127 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-389255 / 13216 : ℚ) : ℝ) - Real.exp ((-788835 / 26432 : ℚ) : ℝ)) ≤ ((127 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_297 : sigmaPower (297 : Fin 384) ≤ ((26352782323193 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_298 : sigmaFactor (298 : Fin 384) ≤ ((19 / 17592186044416 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-1159599 / 39616 : ℚ) : ℝ) - Real.exp ((-587537 / 19808 : ℚ) : ℝ)) ≤ ((19 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_298 : sigmaPower (298 : Fin 384) ≤ ((52141837365895 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_299 : sigmaFactor (299 : Fin 384) ≤ ((365 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-575729 / 19792 : ℚ) : ℝ) - Real.exp ((-2333841 / 79168 : ℚ) : ℝ)) ≤ ((365 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_299 : sigmaPower (299 : Fin 384) ≤ ((51577198642751 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_300 : sigmaFactor (300 : Fin 384) ≤ ((219 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-190557 / 6592 : ℚ) : ℝ) - Real.exp ((-48283 / 1648 : ℚ) : ℝ)) ≤ ((219 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_300 : sigmaPower (300 : Fin 384) ≤ ((51011646264715 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_301 : sigmaFactor (301 : Fin 384) ≤ ((525 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-87327 / 3040 : ℚ) : ℝ) - Real.exp ((-177029 / 6080 : ℚ) : ℝ)) ≤ ((525 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_301 : sigmaPower (301 : Fin 384) ≤ ((50445178012383 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_302 : sigmaFactor (302 : Fin 384) ≤ ((629 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-1127185 / 39488 : ℚ) : ℝ) - Real.exp ((-571305 / 19744 : ℚ) : ℝ)) ≤ ((629 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_302 : sigmaPower (302 : Fin 384) ≤ ((49877791659155 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_303 : sigmaFactor (303 : Fin 384) ≤ ((753 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-46631 / 1644 : ℚ) : ℝ) - Real.exp ((-756371 / 26304 : ℚ) : ℝ)) ≤ ((753 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_303 : sigmaPower (303 : Fin 384) ≤ ((24654742485605 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_304 : sigmaFactor (304 : Fin 384) ≤ ((451 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-138891 / 4928 : ℚ) : ℝ) - Real.exp ((-8801 / 308 : ℚ) : ℝ)) ≤ ((451 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_304 : sigmaPower (304 : Fin 384) ≤ ((48740255707473 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_305 : sigmaFactor (305 : Fin 384) ≤ ((1079 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-1103137 / 39392 : ℚ) : ℝ) - Real.exp ((-2237049 / 78784 : ℚ) : ℝ)) ≤ ((1079 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_305 : sigmaPower (305 : Fin 384) ≤ ((48170101619587 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_306 : sigmaFactor (306 : Fin 384) ≤ ((1291 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-365057 / 13120 : ℚ) : ℝ) - Real.exp ((-185091 / 6560 : ℚ) : ℝ)) ≤ ((1291 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_306 : sigmaPower (306 : Fin 384) ≤ ((11899755112971 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_307 : sigmaFactor (307 : Fin 384) ≤ ((1545 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-543615 / 19664 : ℚ) : ℝ) - Real.exp ((-2205185 / 78656 : ℚ) : ℝ)) ≤ ((1545 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_307 : sigmaPower (307 : Fin 384) ≤ ((5878376242669 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_308 : sigmaFactor (308 : Fin 384) ≤ ((231 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-539657 / 19648 : ℚ) : ℝ) - Real.exp ((-136833 / 4912 : ℚ) : ℝ)) ≤ ((231 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_308 : sigmaPower (308 : Fin 384) ≤ ((46454067817611 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_309 : sigmaFactor (309 : Fin 384) ≤ ((2209 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-357141 / 13088 : ℚ) : ℝ) - Real.exp ((-724507 / 26176 : ℚ) : ℝ)) ≤ ((2209 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_309 : sigmaPower (309 : Fin 384) ≤ ((22940095901439 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_310 : sigmaFactor (310 : Fin 384) ≤ ((165 / 17592186044416 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-1063557 / 39232 : ℚ) : ℝ) - Real.exp ((-539441 / 19616 : ℚ) : ℝ)) ≤ ((165 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_310 : sigmaPower (310 : Fin 384) ≤ ((45305379611939 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_311 : sigmaFactor (311 : Fin 384) ≤ ((3153 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-263929 / 9800 : ℚ) : ℝ) - Real.exp ((-2142057 / 78400 : ℚ) : ℝ)) ≤ ((3153 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_311 : sigmaPower (311 : Fin 384) ≤ ((11182407238029 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_312 : sigmaFactor (312 : Fin 384) ≤ ((1883 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-87325 / 3264 : ℚ) : ℝ) - Real.exp ((-11075 / 408 : ℚ) : ℝ)) ≤ ((1883 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_312 : sigmaPower (312 : Fin 384) ≤ ((44152937523241 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_313 : sigmaFactor (313 : Fin 384) ≤ ((281 / 17592186044416 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-1040109 / 39136 : ℚ) : ℝ) - Real.exp ((-2110793 / 78272 : ℚ) : ℝ)) ≤ ((281 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_313 : sigmaPower (313 : Fin 384) ≤ ((21787651508811 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_314 : sigmaFactor (314 : Fin 384) ≤ ((2683 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-79411 / 3008 : ℚ) : ℝ) - Real.exp ((-40293 / 1504 : ℚ) : ℝ)) ≤ ((2683 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_314 : sigmaPower (314 : Fin 384) ≤ ((42996723120013 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_315 : sigmaFactor (315 : Fin 384) ≤ ((6401 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-170767 / 6512 : ℚ) : ℝ) - Real.exp ((-693243 / 26048 : ℚ) : ℝ)) ≤ ((6401 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_315 : sigmaPower (315 : Fin 384) ≤ ((42417195507585 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_316 : sigmaFactor (316 : Fin 384) ≤ ((3817 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-508443 / 19520 : ℚ) : ℝ) - Real.exp ((-129017 / 4880 : ℚ) : ℝ)) ≤ ((3817 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_316 : sigmaPower (316 : Fin 384) ≤ ((20918358924945 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_317 : sigmaFactor (317 : Fin 384) ≤ ((9101 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-1009195 / 39008 : ℚ) : ℝ) - Real.exp ((-2048865 / 78016 : ℚ) : ℝ)) ≤ ((9101 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_317 : sigmaPower (317 : Fin 384) ≤ ((10313821952209 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_318 : sigmaFactor (318 : Fin 384) ≤ ((5423 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-333843 / 12992 : ℚ) : ℝ) - Real.exp ((-169459 / 6496 : ℚ) : ℝ)) ≤ ((5423 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_318 : sigmaPower (318 : Fin 384) ≤ ((20336451519325 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_319 : sigmaFactor (319 : Fin 384) ≤ ((6461 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-31059 / 1217 : ℚ) : ℝ) - Real.exp ((-2018201 / 77888 : ℚ) : ℝ)) ≤ ((6461 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_319 : sigmaPower (319 : Fin 384) ≤ ((40089561185851 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

end LegendreK6.M3Far.Enclosures.Sigma009
