import LegendreK6.M3FarDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M3Far.Enclosures.Sigma010
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sigma_factor_upper_320 : sigmaFactor (320 : Fin 384) ≤ ((17267 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-30821 / 1216 : ℚ) : ℝ) - Real.exp ((-489 / 19 : ℚ) : ℝ)) ≤ ((17267 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_320 : sigmaPower (320 : Fin 384) ≤ ((39505259889215 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_321 : sigmaFactor (321 : Fin 384) ≤ ((5139 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-326227 / 12960 : ℚ) : ℝ) - Real.exp ((-662579 / 25920 : ℚ) : ℝ)) ≤ ((5139 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_321 : sigmaPower (321 : Fin 384) ≤ ((19459998389873 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_322 : sigmaFactor (322 : Fin 384) ≤ ((24463 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-971115 / 38848 : ℚ) : ℝ) - Real.exp ((-493145 / 19424 : ℚ) : ℝ)) ≤ ((24463 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_322 : sigmaPower (322 : Fin 384) ≤ ((38333769480639 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_323 : sigmaFactor (323 : Fin 384) ≤ ((29103 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-481787 / 19408 : ℚ) : ℝ) - Real.exp ((-1957473 / 77632 : ℚ) : ℝ)) ≤ ((29103 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_323 : sigmaPower (323 : Fin 384) ≤ ((37746575607255 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_324 : sigmaFactor (324 : Fin 384) ≤ ((17305 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-159343 / 6464 : ℚ) : ℝ) - Real.exp ((-40467 / 1616 : ℚ) : ℝ)) ≤ ((17305 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_324 : sigmaPower (324 : Fin 384) ≤ ((9289603191771 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_325 : sigmaFactor (325 : Fin 384) ≤ ((5143 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-948567 / 38752 : ℚ) : ℝ) - Real.exp ((-1927409 / 77504 : ℚ) : ℝ)) ≤ ((5143 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_325 : sigmaPower (325 : Fin 384) ≤ ((36569278559711 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_326 : sigmaFactor (326 : Fin 384) ≤ ((48895 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-941101 / 38720 : ℚ) : ℝ) - Real.exp ((-478113 / 19360 : ℚ) : ℝ)) ≤ ((48895 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_326 : sigmaPower (326 : Fin 384) ≤ ((17989585288395 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_327 : sigmaFactor (327 : Fin 384) ≤ ((58085 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-5985 / 248 : ℚ) : ℝ) - Real.exp ((-48655 / 1984 : ℚ) : ℝ)) ≤ ((58085 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_327 : sigmaPower (327 : Fin 384) ≤ ((17694043201001 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_328 : sigmaFactor (328 : Fin 384) ≤ ((68977 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-231561 / 9664 : ℚ) : ℝ) - Real.exp ((-29417 / 1208 : ℚ) : ℝ)) ≤ ((68977 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_328 : sigmaPower (328 : Fin 384) ≤ ((34796023611031 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_329 : sigmaFactor (329 : Fin 384) ≤ ((40941 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-918853 / 38624 : ℚ) : ℝ) - Real.exp ((-1867881 / 77248 : ℚ) : ℝ)) ≤ ((40941 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_329 : sigmaPower (329 : Fin 384) ≤ ((34202979771525 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_330 : sigmaFactor (330 : Fin 384) ≤ ((48583 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-303829 / 12864 : ℚ) : ℝ) - Real.exp ((-154427 / 6432 : ℚ) : ℝ)) ≤ ((48583 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_330 : sigmaPower (330 : Fin 384) ≤ ((4201119055383 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_331 : sigmaFactor (331 : Fin 384) ≤ ((115261 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-452073 / 19280 : ℚ) : ℝ) - Real.exp ((-1838417 / 77120 : ℚ) : ℝ)) ≤ ((115261 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_331 : sigmaPower (331 : Fin 384) ≤ ((33013939177129 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_332 : sigmaFactor (332 : Fin 384) ≤ ((136675 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-448415 / 19264 : ℚ) : ℝ) - Real.exp ((-113985 / 4816 : ℚ) : ℝ)) ≤ ((136675 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_332 : sigmaPower (332 : Fin 384) ≤ ((4052242189633 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_333 : sigmaFactor (333 : Fin 384) ≤ ((81005 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-296513 / 12832 : ℚ) : ℝ) - Real.exp ((-603051 / 25664 : ℚ) : ℝ)) ≤ ((81005 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_333 : sigmaPower (333 : Fin 384) ≤ ((15910472499023 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_334 : sigmaFactor (334 : Fin 384) ≤ ((191969 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-882273 / 38464 : ℚ) : ℝ) - Real.exp ((-448649 / 19232 : ℚ) : ℝ)) ≤ ((191969 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_334 : sigmaPower (334 : Fin 384) ≤ ((31222959147051 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_335 : sigmaFactor (335 : Fin 384) ≤ ((227385 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-109379 / 4804 : ℚ) : ℝ) - Real.exp ((-1780089 / 76864 : ℚ) : ℝ)) ≤ ((227385 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_335 : sigmaPower (335 : Fin 384) ≤ ((15311988741407 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_336 : sigmaFactor (336 : Fin 384) ≤ ((67309 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-36159 / 1600 : ℚ) : ℝ) - Real.exp ((-2299 / 100 : ℚ) : ℝ)) ≤ ((67309 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_336 : sigmaPower (336 : Fin 384) ≤ ((7505999378951 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_337 : sigmaFactor (337 : Fin 384) ≤ ((19917 / 17592186044416 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-860625 / 38368 : ℚ) : ℝ) - Real.exp ((-1751225 / 76736 : ℚ) : ℝ)) ≤ ((19917 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_337 : sigmaPower (337 : Fin 384) ≤ ((29423016748181 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_338 : sigmaFactor (338 : Fin 384) ≤ ((377045 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-853459 / 38336 : ℚ) : ℝ) - Real.exp ((-434217 / 19168 : ℚ) : ℝ)) ≤ ((377045 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_338 : sigmaPower (338 : Fin 384) ≤ ((3602629084221 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_339 : sigmaFactor (339 : Fin 384) ≤ ((445945 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-141053 / 6384 : ℚ) : ℝ) - Real.exp ((-574187 / 25536 : ℚ) : ℝ)) ≤ ((445945 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_339 : sigmaPower (339 : Fin 384) ≤ ((28218042778011 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_340 : sigmaFactor (340 : Fin 384) ≤ ((527239 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-32277 / 1472 : ℚ) : ℝ) - Real.exp ((-8213 / 368 : ℚ) : ℝ)) ≤ ((527239 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_340 : sigmaPower (340 : Fin 384) ≤ ((27614044537947 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_341 : sigmaFactor (341 : Fin 384) ≤ ((38945 / 17592186044416 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-832111 / 38240 : ℚ) : ℝ) - Real.exp ((-1694097 / 76480 : ℚ) : ℝ)) ≤ ((38945 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_341 : sigmaPower (341 : Fin 384) ≤ ((27009035422167 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_342 : sigmaFactor (342 : Fin 384) ≤ ((736161 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-275015 / 12736 : ℚ) : ℝ) - Real.exp ((-139995 / 6368 : ℚ) : ℝ)) ≤ ((736161 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_342 : sigmaPower (342 : Fin 384) ≤ ((13201506445391 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_343 : sigmaFactor (343 : Fin 384) ≤ ((869383 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-204501 / 9544 : ℚ) : ℝ) - Real.exp ((-1665833 / 76352 : ℚ) : ℝ)) ≤ ((869383 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_343 : sigmaPower (343 : Fin 384) ≤ ((25795974395389 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_344 : sigmaFactor (344 : Fin 384) ≤ ((128291 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-202747 / 9536 : ℚ) : ℝ) - Real.exp ((-25809 / 1192 : ℚ) : ℝ)) ≤ ((128291 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_344 : sigmaPower (344 : Fin 384) ≤ ((12593958689515 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_345 : sigmaFactor (345 : Fin 384) ≤ ((302787 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-267999 / 12704 : ℚ) : ℝ) - Real.exp ((-545923 / 25408 : ℚ) : ℝ)) ≤ ((302787 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_345 : sigmaPower (345 : Fin 384) ≤ ((12289419638081 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_346 : sigmaFactor (346 : Fin 384) ≤ ((714355 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-797031 / 38080 : ℚ) : ℝ) - Real.exp ((-405953 / 19040 : ℚ) : ℝ)) ≤ ((714355 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_346 : sigmaPower (346 : Fin 384) ≤ ((23968737512617 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_347 : sigmaFactor (347 : Fin 384) ≤ ((842357 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-395045 / 19024 : ℚ) : ℝ) - Real.exp ((-1609905 / 76096 : ℚ) : ℝ)) ≤ ((842357 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_347 : sigmaPower (347 : Fin 384) ≤ ((23357609505567 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_348 : sigmaFactor (348 : Fin 384) ≤ ((1985835 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-130529 / 6336 : ℚ) : ℝ) - Real.exp ((-33251 / 1584 : ℚ) : ℝ)) ≤ ((1985835 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_348 : sigmaPower (348 : Fin 384) ≤ ((355397697867 / 4398046511104 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_349 : sigmaFactor (349 : Fin 384) ≤ ((1169943 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-776283 / 37984 : ℚ) : ℝ) - Real.exp ((-1582241 / 75968 : ℚ) : ℝ)) ≤ ((1169943 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_349 : sigmaPower (349 : Fin 384) ≤ ((22132264386123 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_350 : sigmaFactor (350 : Fin 384) ≤ ((2756007 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-769417 / 37952 : ℚ) : ℝ) - Real.exp ((-392121 / 18976 : ℚ) : ℝ)) ≤ ((2756007 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_350 : sigmaPower (350 : Fin 384) ≤ ((10759021032223 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_351 : sigmaFactor (351 : Fin 384) ≤ ((405611 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-15887 / 790 : ℚ) : ℝ) - Real.exp ((-518259 / 25280 : ℚ) : ℝ)) ≤ ((405611 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_351 : sigmaPower (351 : Fin 384) ≤ ((20902783080623 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

end LegendreK6.M3Far.Enclosures.Sigma010
