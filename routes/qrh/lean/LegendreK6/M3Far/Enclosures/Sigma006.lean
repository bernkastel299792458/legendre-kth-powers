import LegendreK6.M3FarDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M3Far.Enclosures.Sigma006
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sigma_factor_upper_192 : sigmaFactor (192 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-22545 / 448 : ℚ) : ℝ) - Real.exp ((-355 / 7 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_192 : sigmaPower (192 : Fin 384) ≤ ((107228562556441 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_193 : sigmaFactor (193 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-2153529 / 42976 : ℚ) : ℝ) - Real.exp ((-4340633 / 85952 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_193 : sigmaPower (193 : Fin 384) ≤ ((53374753588221 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_194 : sigmaFactor (194 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-2142763 / 42944 : ℚ) : ℝ) - Real.exp ((-1079769 / 21472 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_194 : sigmaPower (194 : Fin 384) ≤ ((106269737853999 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_195 : sigmaFactor (195 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-355337 / 7152 : ℚ) : ℝ) - Real.exp ((-1432523 / 28608 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_195 : sigmaPower (195 : Fin 384) ≤ ((105789252991925 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_196 : sigmaFactor (196 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1060653 / 21440 : ℚ) : ℝ) - Real.exp ((-267257 / 5360 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_196 : sigmaPower (196 : Fin 384) ≤ ((52654025494133 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_197 : sigmaFactor (197 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-162355 / 3296 : ℚ) : ℝ) - Real.exp ((-327285 / 6592 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_197 : sigmaPower (197 : Fin 384) ≤ ((52413065118141 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_198 : sigmaFactor (198 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-699983 / 14272 : ℚ) : ℝ) - Real.exp ((-352779 / 7136 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_198 : sigmaPower (198 : Fin 384) ≤ ((104343489124429 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_199 : sigmaFactor (199 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-522327 / 10696 : ℚ) : ℝ) - Real.exp ((-4212041 / 85568 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_199 : sigmaPower (199 : Fin 384) ≤ ((103860126036343 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_200 : sigmaFactor (200 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-519673 / 10688 : ℚ) : ℝ) - Real.exp ((-65481 / 1336 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_200 : sigmaPower (200 : Fin 384) ≤ ((25844009837705 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_201 : sigmaFactor (201 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-689367 / 14240 : ℚ) : ℝ) - Real.exp ((-1389859 / 28480 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_201 : sigmaPower (201 : Fin 384) ≤ ((51445613720899 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_202 : sigmaFactor (202 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-2057535 / 42688 : ℚ) : ℝ) - Real.exp ((-1037105 / 21344 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_202 : sigmaPower (202 : Fin 384) ≤ ((25601422169585 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_203 : sigmaFactor (203 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1023497 / 21328 : ℚ) : ℝ) - Real.exp ((-4127313 / 85312 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_203 : sigmaPower (203 : Fin 384) ≤ ((50959710712307 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_204 : sigmaFactor (204 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-339413 / 7104 : ℚ) : ℝ) - Real.exp ((-85547 / 1776 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_204 : sigmaPower (204 : Fin 384) ≤ ((101432424039877 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_205 : sigmaFactor (205 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-2025987 / 42592 : ℚ) : ℝ) - Real.exp ((-4085249 / 85184 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_205 : sigmaPower (205 : Fin 384) ≤ ((100944694878453 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_206 : sigmaFactor (206 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-2015521 / 42560 : ℚ) : ℝ) - Real.exp ((-1016073 / 21280 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_206 : sigmaPower (206 : Fin 384) ≤ ((50228116144859 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_207 : sigmaFactor (207 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-83545 / 1772 : ℚ) : ℝ) - Real.exp ((-1347795 / 28352 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_207 : sigmaPower (207 : Fin 384) ≤ ((99967034618081 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_208 : sigmaFactor (208 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-249333 / 5312 : ℚ) : ℝ) - Real.exp ((-15713 / 332 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_208 : sigmaPower (208 : Fin 384) ≤ ((99477100202963 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_209 : sigmaFactor (209 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1984273 / 42464 : ℚ) : ℝ) - Real.exp ((-4001721 / 84928 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_209 : sigmaPower (209 : Fin 384) ≤ ((98986427378779 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_210 : sigmaFactor (210 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-50613 / 1088 : ℚ) : ℝ) - Real.exp ((-25519 / 544 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_210 : sigmaPower (210 : Fin 384) ≤ ((98495014474921 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_211 : sigmaFactor (211 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-981783 / 21200 : ℚ) : ℝ) - Real.exp ((-3960257 / 84800 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_211 : sigmaPower (211 : Fin 384) ≤ ((12250357476967 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_212 : sigmaFactor (212 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-976625 / 21184 : ℚ) : ℝ) - Real.exp ((-246225 / 5296 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_212 : sigmaPower (212 : Fin 384) ≤ ((48754980860255 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_213 : sigmaFactor (213 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-647653 / 14112 : ℚ) : ℝ) - Real.exp ((-1306331 / 28224 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_213 : sigmaPower (213 : Fin 384) ≤ ((97016318503447 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_214 : sigmaFactor (214 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1932693 / 42304 : ℚ) : ℝ) - Real.exp ((-974609 / 21152 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_214 : sigmaPower (214 : Fin 384) ≤ ((48260964236825 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_215 : sigmaFactor (215 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-480613 / 10568 : ℚ) : ℝ) - Real.exp ((-3877929 / 84544 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_215 : sigmaPower (215 : Fin 384) ≤ ((48013394967551 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_216 : sigmaFactor (216 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-159353 / 3520 : ℚ) : ℝ) - Real.exp ((-20091 / 440 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_216 : sigmaPower (216 : Fin 384) ≤ ((95530901186647 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_217 : sigmaFactor (217 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1902045 / 42208 : ℚ) : ℝ) - Real.exp ((-3837065 / 84416 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_217 : sigmaPower (217 : Fin 384) ≤ ((95034260521971 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_218 : sigmaFactor (218 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1891879 / 42176 : ℚ) : ℝ) - Real.exp ((-954177 / 21088 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_218 : sigmaPower (218 : Fin 384) ≤ ((47268433114789 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_219 : sigmaFactor (219 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-313623 / 7024 : ℚ) : ℝ) - Real.exp ((-1265467 / 28096 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_219 : sigmaPower (219 : Fin 384) ≤ ((94038716592779 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_220 : sigmaFactor (220 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-935811 / 21056 : ℚ) : ℝ) - Real.exp ((-236009 / 5264 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_220 : sigmaPower (220 : Fin 384) ≤ ((93539809889661 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_221 : sigmaFactor (221 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1861531 / 42080 : ℚ) : ℝ) - Real.exp ((-3755937 / 84160 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_221 : sigmaPower (221 : Fin 384) ≤ ((93040144393079 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_222 : sigmaFactor (222 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-617155 / 14016 : ℚ) : ℝ) - Real.exp ((-311315 / 7008 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_222 : sigmaPower (222 : Fin 384) ≤ ((92539718370627 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_223 : sigmaFactor (223 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-8853 / 202 : ℚ) : ℝ) - Real.exp ((-285821 / 6464 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_223 : sigmaPower (223 : Fin 384) ≤ ((46019265042311 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

end LegendreK6.M3Far.Enclosures.Sigma006
