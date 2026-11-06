import LegendreK6.M3FarDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M3Far.Enclosures.Sigma008
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sigma_factor_upper_256 : sigmaFactor (256 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-11907 / 320 : ℚ) : ℝ) - Real.exp ((-188 / 5 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_256 : sigmaPower (256 : Fin 384) ≤ ((75059993789509 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_257 : sigmaFactor (257 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-1514905 / 40928 : ℚ) : ℝ) - Real.exp ((-3061785 / 81856 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_257 : sigmaPower (257 : Fin 384) ≤ ((74531815568941 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_258 : sigmaFactor (258 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-501913 / 13632 : ℚ) : ℝ) - Real.exp ((-253619 / 6816 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_258 : sigmaPower (258 : Fin 384) ≤ ((74002810778389 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_259 : sigmaFactor (259 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-748299 / 20432 : ℚ) : ℝ) - Real.exp ((-3025121 / 81728 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_259 : sigmaPower (259 : Fin 384) ≤ ((73472977476027 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_260 : sigmaFactor (260 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-743741 / 20416 : ℚ) : ℝ) - Real.exp ((-187929 / 5104 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_260 : sigmaPower (260 : Fin 384) ≤ ((72942313713943 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_261 : sigmaFactor (261 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-492797 / 13600 : ℚ) : ℝ) - Real.exp ((-996219 / 27200 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_261 : sigmaPower (261 : Fin 384) ≤ ((36205408769057 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_262 : sigmaFactor (262 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-113025 / 3136 : ℚ) : ℝ) - Real.exp ((-57125 / 1568 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_262 : sigmaPower (262 : Fin 384) ≤ ((2246202718387 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_263 : sigmaFactor (263 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-365071 / 10184 : ℚ) : ℝ) - Real.exp ((-2952393 / 81472 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_263 : sigmaPower (263 : Fin 384) ≤ ((71345320098433 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_264 : sigmaFactor (264 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-120939 / 3392 : ℚ) : ℝ) - Real.exp ((-15283 / 424 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_264 : sigmaPower (264 : Fin 384) ≤ ((70811314895763 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_265 : sigmaFactor (265 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-1442277 / 40672 : ℚ) : ℝ) - Real.exp ((-2916329 / 81344 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_265 : sigmaPower (265 : Fin 384) ≤ ((1098069834401 / 4398046511104 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_266 : sigmaFactor (266 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-1433311 / 40640 : ℚ) : ℝ) - Real.exp ((-724593 / 20320 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_266 : sigmaPower (266 : Fin 384) ≤ ((69740781631197 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_267 : sigmaFactor (267 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-237395 / 6768 : ℚ) : ℝ) - Real.exp ((-960155 / 27072 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_267 : sigmaPower (267 : Fin 384) ≤ ((17301062398291 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_268 : sigmaFactor (268 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-707727 / 20288 : ℚ) : ℝ) - Real.exp ((-178913 / 5072 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_268 : sigmaPower (268 : Fin 384) ≤ ((68666871290087 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_269 : sigmaFactor (269 : Fin 384) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-1406563 / 40544 : ℚ) : ℝ) - Real.exp ((-2844801 / 81088 : ℚ) : ℝ)) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_269 : sigmaPower (269 : Fin 384) ≤ ((68128644718181 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_270 : sigmaFactor (270 : Fin 384) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-465899 / 13504 : ℚ) : ℝ) - Real.exp ((-235587 / 6752 : ℚ) : ℝ)) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_270 : sigmaPower (270 : Fin 384) ≤ ((33794783933665 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_271 : sigmaFactor (271 : Fin 384) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-173607 / 5060 : ℚ) : ℝ) - Real.exp ((-2809337 / 80960 : ℚ) : ℝ)) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_271 : sigmaPower (271 : Fin 384) ≤ ((67049638721063 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_272 : sigmaFactor (272 : Fin 384) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-172505 / 5056 : ℚ) : ℝ) - Real.exp ((-10905 / 316 : ℚ) : ℝ)) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_272 : sigmaPower (272 : Fin 384) ≤ ((66508855256527 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_273 : sigmaFactor (273 : Fin 384) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-457083 / 13472 : ℚ) : ℝ) - Real.exp ((-924691 / 26944 : ℚ) : ℝ)) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_273 : sigmaPower (273 : Fin 384) ≤ ((65967215444461 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_274 : sigmaFactor (274 : Fin 384) ≤ ((1 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-1362483 / 40384 : ℚ) : ℝ) - Real.exp ((-689129 / 20192 : ℚ) : ℝ)) ≤ ((1 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_274 : sigmaPower (274 : Fin 384) ≤ ((8178089656147 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_275 : sigmaFactor (275 : Fin 384) ≤ ((1 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-52067 / 1552 : ℚ) : ℝ) - Real.exp ((-210693 / 6208 : ℚ) : ℝ)) ≤ ((1 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_275 : sigmaPower (275 : Fin 384) ≤ ((64881358628521 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_276 : sigmaFactor (276 : Fin 384) ≤ ((5 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-224171 / 6720 : ℚ) : ℝ) - Real.exp ((-56699 / 1680 : ℚ) : ℝ)) ≤ ((5 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_276 : sigmaPower (276 : Fin 384) ≤ ((64337137533865 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_277 : sigmaFactor (277 : Fin 384) ≤ ((3 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-1336335 / 40288 : ℚ) : ℝ) - Real.exp ((-2704145 / 80576 : ℚ) : ℝ)) ≤ ((3 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_277 : sigmaPower (277 : Fin 384) ≤ ((63792051910067 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_278 : sigmaFactor (278 : Fin 384) ≤ ((7 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-1327669 / 40256 : ℚ) : ℝ) - Real.exp ((-671697 / 20128 : ℚ) : ℝ)) ≤ ((7 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_278 : sigmaPower (278 : Fin 384) ≤ ((63246099695453 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_279 : sigmaFactor (279 : Fin 384) ≤ ((9 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-109919 / 3352 : ℚ) : ℝ) - Real.exp ((-889827 / 26816 : ℚ) : ℝ)) ≤ ((9 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_279 : sigmaPower (279 : Fin 384) ≤ ((62699278821785 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_280 : sigmaFactor (280 : Fin 384) ≤ ((5 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-327603 / 10048 : ℚ) : ℝ) - Real.exp ((-41441 / 1256 : ℚ) : ℝ)) ≤ ((5 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_280 : sigmaPower (280 : Fin 384) ≤ ((62151587214243 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_281 : sigmaFactor (281 : Fin 384) ≤ ((3 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-1301821 / 40160 : ℚ) : ℝ) - Real.exp ((-2635017 / 80320 : ℚ) : ℝ)) ≤ ((3 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_281 : sigmaPower (281 : Fin 384) ≤ ((30801511395695 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_282 : sigmaFactor (282 : Fin 384) ≤ ((15 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-431085 / 13376 : ℚ) : ℝ) - Real.exp ((-218155 / 6688 : ℚ) : ℝ)) ≤ ((15 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_282 : sigmaPower (282 : Fin 384) ≤ ((61053583465151 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_283 : sigmaFactor (283 : Fin 384) ≤ ((17 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-642357 / 20048 : ℚ) : ℝ) - Real.exp ((-2600753 / 80192 : ℚ) : ℝ)) ≤ ((17 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_283 : sigmaPower (283 : Fin 384) ≤ ((60503267140785 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_284 : sigmaFactor (284 : Fin 384) ≤ ((21 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-638099 / 20032 : ℚ) : ℝ) - Real.exp ((-161481 / 5008 : ℚ) : ℝ)) ≤ ((21 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_284 : sigmaPower (284 : Fin 384) ≤ ((14988017929215 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_285 : sigmaFactor (285 : Fin 384) ≤ ((25 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-422569 / 13344 : ℚ) : ℝ) - Real.exp ((-855563 / 26688 : ℚ) : ℝ)) ≤ ((25 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_285 : sigmaPower (285 : Fin 384) ≤ ((59399995085223 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_286 : sigmaFactor (286 : Fin 384) ≤ ((15 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-1259241 / 40000 : ℚ) : ℝ) - Real.exp ((-637433 / 20000 : ℚ) : ℝ)) ≤ ((15 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_286 : sigmaPower (286 : Fin 384) ≤ ((58847035130975 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_287 : sigmaFactor (287 : Fin 384) ≤ ((9 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-78175 / 2498 : ℚ) : ℝ) - Real.exp ((-2532825 / 79936 : ℚ) : ℝ)) ≤ ((9 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_287 : sigmaPower (287 : Fin 384) ≤ ((58293189732445 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

end LegendreK6.M3Far.Enclosures.Sigma008
