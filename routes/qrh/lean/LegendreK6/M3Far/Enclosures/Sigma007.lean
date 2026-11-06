import LegendreK6.M3FarDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M3Far.Enclosures.Sigma007
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sigma_factor_upper_224 : sigmaFactor (224 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-114463 / 2624 : ℚ) : ℝ) - Real.exp ((-3609 / 82 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_224 : sigmaPower (224 : Fin 384) ≤ ((22884144448021 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_225 : sigmaFactor (225 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-607139 / 13984 : ℚ) : ℝ) - Real.exp ((-1225203 / 27968 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_225 : sigmaPower (225 : Fin 384) ≤ ((91033859744713 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_226 : sigmaFactor (226 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1811451 / 41920 : ℚ) : ℝ) - Real.exp ((-913913 / 20960 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_226 : sigmaPower (226 : Fin 384) ≤ ((90530374188873 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_227 : sigmaFactor (227 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-900755 / 20944 : ℚ) : ℝ) - Real.exp ((-3635745 / 83776 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_227 : sigmaPower (227 : Fin 384) ≤ ((1406658115087 / 4398046511104 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_228 : sigmaFactor (228 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-298599 / 6976 : ℚ) : ℝ) - Real.exp ((-75331 / 1744 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_228 : sigmaPower (228 : Fin 384) ≤ ((89521093510423 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_229 : sigmaFactor (229 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1781703 / 41824 : ℚ) : ℝ) - Real.exp ((-3596081 / 83648 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_229 : sigmaPower (229 : Fin 384) ≤ ((2781727964177 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_230 : sigmaFactor (230 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1771837 / 41792 : ℚ) : ℝ) - Real.exp ((-894081 / 20896 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_230 : sigmaPower (230 : Fin 384) ≤ ((44254360810047 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_231 : sigmaFactor (231 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-146833 / 3480 : ℚ) : ℝ) - Real.exp ((-1185539 / 27840 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_231 : sigmaPower (231 : Fin 384) ≤ ((88001372029079 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_232 : sigmaFactor (232 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-438045 / 10432 : ℚ) : ℝ) - Real.exp ((-55265 / 1304 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_232 : sigmaPower (232 : Fin 384) ≤ ((87493244294519 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_233 : sigmaFactor (233 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1742389 / 41696 : ℚ) : ℝ) - Real.exp ((-3517353 / 83392 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_233 : sigmaPower (233 : Fin 384) ≤ ((43492168312417 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_234 : sigmaFactor (234 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-577541 / 13888 : ℚ) : ℝ) - Real.exp ((-291483 / 6944 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_234 : sigmaPower (234 : Fin 384) ≤ ((10809330902867 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_235 : sigmaFactor (235 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-861441 / 20816 : ℚ) : ℝ) - Real.exp ((-3478289 / 83264 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_235 : sigmaPower (235 : Fin 384) ≤ ((85964174286217 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_236 : sigmaFactor (236 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-65891 / 1600 : ℚ) : ℝ) - Real.exp ((-16629 / 400 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_236 : sigmaPower (236 : Fin 384) ≤ ((42726458003259 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_237 : sigmaFactor (237 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-567825 / 13856 : ℚ) : ℝ) - Real.exp ((-1146475 / 27712 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_237 : sigmaPower (237 : Fin 384) ≤ ((42470435285057 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_238 : sigmaFactor (238 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1693809 / 41536 : ℚ) : ℝ) - Real.exp ((-855017 / 20768 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_238 : sigmaPower (238 : Fin 384) ≤ ((84428036157691 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_239 : sigmaFactor (239 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-210521 / 5188 : ℚ) : ℝ) - Real.exp ((-3400761 / 83008 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_239 : sigmaPower (239 : Fin 384) ≤ ((20978602736081 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_240 : sigmaFactor (240 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-69773 / 1728 : ℚ) : ℝ) - Real.exp ((-4403 / 108 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_240 : sigmaPower (240 : Fin 384) ≤ ((41699996549727 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_241 : sigmaFactor (241 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1664961 / 41440 : ℚ) : ℝ) - Real.exp ((-3362297 / 82880 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_241 : sigmaPower (241 : Fin 384) ≤ ((82884780786871 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_242 : sigmaFactor (242 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1655395 / 41408 : ℚ) : ℝ) - Real.exp ((-835785 / 20704 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_242 : sigmaPower (242 : Fin 384) ≤ ((82368772164685 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_243 : sigmaFactor (243 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-274309 / 6896 : ℚ) : ℝ) - Real.exp ((-1108011 / 27584 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_243 : sigmaPower (243 : Fin 384) ≤ ((81851965385311 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_244 : sigmaFactor (244 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-818169 / 20672 : ℚ) : ℝ) - Real.exp ((-206561 / 5168 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_244 : sigmaPower (244 : Fin 384) ≤ ((81334358595443 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_245 : sigmaFactor (245 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1626847 / 41312 : ℚ) : ℝ) - Real.exp ((-3285969 / 82624 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_245 : sigmaPower (245 : Fin 384) ≤ ((2525498435501 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_246 : sigmaFactor (246 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-539127 / 13760 : ℚ) : ℝ) - Real.exp ((-272251 / 6880 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_246 : sigmaPower (246 : Fin 384) ≤ ((80296737542265 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_247 : sigmaFactor (247 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-401985 / 10312 : ℚ) : ℝ) - Real.exp ((-3248105 / 82496 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_247 : sigmaPower (247 : Fin 384) ≤ ((79776719543543 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_248 : sigmaFactor (248 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-399631 / 10304 : ℚ) : ℝ) - Real.exp ((-50457 / 1288 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_248 : sigmaPower (248 : Fin 384) ≤ ((2476746689483 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_249 : sigmaFactor (249 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-40747 / 1056 : ℚ) : ℝ) - Real.exp ((-82319 / 2112 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_249 : sigmaPower (249 : Fin 384) ≤ ((19683564804941 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_250 : sigmaFactor (250 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1579767 / 41152 : ℚ) : ℝ) - Real.exp ((-797921 / 20576 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_250 : sigmaPower (250 : Fin 384) ≤ ((78211813124371 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_251 : sigmaFactor (251 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-785213 / 20560 : ℚ) : ℝ) - Real.exp ((-3172977 / 82240 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_251 : sigmaPower (251 : Fin 384) ≤ ((77688553883305 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_252 : sigmaFactor (252 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-260185 / 6848 : ℚ) : ℝ) - Real.exp ((-65715 / 1712 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_252 : sigmaPower (252 : Fin 384) ≤ ((77164479596691 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_253 : sigmaFactor (253 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1551819 / 41056 : ℚ) : ℝ) - Real.exp ((-3135713 / 82112 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_253 : sigmaPower (253 : Fin 384) ≤ ((76639588358735 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_254 : sigmaFactor (254 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1542553 / 41024 : ℚ) : ℝ) - Real.exp ((-779289 / 20512 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_254 : sigmaPower (254 : Fin 384) ≤ ((19028469564423 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_255 : sigmaFactor (255 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-15972 / 427 : ℚ) : ℝ) - Real.exp ((-1032883 / 27328 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_255 : sigmaPower (255 : Fin 384) ≤ ((18896836843963 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

end LegendreK6.M3Far.Enclosures.Sigma007
