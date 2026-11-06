import LegendreK6.M3FarDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M3Far.Enclosures.Sigma005
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sigma_factor_upper_160 : sigmaFactor (160 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-157677 / 2752 : ℚ) : ℝ) - Real.exp ((-4961 / 86 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_160 : sigmaPower (160 : Fin 384) ≤ ((30547671891079 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_161 : sigmaFactor (161 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-2511241 / 44000 : ℚ) : ℝ) - Real.exp ((-5056857 / 88000 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_161 : sigmaPower (161 : Fin 384) ≤ ((121733662654985 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_162 : sigmaFactor (162 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-833225 / 14656 : ℚ) : ℝ) - Real.exp ((-419475 / 7328 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_162 : sigmaPower (162 : Fin 384) ≤ ((121275972498333 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_163 : sigmaFactor (163 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1244067 / 21968 : ℚ) : ℝ) - Real.exp ((-5010593 / 87872 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_163 : sigmaPower (163 : Fin 384) ≤ ((120817615640797 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_164 : sigmaFactor (164 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1238309 / 21952 : ℚ) : ℝ) - Real.exp ((-311721 / 5488 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_164 : sigmaPower (164 : Fin 384) ≤ ((1880602978509 / 4398046511104 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_165 : sigmaFactor (165 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-821709 / 14624 : ℚ) : ℝ) - Real.exp ((-1654843 / 29248 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_165 : sigmaPower (165 : Fin 384) ≤ ((59949447993809 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_166 : sigmaFactor (166 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-2453661 / 43840 : ℚ) : ℝ) - Real.exp ((-1235393 / 21920 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_166 : sigmaPower (166 : Fin 384) ≤ ((59719265131799 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_167 : sigmaFactor (167 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-610555 / 10952 : ℚ) : ℝ) - Real.exp ((-4918665 / 87616 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_167 : sigmaPower (167 : Fin 384) ≤ ((118977491981909 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_168 : sigmaFactor (168 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-202567 / 3648 : ℚ) : ℝ) - Real.exp ((-25499 / 456 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_168 : sigmaPower (168 : Fin 384) ≤ ((118515779667645 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_169 : sigmaFactor (169 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-2419413 / 43744 : ℚ) : ℝ) - Real.exp ((-4873001 / 87488 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_169 : sigmaPower (169 : Fin 384) ≤ ((118053391841583 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_170 : sigmaFactor (170 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-2408047 / 43712 : ℚ) : ℝ) - Real.exp ((-1212561 / 21856 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_170 : sigmaPower (170 : Fin 384) ≤ ((117590327020167 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_171 : sigmaFactor (171 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-30727 / 560 : ℚ) : ℝ) - Real.exp ((-123783 / 2240 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_171 : sigmaPower (171 : Fin 384) ≤ ((117126583715497 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_172 : sigmaFactor (172 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1192695 / 21824 : ℚ) : ℝ) - Real.exp ((-300305 / 5456 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_172 : sigmaPower (172 : Fin 384) ≤ ((116662160435307 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_173 : sigmaFactor (173 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-2374099 / 43616 : ℚ) : ℝ) - Real.exp ((-4782273 / 87232 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_173 : sigmaPower (173 : Fin 384) ≤ ((14524631960369 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_174 : sigmaFactor (174 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-787611 / 14528 : ℚ) : ℝ) - Real.exp ((-396643 / 7264 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_174 : sigmaPower (174 : Fin 384) ≤ ((7233204247337 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_175 : sigmaFactor (175 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-293949 / 5444 : ℚ) : ℝ) - Real.exp ((-4737209 / 87104 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_175 : sigmaPower (175 : Fin 384) ≤ ((14408099469147 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_176 : sigmaFactor (176 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-292547 / 5440 : ℚ) : ℝ) - Real.exp ((-18417 / 340 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_176 : sigmaPower (176 : Fin 384) ≤ ((114797637560425 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_177 : sigmaFactor (177 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-776395 / 14496 : ℚ) : ℝ) - Real.exp ((-1564115 / 28992 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_177 : sigmaPower (177 : Fin 384) ≤ ((57164895932407 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_178 : sigmaFactor (178 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-2318019 / 43456 : ℚ) : ℝ) - Real.exp ((-1167497 / 21728 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_178 : sigmaPower (178 : Fin 384) ≤ ((113861257147561 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_179 : sigmaFactor (179 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1153439 / 21712 : ℚ) : ℝ) - Real.exp ((-4647681 / 86848 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_179 : sigmaPower (179 : Fin 384) ≤ ((28348007971351 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_180 : sigmaFactor (180 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-382627 / 7232 : ℚ) : ℝ) - Real.exp ((-96363 / 1808 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_180 : sigmaPower (180 : Fin 384) ≤ ((28230528637647 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_181 : sigmaFactor (181 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-2284671 / 43360 : ℚ) : ℝ) - Real.exp ((-4603217 / 86720 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_181 : sigmaPower (181 : Fin 384) ≤ ((112451503610851 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_182 : sigmaFactor (182 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-2273605 / 43328 : ℚ) : ℝ) - Real.exp ((-1145265 / 21664 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_182 : sigmaPower (182 : Fin 384) ≤ ((13997524691175 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_183 : sigmaFactor (183 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-188547 / 3608 : ℚ) : ℝ) - Real.exp ((-1519651 / 28864 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_183 : sigmaPower (183 : Fin 384) ≤ ((55754097382451 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_184 : sigmaFactor (184 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-43299 / 832 : ℚ) : ℝ) - Real.exp ((-5453 / 104 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_184 : sigmaPower (184 : Fin 384) ≤ ((55517746885731 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_185 : sigmaFactor (185 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-2240557 / 43232 : ℚ) : ℝ) - Real.exp ((-4514889 / 86464 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_185 : sigmaPower (185 : Fin 384) ≤ ((55281046499305 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_186 : sigmaFactor (186 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-743197 / 14400 : ℚ) : ℝ) - Real.exp ((-374411 / 7200 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_186 : sigmaPower (186 : Fin 384) ≤ ((110087990891279 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_187 : sigmaFactor (187 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1109325 / 21584 : ℚ) : ℝ) - Real.exp ((-4471025 / 86336 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_187 : sigmaPower (187 : Fin 384) ≤ ((54806592944897 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_188 : sigmaFactor (188 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1103867 / 21568 : ℚ) : ℝ) - Real.exp ((-278073 / 5392 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_188 : sigmaPower (188 : Fin 384) ≤ ((109137676429849 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_189 : sigmaFactor (189 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-732281 / 14368 : ℚ) : ℝ) - Real.exp ((-1475787 / 28736 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_189 : sigmaPower (189 : Fin 384) ≤ ((3395670654453 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_190 : sigmaFactor (190 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-2185977 / 43072 : ℚ) : ℝ) - Real.exp ((-1101401 / 21536 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_190 : sigmaPower (190 : Fin 384) ≤ ((108184537854121 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_191 : sigmaFactor (191 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-67973 / 1345 : ℚ) : ℝ) - Real.exp ((-4383897 / 86080 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_191 : sigmaPower (191 : Fin 384) ≤ ((420730099947 / 1099511627776 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

end LegendreK6.M3Far.Enclosures.Sigma005
