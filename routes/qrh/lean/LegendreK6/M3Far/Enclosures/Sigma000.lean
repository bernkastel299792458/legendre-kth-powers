import LegendreK6.M3FarDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M3Far.Enclosures.Sigma000
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sigma_factor_upper_0 : sigmaFactor (0 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-6119 / 64 : ℚ) : ℝ) - Real.exp ((-96 / 1 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_0 : sigmaPower (0 : Fin 384) ≤ ((187649984473771 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1 : sigmaFactor (1 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-4683801 / 49120 : ℚ) : ℝ) - Real.exp ((-9405977 / 98240 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1 : sigmaPower (1 : Fin 384) ≤ ((93641620916553 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_2 : sigmaFactor (2 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-359095 / 3776 : ℚ) : ℝ) - Real.exp ((-180285 / 1888 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_2 : sigmaPower (2 : Fin 384) ≤ ((186916021040367 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_3 : sigmaFactor (3 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-775449 / 8176 : ℚ) : ℝ) - Real.exp ((-3114571 / 32704 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_3 : sigmaPower (3 : Fin 384) ≤ ((186548321159835 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_4 : sigmaFactor (4 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2318589 / 24512 : ℚ) : ℝ) - Real.exp ((-582041 / 6128 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_4 : sigmaPower (4 : Fin 384) ≤ ((93090070626675 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_5 : sigmaFactor (5 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-4621687 / 48992 : ℚ) : ℝ) - Real.exp ((-9281649 / 97984 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_5 : sigmaPower (5 : Fin 384) ≤ ((185811480380299 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_6 : sigmaFactor (6 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-1535407 / 16320 : ℚ) : ℝ) - Real.exp ((-770891 / 8160 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_6 : sigmaPower (6 : Fin 384) ≤ ((185442337597609 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_7 : sigmaFactor (7 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-1147695 / 12232 : ℚ) : ℝ) - Real.exp ((-9219785 / 97856 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_7 : sigmaPower (7 : Fin 384) ≤ ((185072711959743 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_8 : sigmaFactor (8 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-1143841 / 12224 : ℚ) : ℝ) - Real.exp ((-143577 / 1528 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_8 : sigmaPower (8 : Fin 384) ≤ ((92351301259343 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_9 : sigmaFactor (9 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-1519991 / 16288 : ℚ) : ℝ) - Real.exp ((-3052707 / 32576 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_9 : sigmaPower (9 : Fin 384) ≤ ((46083002080985 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_10 : sigmaFactor (10 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-4544607 / 48832 : ℚ) : ℝ) - Real.exp ((-2281841 / 24416 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_10 : sigmaPower (10 : Fin 384) ≤ ((183960928422517 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_11 : sigmaFactor (11 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2264633 / 24400 : ℚ) : ℝ) - Real.exp ((-9096657 / 97600 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_11 : sigmaPower (11 : Fin 384) ≤ ((183589361858929 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_12 : sigmaFactor (12 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-752325 / 8128 : ℚ) : ℝ) - Real.exp ((-188875 / 2032 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_12 : sigmaPower (12 : Fin 384) ≤ ((91608653837589 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_13 : sigmaFactor (13 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-4498659 / 48736 : ℚ) : ℝ) - Real.exp ((-9035393 / 97472 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_13 : sigmaPower (13 : Fin 384) ≤ ((182844764910753 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_14 : sigmaFactor (14 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-4483393 / 48704 : ℚ) : ℝ) - Real.exp ((-2251209 / 24352 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_14 : sigmaPower (14 : Fin 384) ≤ ((22808966575327 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_15 : sigmaFactor (15 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-14321 / 156 : ℚ) : ℝ) - Real.exp ((-230111 / 2496 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_15 : sigmaPower (15 : Fin 384) ≤ ((91049104892599 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_16 : sigmaFactor (16 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-556617 / 6080 : ℚ) : ℝ) - Real.exp ((-34937 / 380 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_16 : sigmaPower (16 : Fin 384) ≤ ((181724195490389 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_17 : sigmaFactor (17 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-4437745 / 48608 : ℚ) : ℝ) - Real.exp ((-8913465 / 97216 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_17 : sigmaPower (17 : Fin 384) ≤ ((181349688747529 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_18 : sigmaFactor (18 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-1474193 / 16192 : ℚ) : ℝ) - Real.exp ((-740259 / 8096 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_18 : sigmaPower (18 : Fin 384) ≤ ((22621836072925 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_19 : sigmaFactor (19 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2203719 / 24272 : ℚ) : ℝ) - Real.exp ((-8852801 / 97088 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_19 : sigmaPower (19 : Fin 384) ≤ ((180599194022219 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_20 : sigmaFactor (20 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2196161 / 24256 : ℚ) : ℝ) - Real.exp ((-551409 / 6064 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_20 : sigmaPower (20 : Fin 384) ≤ ((180223204085627 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_21 : sigmaFactor (21 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-1459077 / 16160 : ℚ) : ℝ) - Real.exp ((-2930779 / 32320 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_21 : sigmaPower (21 : Fin 384) ≤ ((44961679448171 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_22 : sigmaFactor (22 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-4362165 / 48448 : ℚ) : ℝ) - Real.exp ((-2190545 / 24224 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_22 : sigmaPower (22 : Fin 384) ≤ ((179469734159855 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_23 : sigmaFactor (23 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-1086781 / 12104 : ℚ) : ℝ) - Real.exp ((-8732073 / 96832 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_23 : sigmaPower (23 : Fin 384) ≤ ((11193265762563 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_24 : sigmaFactor (24 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-361009 / 4032 : ℚ) : ℝ) - Real.exp ((-45323 / 504 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_24 : sigmaPower (24 : Fin 384) ≤ ((178714270927401 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_25 : sigmaFactor (25 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-4317117 / 48352 : ℚ) : ℝ) - Real.exp ((-8672009 / 96704 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_25 : sigmaPower (25 : Fin 384) ≤ ((89167894673837 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_26 : sigmaFactor (26 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-4302151 / 48320 : ℚ) : ℝ) - Real.exp ((-2160513 / 24160 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_26 : sigmaPower (26 : Fin 384) ≤ ((177956806467841 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_27 : sigmaFactor (27 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-714535 / 8048 : ℚ) : ℝ) - Real.exp ((-2870715 / 32192 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_27 : sigmaPower (27 : Fin 384) ≤ ((88788660645641 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_28 : sigmaFactor (28 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-164319 / 1856 : ℚ) : ℝ) - Real.exp ((-41261 / 464 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_28 : sigmaPower (28 : Fin 384) ≤ ((88598666409367 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_29 : sigmaFactor (29 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-4257403 / 48224 : ℚ) : ℝ) - Real.exp ((-8552481 / 96448 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_29 : sigmaPower (29 : Fin 384) ≤ ((88408420024139 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_30 : sigmaFactor (30 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-1414179 / 16064 : ℚ) : ℝ) - Real.exp ((-710227 / 8032 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_30 : sigmaPower (30 : Fin 384) ≤ ((176435841975339 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_31 : sigmaFactor (31 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-264231 / 3010 : ℚ) : ℝ) - Real.exp ((-8493017 / 96320 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_31 : sigmaPower (31 : Fin 384) ≤ ((44013584398167 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

end LegendreK6.M3Far.Enclosures.Sigma000
