import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Sigma000
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sigma_factor_upper_0 : sigmaFactor (0 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-937013 / 16384 : ℚ) : ℝ) - Real.exp ((-3663 / 64 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_0 : sigmaPower (0 : Fin 1536) ≤ ((187649984473771 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1 : sigmaFactor (1 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2876365899 / 50323456 : ℚ) : ℝ) - Real.exp ((-5757124043 / 100646912 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1 : sigmaPower (1 : Fin 1536) ≤ ((187558343589281 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_2 : sigmaFactor (2 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2874228577 / 50315264 : ℚ) : ℝ) - Real.exp ((-1438212171 / 25157632 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_2 : sigmaPower (2 : Fin 1536) ≤ ((187466672864061 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_3 : sigmaFactor (3 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-478681995 / 8384512 : ℚ) : ℝ) - Real.exp ((-1916191585 / 33538048 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_3 : sigmaPower (3 : Fin 1536) ≤ ((187374972283531 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_4 : sigmaFactor (4 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-1434978039 / 25149440 : ℚ) : ℝ) - Real.exp ((-359018891 / 6287360 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_4 : sigmaPower (4 : Fin 1536) ≤ ((93641620916553 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_5 : sigmaFactor (5 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2867820901 / 50290688 : ℚ) : ℝ) - Real.exp ((-5740031187 / 100581376 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_5 : sigmaPower (5 : Fin 1536) ≤ ((46797870374547 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_6 : sigmaFactor (6 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-86838983 / 1523712 : ℚ) : ℝ) - Real.exp ((-43452739 / 761856 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_6 : sigmaPower (6 : Fin 1536) ≤ ((187099691264171 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_7 : sigmaFactor (7 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-42111069 / 739328 : ℚ) : ℝ) - Real.exp ((-337146667 / 5914624 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_7 : sigmaPower (7 : Fin 1536) ≤ ((187007871116439 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_8 : sigmaFactor (8 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-715354915 / 12566528 : ℚ) : ℝ) - Real.exp ((-89487915 / 1570816 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_8 : sigmaPower (8 : Fin 1536) ≤ ((186916021040367 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_9 : sigmaFactor (9 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-953095781 / 16752640 : ℚ) : ℝ) - Real.exp ((-1907653737 / 33505280 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_9 : sigmaPower (9 : Fin 1536) ≤ ((186824141021319 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_10 : sigmaFactor (10 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2857155741 / 50249728 : ℚ) : ℝ) - Real.exp ((-1429674323 / 25124864 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_10 : sigmaPower (10 : Fin 1536) ≤ ((186732231044653 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_11 : sigmaFactor (11 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-1427512427 / 25120768 : ℚ) : ℝ) - Real.exp ((-5714434803 / 100483072 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_11 : sigmaPower (11 : Fin 1536) ≤ ((5832509096741 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_12 : sigmaFactor (12 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-475482447 / 8372224 : ℚ) : ℝ) - Real.exp ((-118961953 / 2093056 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_12 : sigmaPower (12 : Fin 1536) ≤ ((186548321159835 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_13 : sigmaFactor (13 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2850765225 / 50225152 : ℚ) : ℝ) - Real.exp ((-5705914115 / 100450304 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_13 : sigmaPower (13 : Fin 1536) ≤ ((46614080305587 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_14 : sigmaFactor (14 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2848636483 / 50216960 : ℚ) : ℝ) - Real.exp ((-1425413979 / 25108480 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_14 : sigmaPower (14 : Fin 1536) ≤ ((23295536408571 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_15 : sigmaFactor (15 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-118604519 / 2092032 : ℚ) : ℝ) - Real.exp ((-1899133049 / 33472512 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_15 : sigmaPower (15 : Fin 1536) ≤ ((93136115641901 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_16 : sigmaFactor (16 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-355547643 / 6275072 : ℚ) : ℝ) - Real.exp ((-22238843 / 392192 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_16 : sigmaPower (16 : Fin 1536) ≤ ((93090070626675 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_17 : sigmaFactor (17 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-258386777 / 4562944 : ℚ) : ℝ) - Real.exp ((-517171809 / 9125888 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_17 : sigmaPower (17 : Fin 1536) ≤ ((186088021162499 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_18 : sigmaFactor (18 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-946709555 / 16728064 : ℚ) : ℝ) - Real.exp ((-473719785 / 8364032 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_18 : sigmaPower (18 : Fin 1536) ≤ ((185995870996529 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_19 : sigmaFactor (19 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-1419001749 / 25088000 : ℚ) : ℝ) - Real.exp ((-5680386371 / 100352000 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_19 : sigmaPower (19 : Fin 1536) ≤ ((185903690740709 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_20 : sigmaFactor (20 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-1417939523 / 25083904 : ℚ) : ℝ) - Real.exp ((-354758547 / 6270976 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_20 : sigmaPower (20 : Fin 1536) ≤ ((185811480380299 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_21 : sigmaFactor (21 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-944585103 / 16719872 : ℚ) : ℝ) - Real.exp ((-1890629521 / 33439744 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_21 : sigmaPower (21 : Fin 1536) ≤ ((46429809975137 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_22 : sigmaFactor (22 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2831632287 / 50151424 : ℚ) : ℝ) - Real.exp ((-1416910451 / 25075712 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_22 : sigmaPower (22 : Fin 1536) ≤ ((185626969286697 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_23 : sigmaFactor (23 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-707377495 / 12535808 : ℚ) : ℝ) - Real.exp ((-5663396475 / 100286464 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_23 : sigmaPower (23 : Fin 1536) ≤ ((185534668523977 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_24 : sigmaFactor (24 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-13859747 / 245760 : ℚ) : ℝ) - Real.exp ((-1733809 / 30720 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_24 : sigmaPower (24 : Fin 1536) ≤ ((185442337597609 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_25 : sigmaFactor (25 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2825267511 / 50126848 : ℚ) : ℝ) - Real.exp ((-5654910107 / 100253696 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_25 : sigmaPower (25 : Fin 1536) ≤ ((185349976492805 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_26 : sigmaFactor (26 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2823147349 / 50118656 : ℚ) : ℝ) - Real.exp ((-1412667267 / 25059328 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_26 : sigmaPower (26 : Fin 1536) ≤ ((92628792597383 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_27 : sigmaFactor (27 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-470171317 / 8351744 : ℚ) : ℝ) - Real.exp ((-1882143153 / 33406976 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_27 : sigmaPower (27 : Fin 1536) ≤ ((46291290922171 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_28 : sigmaFactor (28 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-128132235 / 2277376 : ℚ) : ℝ) - Real.exp ((-32057905 / 569344 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_28 : sigmaPower (28 : Fin 1536) ≤ ((185072711959743 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_29 : sigmaFactor (29 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2816791153 / 50094080 : ℚ) : ℝ) - Real.exp ((-5637954531 / 100188160 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_29 : sigmaPower (29 : Fin 1536) ≤ ((92490114996557 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_30 : sigmaFactor (30 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-938224617 / 16695296 : ℚ) : ℝ) - Real.exp ((-469476601 / 8347648 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_30 : sigmaPower (30 : Fin 1536) ≤ ((184887717773961 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_31 : sigmaFactor (31 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-175784829 / 3129856 : ℚ) : ℝ) - Real.exp ((-5629485323 / 100155392 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_31 : sigmaPower (31 : Fin 1536) ≤ ((184795175287437 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_32 : sigmaFactor (32 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-175652587 / 3129344 : ℚ) : ℝ) - Real.exp ((-5493411 / 97792 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_32 : sigmaPower (32 : Fin 1536) ≤ ((92351301259343 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_33 : sigmaFactor (33 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-936108745 / 16687104 : ℚ) : ℝ) - Real.exp ((-1873673945 / 33374208 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_33 : sigmaPower (33 : Fin 1536) ≤ ((184609999452841 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_34 : sigmaFactor (34 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2806211793 / 50053120 : ℚ) : ℝ) - Real.exp ((-1404198059 / 25026560 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_34 : sigmaPower (34 : Fin 1536) ≤ ((184517366075027 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_35 : sigmaFactor (35 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-1402049033 / 25022464 : ℚ) : ℝ) - Real.exp ((-5612564067 / 100089856 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_35 : sigmaPower (35 : Fin 1536) ≤ ((184424702370359 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_36 : sigmaFactor (36 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-466997509 / 8339456 : ℚ) : ℝ) - Real.exp ((-116840361 / 2084864 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_36 : sigmaPower (36 : Fin 1536) ≤ ((46083002080985 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_37 : sigmaFactor (37 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2799872757 / 50028544 : ℚ) : ℝ) - Real.exp ((-5604112019 / 100057088 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_37 : sigmaPower (37 : Fin 1536) ≤ ((184239283920867 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_38 : sigmaFactor (38 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2797761175 / 50020352 : ℚ) : ℝ) - Real.exp ((-1399972035 / 25010176 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_38 : sigmaPower (38 : Fin 1536) ≤ ((184146529146223 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_39 : sigmaFactor (39 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-21179169 / 378880 : ℚ) : ℝ) - Real.exp ((-169565627 / 3031040 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_39 : sigmaPower (39 : Fin 1536) ≤ ((184053743985085 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_40 : sigmaFactor (40 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-698385039 / 12500992 : ℚ) : ℝ) - Real.exp ((-87366323 / 1562624 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_40 : sigmaPower (40 : Fin 1536) ≤ ((183960928422517 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_41 : sigmaFactor (41 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-164201807 / 2940928 : ℚ) : ℝ) - Real.exp ((-328660299 / 5881856 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_41 : sigmaPower (41 : Fin 1536) ≤ ((183868082443577 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_42 : sigmaFactor (42 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-929773999 / 16662528 : ℚ) : ℝ) - Real.exp ((-465250577 / 8331264 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_42 : sigmaPower (42 : Fin 1536) ≤ ((91887603016655 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_43 : sigmaFactor (43 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-1393606995 / 24989696 : ℚ) : ℝ) - Real.exp ((-5578790195 / 99958784 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_43 : sigmaPower (43 : Fin 1536) ≤ ((11480143698547 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_44 : sigmaFactor (44 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-1392553349 / 24985600 : ℚ) : ℝ) - Real.exp ((-348410931 / 6246400 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_44 : sigmaPower (44 : Fin 1536) ≤ ((183589361858929 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_45 : sigmaFactor (45 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-927666707 / 16654336 : ℚ) : ℝ) - Real.exp ((-1856787009 / 33308672 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_45 : sigmaPower (45 : Fin 1536) ≤ ((91748197032429 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_46 : sigmaFactor (46 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2780894259 / 49954816 : ℚ) : ℝ) - Real.exp ((-1391537147 / 24977408 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_46 : sigmaPower (46 : Fin 1536) ≤ ((183403395779547 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_47 : sigmaFactor (47 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-347348639 / 6243328 : ℚ) : ℝ) - Real.exp ((-5561937579 / 99893248 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_47 : sigmaPower (47 : Fin 1536) ≤ ((183310366987991 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_48 : sigmaFactor (48 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-115695195 / 2080768 : ℚ) : ℝ) - Real.exp ((-7236625 / 130048 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_48 : sigmaPower (48 : Fin 1536) ≤ ((91608653837589 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_49 : sigmaFactor (49 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2774580963 / 49930240 : ℚ) : ℝ) - Real.exp ((-5553519851 / 99860480 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_49 : sigmaPower (49 : Fin 1536) ≤ ((183124217826085 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_50 : sigmaFactor (50 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-252043451 / 4538368 : ℚ) : ℝ) - Real.exp ((-126120753 / 2269184 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_50 : sigmaPower (50 : Fin 1536) ≤ ((11439443589105 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_51 : sigmaFactor (51 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-461729279 / 8318976 : ℚ) : ℝ) - Real.exp ((-1848369281 / 33275904 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_51 : sigmaPower (51 : Fin 1536) ≤ ((22867243307365 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_52 : sigmaFactor (52 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-1384137051 / 24952832 : ℚ) : ℝ) - Real.exp ((-346306499 / 6238208 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_52 : sigmaPower (52 : Fin 1536) ≤ ((182844764910753 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_53 : sigmaFactor (53 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2766173245 / 49897472 : ℚ) : ℝ) - Real.exp ((-5536701555 / 99794944 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_53 : sigmaPower (53 : Fin 1536) ≤ ((45687888191529 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_54 : sigmaFactor (54 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-921357701 / 16629760 : ℚ) : ℝ) - Real.exp ((-461041713 / 8314880 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_54 : sigmaPower (54 : Fin 1536) ≤ ((182658310009937 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_55 : sigmaFactor (55 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-690493419 / 12470272 : ℚ) : ℝ) - Real.exp ((-5528300987 / 99762176 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_55 : sigmaPower (55 : Fin 1536) ≤ ((91282518313567 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_56 : sigmaFactor (56 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-689968741 / 12468224 : ℚ) : ℝ) - Real.exp ((-86314107 / 1558528 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_56 : sigmaPower (56 : Fin 1536) ≤ ((22808966575327 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_57 : sigmaFactor (57 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-919258989 / 16621568 : ℚ) : ℝ) - Real.exp ((-1839968713 / 33243136 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_57 : sigmaPower (57 : Fin 1536) ≤ ((44525976055 / 68719476736 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_58 : sigmaFactor (58 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-162098805 / 2932736 : ℚ) : ℝ) - Real.exp ((-81113395 / 1466368 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_58 : sigmaPower (58 : Fin 1536) ≤ ((91142516284007 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_59 : sigmaFactor (59 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-1376791559 / 24924160 : ℚ) : ℝ) - Real.exp ((-5511517011 / 99696640 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_59 : sigmaPower (59 : Fin 1536) ≤ ((91095818263849 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_60 : sigmaFactor (60 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-458581211 / 8306688 : ℚ) : ℝ) - Real.exp ((-114735929 / 2076672 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_60 : sigmaPower (60 : Fin 1536) ≤ ((91049104892599 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_61 : sigmaFactor (61 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-249944739 / 4530176 : ℚ) : ℝ) - Real.exp ((-500284873 / 9060352 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_61 : sigmaPower (61 : Fin 1536) ≤ ((91002376162687 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_62 : sigmaFactor (62 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2747297707 / 49823744 : ℚ) : ℝ) - Real.exp ((-1374736011 / 24911872 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_62 : sigmaPower (62 : Fin 1536) ≤ ((90955632066537 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_63 : sigmaFactor (63 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-28595875 / 518912 : ℚ) : ℝ) - Real.exp ((-1831585305 / 33210368 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_63 : sigmaPower (63 : Fin 1536) ≤ ((11363609074571 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_64 : sigmaFactor (64 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-85722219 / 1556480 : ℚ) : ℝ) - Real.exp ((-1340471 / 24320 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_64 : sigmaPower (64 : Fin 1536) ≤ ((181724195490389 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_65 : sigmaFactor (65 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2741018731 / 49799168 : ℚ) : ℝ) - Real.exp ((-5486383947 / 99598336 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_65 : sigmaPower (65 : Fin 1536) ≤ ((181630615009651 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_66 : sigmaFactor (66 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-912975723 / 16596992 : ℚ) : ℝ) - Real.exp ((-456850009 / 8298496 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_66 : sigmaPower (66 : Fin 1536) ≤ ((181537003735731 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_67 : sigmaFactor (67 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-1368418161 / 24891392 : ℚ) : ℝ) - Real.exp ((-5478017699 / 99565568 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_67 : sigmaPower (67 : Fin 1536) ≤ ((45360840413357 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_68 : sigmaFactor (68 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-1367373095 / 24887296 : ℚ) : ℝ) - Real.exp ((-342114795 / 6221824 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_68 : sigmaPower (68 : Fin 1536) ≤ ((181349688747529 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_69 : sigmaFactor (69 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-910885591 / 16588800 : ℚ) : ℝ) - Real.exp ((-1823219057 / 33177600 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_69 : sigmaPower (69 : Fin 1536) ≤ ((181255985002813 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_70 : sigmaFactor (70 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2730568071 / 49758208 : ℚ) : ℝ) - Real.exp ((-1366369763 / 24879104 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_70 : sigmaPower (70 : Fin 1536) ≤ ((181162250404049 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_71 : sigmaFactor (71 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-682120021 / 12437504 : ℚ) : ℝ) - Real.exp ((-5461302363 / 99500032 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_71 : sigmaPower (71 : Fin 1536) ≤ ((181068484935995 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_72 : sigmaFactor (72 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-20654491 / 376832 : ℚ) : ℝ) - Real.exp ((-2583867 / 47104 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_72 : sigmaPower (72 : Fin 1536) ≤ ((22621836072925 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_73 : sigmaFactor (73 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2724306255 / 49733632 : ℚ) : ℝ) - Real.exp ((-5452953275 / 99467264 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_73 : sigmaPower (73 : Fin 1536) ≤ ((180880861331001 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_74 : sigmaFactor (74 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2722220413 / 49725440 : ℚ) : ℝ) - Real.exp ((-1362195219 / 24862720 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_74 : sigmaPower (74 : Fin 1536) ≤ ((22598375395441 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_75 : sigmaFactor (75 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-26667993 / 487424 : ℚ) : ℝ) - Real.exp ((-106757057 / 1949696 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_75 : sigmaPower (75 : Fin 1536) ≤ ((90346557032849 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_76 : sigmaFactor (76 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-1359025437 / 24854528 : ℚ) : ℝ) - Real.exp ((-340027523 / 6213632 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_76 : sigmaPower (76 : Fin 1536) ≤ ((180599194022219 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_77 : sigmaFactor (77 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2715967177 / 49700864 : ℚ) : ℝ) - Real.exp ((-5436272259 / 99401728 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_77 : sigmaPower (77 : Fin 1536) ≤ ((180505243017789 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_78 : sigmaFactor (78 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-904628065 / 16564224 : ℚ) : ℝ) - Real.exp ((-452675465 / 8282112 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_78 : sigmaPower (78 : Fin 1536) ≤ ((90205630518549 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_79 : sigmaFactor (79 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-338975241 / 6210560 : ℚ) : ℝ) - Real.exp ((-5427940331 / 99368960 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_79 : sigmaPower (79 : Fin 1536) ≤ ((180317248064821 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_80 : sigmaFactor (80 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-338715047 / 6209536 : ℚ) : ℝ) - Real.exp ((-21186627 / 388096 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_80 : sigmaPower (80 : Fin 1536) ≤ ((180223204085627 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_81 : sigmaFactor (81 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-902546513 / 16556032 : ℚ) : ℝ) - Real.exp ((-1806538041 / 33112064 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_81 : sigmaPower (81 : Fin 1536) ≤ ((90064564542087 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_82 : sigmaFactor (82 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2705559417 / 49659904 : ℚ) : ℝ) - Real.exp ((-1353863291 / 24829952 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_82 : sigmaPower (82 : Fin 1536) ≤ ((180035023045109 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_83 : sigmaFactor (83 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-122885455 / 2256896 : ℚ) : ℝ) - Real.exp ((-491935785 / 9027584 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_83 : sigmaPower (83 : Fin 1536) ≤ ((89970442976535 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_84 : sigmaFactor (84 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-450233553 / 8273920 : ℚ) : ℝ) - Real.exp ((-112648657 / 2068480 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_84 : sigmaPower (84 : Fin 1536) ≤ ((44961679448171 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_85 : sigmaFactor (85 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2699323341 / 49635328 : ℚ) : ℝ) - Real.exp ((-5402978867 / 99270656 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_85 : sigmaPower (85 : Fin 1536) ≤ ((179752518548567 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_86 : sigmaFactor (86 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2697246079 / 49627136 : ℚ) : ℝ) - Real.exp ((-1349705907 / 24813568 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_86 : sigmaPower (86 : Fin 1536) ≤ ((179658288205327 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_87 : sigmaFactor (87 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-224597461 / 4134912 : ℚ) : ℝ) - Real.exp ((-1798223273 / 33079296 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_87 : sigmaPower (87 : Fin 1536) ≤ ((179564026747561 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_88 : sigmaFactor (88 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-673273425 / 12402688 : ℚ) : ℝ) - Real.exp ((-84226835 / 1550336 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_88 : sigmaPower (88 : Fin 1536) ≤ ((179469734159855 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_89 : sigmaFactor (89 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2691018583 / 49602560 : ℚ) : ℝ) - Real.exp ((-5386366491 / 99205120 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_89 : sigmaPower (89 : Fin 1536) ≤ ((89687705213393 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_90 : sigmaFactor (90 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-896314727 / 16531456 : ℚ) : ℝ) - Real.exp ((-448518081 / 8265728 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_90 : sigmaPower (90 : Fin 1536) ≤ ((179281055532919 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_91 : sigmaFactor (91 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-1343435247 / 24793088 : ℚ) : ℝ) - Real.exp ((-5378068883 / 99172352 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_91 : sigmaPower (91 : Fin 1536) ≤ ((179186669462811 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_92 : sigmaFactor (92 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-78964633 / 1458176 : ℚ) : ℝ) - Real.exp ((-19757067 / 364544 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_92 : sigmaPower (92 : Fin 1536) ≤ ((11193265762563 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_93 : sigmaFactor (93 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-894241755 / 16523264 : ℚ) : ℝ) - Real.exp ((-1789925665 / 33046528 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_93 : sigmaPower (93 : Fin 1536) ≤ ((178997803732045 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_94 : sigmaFactor (94 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-22154163 / 409600 : ℚ) : ℝ) - Real.exp ((-11086019 / 204800 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_94 : sigmaPower (94 : Fin 1536) ≤ ((698841109533 / 1099511627776 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_95 : sigmaFactor (95 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-167411431 / 3097088 : ℚ) : ℝ) - Real.exp ((-5361490827 / 99106816 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_95 : sigmaPower (95 : Fin 1536) ≤ ((44702203277683 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_96 : sigmaFactor (96 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-55760683 / 1032192 : ℚ) : ℝ) - Real.exp ((-1743929 / 32256 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_96 : sigmaPower (96 : Fin 1536) ≤ ((178714270927401 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_97 : sigmaFactor (97 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2674443387 / 49537024 : ℚ) : ℝ) - Real.exp ((-5353210379 / 99074048 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_97 : sigmaPower (97 : Fin 1536) ≤ ((178619697474951 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_98 : sigmaFactor (98 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2672374705 / 49528832 : ℚ) : ℝ) - Real.exp ((-1337268075 / 24764416 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_98 : sigmaPower (98 : Fin 1536) ≤ ((178525092737865 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_99 : sigmaFactor (99 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-445051123 / 8253440 : ℚ) : ℝ) - Real.exp ((-1781645217 / 33013760 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_99 : sigmaPower (99 : Fin 1536) ≤ ((89215228350309 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_100 : sigmaFactor (100 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-1334119743 / 24756224 : ℚ) : ℝ) - Real.exp ((-333800027 / 6189056 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_100 : sigmaPower (100 : Fin 1536) ≤ ((89167894673837 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_101 : sigmaFactor (101 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2666172949 / 49504256 : ℚ) : ℝ) - Real.exp ((-5336666643 / 99008512 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_101 : sigmaPower (101 : Fin 1536) ≤ ((89120545331743 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_102 : sigmaFactor (102 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-888035709 / 16498688 : ℚ) : ℝ) - Real.exp ((-444377857 / 8249344 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_102 : sigmaPower (102 : Fin 1536) ≤ ((89073180316249 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_103 : sigmaFactor (103 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-665510505 / 12371968 : ℚ) : ℝ) - Real.exp ((-5328403355 / 98975744 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_103 : sigmaPower (103 : Fin 1536) ≤ ((89025799619571 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_104 : sigmaFactor (104 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-664994407 / 12369920 : ℚ) : ℝ) - Real.exp ((-83191779 / 1546240 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_104 : sigmaPower (104 : Fin 1536) ≤ ((177956806467841 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_105 : sigmaFactor (105 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-80542847 / 1499136 : ℚ) : ℝ) - Real.exp ((-161216539 / 2998272 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_105 : sigmaPower (105 : Fin 1536) ≤ ((5558186946969 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_106 : sigmaFactor (106 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2655850989 / 49463296 : ℚ) : ℝ) - Real.exp ((-1329004787 / 24731648 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_106 : sigmaPower (106 : Fin 1536) ≤ ((177767126729045 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_107 : sigmaFactor (107 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-1326894371 / 24727552 : ℚ) : ℝ) - Real.exp ((-5311893939 / 98910208 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_107 : sigmaPower (107 : Fin 1536) ≤ ((88836119865171 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_108 : sigmaFactor (108 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-441954535 / 8241152 : ℚ) : ℝ) - Real.exp ((-110578545 / 2060288 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_108 : sigmaPower (108 : Fin 1536) ≤ ((88788660645641 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_109 : sigmaFactor (109 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-155862729 / 2908160 : ℚ) : ℝ) - Real.exp ((-311979283 / 5816320 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_109 : sigmaPower (109 : Fin 1536) ≤ ((44370592849059 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_110 : sigmaFactor (110 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2647606291 / 49430528 : ℚ) : ℝ) - Real.exp ((-1324881723 / 24715264 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_110 : sigmaPower (110 : Fin 1536) ≤ ((44346847507391 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_111 : sigmaFactor (111 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-110231121 / 2059264 : ℚ) : ℝ) - Real.exp ((-1765135801 / 32948224 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_111 : sigmaPower (111 : Fin 1536) ≤ ((177292377175617 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_112 : sigmaFactor (112 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-330436029 / 6176768 : ℚ) : ℝ) - Real.exp ((-20669099 / 386048 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_112 : sigmaPower (112 : Fin 1536) ≤ ((88598666409367 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_113 : sigmaFactor (113 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2641430275 / 49405952 : ℚ) : ℝ) - Real.exp ((-5287172715 / 98811904 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_113 : sigmaPower (113 : Fin 1536) ≤ ((44275564235811 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_114 : sigmaFactor (114 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-879791011 / 16465920 : ℚ) : ℝ) - Real.exp ((-440254793 / 8232960 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_114 : sigmaPower (114 : Fin 1536) ≤ ((44251787383367 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_115 : sigmaFactor (115 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-1318658253 / 24694784 : ℚ) : ℝ) - Real.exp ((-5278943747 / 98779136 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_115 : sigmaPower (115 : Fin 1536) ≤ ((176912010573713 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_116 : sigmaFactor (116 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-119784577 / 2244608 : ℚ) : ℝ) - Real.exp ((-29970633 / 561152 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_116 : sigmaPower (116 : Fin 1536) ≤ ((88408420024139 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_117 : sigmaFactor (117 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-877735199 / 16457728 : ℚ) : ℝ) - Real.exp ((-1756906833 / 32915456 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_117 : sigmaPower (117 : Fin 1536) ≤ ((176721637941451 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_118 : sigmaFactor (118 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2631151215 / 49364992 : ℚ) : ℝ) - Real.exp ((-1316652755 / 24682496 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_118 : sigmaPower (118 : Fin 1536) ≤ ((176626404237509 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_119 : sigmaFactor (119 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-657274387 / 12339200 : ℚ) : ℝ) - Real.exp ((-5262502971 / 98713600 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_119 : sigmaPower (119 : Fin 1536) ≤ ((11033196182545 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_120 : sigmaFactor (120 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-218920383 / 4112384 : ℚ) : ℝ) - Real.exp ((-27387481 / 514048 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_120 : sigmaPower (120 : Fin 1536) ≤ ((176435841975339 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_121 : sigmaFactor (121 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2624992359 / 49340416 : ℚ) : ℝ) - Real.exp ((-5254291163 / 98680832 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_121 : sigmaPower (121 : Fin 1536) ≤ ((176340513385613 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_122 : sigmaFactor (122 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2622940837 / 49332224 : ℚ) : ℝ) - Real.exp ((-1312546851 / 24666112 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_122 : sigmaPower (122 : Fin 1536) ≤ ((176245153135777 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_123 : sigmaFactor (123 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-436815005 / 8220672 : ℚ) : ℝ) - Real.exp ((-1748695025 / 32882688 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_123 : sigmaPower (123 : Fin 1536) ≤ ((176149761210057 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_124 : sigmaFactor (124 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-1309419969 / 24657920 : ℚ) : ℝ) - Real.exp ((-327624011 / 6164480 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_124 : sigmaPower (124 : Fin 1536) ≤ ((44013584398167 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_125 : sigmaFactor (125 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-2616790561 / 49307648 : ℚ) : ℝ) - Real.exp ((-5237884707 / 98615296 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_125 : sigmaPower (125 : Fin 1536) ≤ ((175958882267813 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_126 : sigmaFactor (126 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-51269449 / 966656 : ℚ) : ℝ) - Real.exp ((-25655817 / 483328 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_126 : sigmaPower (126 : Fin 1536) ≤ ((87931697609843 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_127 : sigmaFactor (127 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-3711213 / 70016 : ℚ) : ℝ) - Real.exp ((-475426369 / 8962048 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_127 : sigmaPower (127 : Fin 1536) ≤ ((87883938216235 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

end LegendreK6.M2Pilot.Enclosures.Sigma000
