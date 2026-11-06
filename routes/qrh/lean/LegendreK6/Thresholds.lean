import LegendreK6.Definitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-!
# Kernel-checked exponential thresholds

The `dyadic_interval` tactic below uses its default reflective mode, not
`+native`: interval computations are rechecked by the Lean kernel. The constants
are the lower integer thresholds in the corrected CHL table conversion.
-/

namespace LegendreK6

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem chl_threshold_43 : Real.exp 43 ≤ (1296 : ℝ) ^ 6 := by
  dyadic_interval [prec := 40]

theorem chl_threshold_46 : Real.exp 46 ≤ (2136 : ℝ) ^ 6 := by
  dyadic_interval [prec := 40]

theorem chl_threshold_50 : Real.exp 50 ≤ (4161 : ℝ) ^ 6 := by
  dyadic_interval [prec := 40]

theorem chl_threshold_55 : Real.exp 55 ≤ (9573 : ℝ) ^ 6 := by
  dyadic_interval [prec := 40]

theorem chl_threshold_60 : Real.exp 60 ≤ (22027 : ℝ) ^ 6 := by
  dyadic_interval [prec := 40]

theorem chl_threshold_75 : Real.exp 75 ≤ (268338 : ℝ) ^ 6 := by
  dyadic_interval [prec := 40]

theorem chl_threshold_90 : Real.exp 90 ≤ (3269018 : ℝ) ^ 6 := by
  dyadic_interval [prec := 40]

theorem chl_threshold_105 : Real.exp 105 ≤ (39824785 : ℝ) ^ 6 := by
  dyadic_interval [prec := 40]

theorem chl_threshold_120 : Real.exp 120 ≤ (485165196 : ℝ) ^ 6 := by
  dyadic_interval [prec := 40]

theorem chl_threshold_135 : Real.exp 135 ≤ (5910522064 : ℝ) ^ 6 := by
  dyadic_interval [prec := 40]

theorem chl_threshold_150 : Real.exp 150 ≤ (72004899338 : ℝ) ^ 6 := by
  dyadic_interval [prec := 40]

theorem lower_join_exp : Real.exp 167 < (1242317999994 : ℝ) ^ 6 := by
  dyadic_interval [prec := 20]

end LegendreK6
