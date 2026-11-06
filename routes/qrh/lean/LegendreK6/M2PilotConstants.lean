import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

namespace LegendreK6.M2Pilot

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem first_height_exp_lower :
    Real.exp (((215 / 64 : ℚ) : ℝ)) ≤ (((1842 / 64 : ℚ) : ℝ)) := by
  dyadic_interval [prec := 64]

theorem last_height_exp_upper :
    (((2829 / 64 : ℚ) : ℝ)) ≤ Real.exp (((284 / 64 : ℚ) : ℝ)) := by
  dyadic_interval [prec := 64]

theorem start_height_ge_RH :
    (3000000000000 : ℝ) ≤ Real.exp (((1841 / 64 : ℚ) : ℝ)) := by
  dyadic_interval [prec := 64]

theorem start_heightZ_lower : (31 / 64 : ℝ) ≤ heightZ (1841 / 64) := by
  have h : (((31 / 64 : ℚ) : ℝ)) ≤ Real.exp (-(((1841 / 64 : ℚ) : ℝ))) +
      (((1 / 6 : ℚ) : ℝ)) * Real.exp (((205 / 192 : ℚ) : ℝ)) := by
    dyadic_interval [prec := 64]
  norm_num [heightZ, right] at *
  linarith

theorem start_logKernel_eq_one : logKernel (1841 / 64) = 1 := by
  have hz := start_heightZ_lower
  have hsq := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 31 / 64) hz
  unfold logKernel zKernel
  apply min_eq_left
  apply le_min <;> nlinarith

end LegendreK6.M2Pilot
