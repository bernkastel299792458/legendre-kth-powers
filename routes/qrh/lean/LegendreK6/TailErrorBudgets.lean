import LegendreK6.PrimePowerBudget
import LegendreK6.TailDomains

/-!
# Actual arithmetic and truncation-error budgets in the tail

These estimates connect actual Chebyshev functions and actual interval
endpoints to the last three terms of `tailBound`. The first estimate bounds
the displayed CHJII remainder expression; invoking that literature theorem
to bound the explicit-formula remainder remains a separate step.
-/

namespace LegendreK6

theorem tail_truncation_scaling (L : ℝ) :
    ((1447 : ℝ) / 500) / tailT L * (tailX L * (3 * L + 2)) =
      tailH L * ((1447 / 2000) * (3 * L + 2) * Real.exp (-L / 32)) := by
  have hratio : tailX L / tailT L = Real.exp (23 * L / 32) := by
    unfold tailX tailT
    rw [← Real.exp_sub]
    congr 1
    ring
  have he : Real.exp (3 * L / 4) * Real.exp (-L / 32) =
      Real.exp (23 * L / 32) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (1447 / 500) * (3 * L + 2) * (tailX L / tailT L) := by ring
    _ = (1447 / 500) * (3 * L + 2) * Real.exp (23 * L / 32) := by rw [hratio]
    _ = _ := by rw [← he]; unfold tailH; ring

/-- The two-endpoint CHJII error expression is bounded by the fourth tail term
times the actual interval length. -/
theorem tail_truncation_error_le (L : ℝ) (hL : 700 ≤ L) :
    ((1447 : ℝ) / 500) / tailT L *
        (tailY L * Real.log (tailY L) + tailX L * Real.log (tailX L)) ≤
      tailH L * ((1447 / 2000) * (3 * L + 2) * Real.exp (-L / 32)) := by
  have hylog : 0 ≤ Real.log (tailY L) := Real.log_nonneg (tail_Y_ge_one L hL)
  have hprod : tailY L * Real.log (tailY L) ≤ 2 * tailX L * (L + 1) :=
    mul_le_mul (tail_Y_le_two_X L hL) (tail_log_Y_le L hL) hylog
      (by have h := tailX_pos L; positivity)
  have hsum : tailY L * Real.log (tailY L) + tailX L * Real.log (tailX L) ≤
      tailX L * (3 * L + 2) := by
    rw [tail_log_X]
    nlinarith
  calc
    _ ≤ ((1447 : ℝ) / 500) / tailT L * (tailX L * (3 * L + 2)) := by
      apply mul_le_mul_of_nonneg_left hsum
      exact div_nonneg (by norm_num) (tailT_pos L).le
    _ = _ := tail_truncation_scaling L

theorem tail_prime_power_scaling (L : ℝ) :
    tailH L * ((1 / 2) * (L + 1) ^ 2 * Real.exp (-L / 4)) =
      2 * Real.sqrt (tailX L) * (L + 1) ^ 2 := by
  have he : Real.exp (3 * L / 4) * Real.exp (-L / 4) = Real.exp (L / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [tail_sqrt_X, ← he]
  unfold tailH
  ring

/-- A formalized unconditional Chebyshev estimate is already stronger than the
fifth tail term throughout the actual tail domain. -/
theorem tail_prime_power_error_le (L : ℝ) (hL : 700 ≤ L) :
    Chebyshev.psi (tailY L) - Chebyshev.theta (tailY L) ≤
      tailH L * ((1 / 2) * (L + 1) ^ 2 * Real.exp (-L / 4)) := by
  have hbase : Chebyshev.psi (tailY L) - Chebyshev.theta (tailY L) ≤
      2 * Real.sqrt (tailY L) * Real.log (tailY L) :=
    (le_abs_self _).trans (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (tail_Y_ge_one L hL))
  have hlog0 : 0 ≤ Real.log (tailY L) := Real.log_nonneg (tail_Y_ge_one L hL)
  have hp : Real.sqrt (tailY L) * Real.log (tailY L) ≤
      (2 * Real.sqrt (tailX L)) * (L + 1) :=
    mul_le_mul (tail_sqrt_Y_le L hL) (tail_log_Y_le L hL) hlog0 (by positivity)
  have hl : 2 * (L + 1) ≤ (L + 1) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hl
    (show 0 ≤ 2 * Real.sqrt (tailX L) by positivity)
  rw [tail_prime_power_scaling]
  nlinarith

theorem tail_endpoint_scaling (L : ℝ) :
    tailH L * ((1 / 4) * (L + 1) * Real.exp (-3 * L / 4)) = L + 1 := by
  have he : Real.exp (3 * L / 4) * Real.exp (-3 * L / 4) = 1 := by
    rw [← Real.exp_add, show 3 * L / 4 + -3 * L / 4 = 0 by ring, Real.exp_zero]
  calc
    _ = (L + 1) * (Real.exp (3 * L / 4) * Real.exp (-3 * L / 4)) := by
      unfold tailH
      ring
    _ = _ := by rw [he]; ring

/-- This budget reserves the entire possible contribution of a prime at the
right endpoint, ensuring that the final prime lies in a strict open interval. -/
theorem tail_endpoint_error_le (L : ℝ) (hL : 700 ≤ L) :
    Real.log (tailY L) ≤
      tailH L * ((1 / 4) * (L + 1) * Real.exp (-3 * L / 4)) := by
  rw [tail_endpoint_scaling]
  exact tail_log_Y_le L hL

end LegendreK6
