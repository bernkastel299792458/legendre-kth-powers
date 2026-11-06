import LegendreK6.TailZeroSum
import LegendreK6.TailErrorBudgets
import LegendreK6.TailResult

/-!
# The infinite prime-interval tail from precisely named external inputs

This module closes the tail branch: actual zeta zero contributions, actual
Chebyshev sums, the stated CHJII error, and all six budgets are connected.
There is no assumed local prime conclusion or unexplained weighted budget.
-/

namespace LegendreK6

/-- A residual estimate and a zero-sum norm bound give the corresponding
lower bound for the actual Chebyshev increment. -/
theorem psi_sub_lower_of_complex_residual (x y h R Z : ℝ) (S : ℂ)
    (hres : ‖((Chebyshev.psi y - Chebyshev.psi x - h : ℝ) : ℂ) + S‖ ≤ R)
    (hzero : ‖S‖ ≤ Z) :
    h - (R + Z) ≤ Chebyshev.psi y - Chebyshev.psi x := by
  have htri : ‖((Chebyshev.psi y - Chebyshev.psi x - h : ℝ) : ℂ)‖ ≤
      ‖((Chebyshev.psi y - Chebyshev.psi x - h : ℝ) : ℂ) + S‖ + ‖S‖ := by
    simpa only [add_sub_cancel_right] using
      norm_sub_le (((Chebyshev.psi y - Chebyshev.psi x - h : ℝ) : ℂ) + S) S
  rw [Complex.norm_real, Real.norm_eq_abs] at htri
  have hlow := neg_abs_le (Chebyshev.psi y - Chebyshev.psi x - h)
  linarith

/-- Milestone 1: the tail for the exponential parametrization. Only QRH,
the exact CS table, Rosser's stated bound, and CHJII's stated formula enter. -/
theorem tail_short_interval_exp (HQ : QRHSevenEighths) (HC : CSv2)
    (HR : RosserZeroCount) (HJ : CHJIIShortInterval)
    (L : ℝ) (hL : 700 ≤ L) : ShortInterval4 (tailX L) := by
  let R : ℝ := (1447 / 2000) * (3 * L + 2) * Real.exp (-L / 32)
  let P : ℝ := (1 / 2) * (L + 1) ^ 2 * Real.exp (-L / 4)
  let B : ℝ := (1 / 4) * (L + 1) * Real.exp (-3 * L / 4)
  have hdom : max 51 ((Real.log (tailX L)) ^ 2) < tailT L := by
    rw [tail_log_X]
    exact max_lt (tail_T_gt_51 L hL) (tail_log_sq_lt_T L hL)
  obtain ⟨Tstar, hTslo, hTshi, hres⟩ := HJ (tailX L) (tailH L) (tailT L)
    (tailX_pos L) (by rw [tail_log_X]; linarith) (tailH_pos L).le hdom
    (tail_T_lt_sqrt_limit L hL)
  have hres' :
      ‖((Chebyshev.psi (tailY L) - Chebyshev.psi (tailX L) - tailH L : ℝ) : ℂ) +
        truncatedZeroIncrement (tailX L) (tailY L) Tstar‖ ≤ tailH L * R :=
    hres.trans (tail_truncation_error_le L hL)
  have hzero := tail_truncated_zero_bound HQ HC HR L Tstar hL hTshi
  have hpsi := psi_sub_lower_of_complex_residual (tailX L) (tailY L) (tailH L)
    (tailH L * R) (tailH L * tailZeroBound L)
    (truncatedZeroIncrement (tailX L) (tailY L) Tstar) hres' hzero
  have hpow : Chebyshev.psi (tailY L) - Chebyshev.theta (tailY L) ≤ tailH L * P :=
    tail_prime_power_error_le L hL
  have hend : Real.log (tailY L) ≤ tailH L * B := tail_endpoint_error_le L hL
  have hleft := Chebyshev.theta_le_psi (tailX L)
  have hbound : tailZeroBound L + R + P + B < 1 := by
    have h := tail_bound_all hL
    change tailBound L < (14 / 25 : ℝ) at h
    have heq : tailZeroBound L + R + P + B = tailBound L := by
      dsimp [tailZeroBound, R, P, B, tailBound]
    rw [heq]
    linarith
  have hpositive := tailH_pos L
  have hscaled := mul_lt_mul_of_pos_left hbound hpositive
  have hprime : PrimeInOpenInterval (tailX L) (tailY L) := by
    apply prime_of_theta_sub_gt_log (tailX L) (tailY L) (tailX_pos L).le
      (tail_X_lt_Y L).le (tail_Y_ge_one L hL)
    nlinarith
  simpa only [ShortInterval4, tailY, tailH_eq_rpow] using hprime

/-- The complete tail for every positive real x, with strict prime endpoints. -/
theorem tail_short_interval_from_inputs (HQ : QRHSevenEighths) (HC : CSv2)
    (HR : RosserZeroCount) (HJ : CHJIIShortInterval)
    (x : ℝ) (hx : 0 < x) (hlog : 700 ≤ Real.log x) : ShortInterval4 x := by
  have h := tail_short_interval_exp HQ HC HR HJ (Real.log x) hlog
  simpa only [tailX, Real.exp_log hx] using h

end LegendreK6
