import Mathlib
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-!
# Kernel-checked numerical threshold for the six-term analytic tail

The default reflective `dyadic_interval` proofs below are checked by Lean's
kernel. They do not import an Arb success flag. Connecting this expression to
the zeta explicit formula is a separate analytic obligation.
-/

namespace LegendreK6

set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def tailU (L : ℝ) : ℝ := (9 / 32) * L + Real.log 2
noncomputable def tailLambda (L : ℝ) : ℝ := L / 4 - (8 / 3) * Real.log 2
noncomputable def tailBound (L : ℝ) : ℝ :=
  4 * tailU L * Real.exp (-3 * L / 32) +
  (1122 / 25) * (tailU L) ^ 3 * (L / tailLambda L) * Real.exp (-tailLambda L / 8) +
  2 * ((829 / 100) * (tailU L) ^ 2 + 147 * tailU L) * Real.exp (-L / 8) +
  (1447 / 2000) * (3 * L + 2) * Real.exp (-L / 32) +
  (1 / 2) * (L + 1) ^ 2 * Real.exp (-L / 4) +
  (1 / 4) * (L + 1) * Real.exp (-3 * L / 4)

theorem log_two_bounds :
    (0.693147 : ℝ) < Real.log 2 ∧
    Real.log 2 < (0.693148 : ℝ) := by
  constructor
  · apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 2)).2
    dyadic_interval [prec := 48]
  · apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).2
    dyadic_interval [prec := 48]

theorem tail_at_700 : tailBound 700 < (14 / 25 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := log_two_bounds
  let u : ℝ := tailU 700
  let l : ℝ := tailLambda 700
  have hu0 : 197.568147 < u := by dsimp [u, tailU]; linarith
  have hu1 : u < 197.568148 := by dsimp [u, tailU]; linarith
  have hl0 : 173.1516 < l := by dsimp [l, tailLambda]; linarith
  have hl1 : l < 173.1517 := by dsimp [l, tailLambda]; linarith
  have hlpos : 0 < l := by linarith
  let A : ℝ := 4 * u * Real.exp (-65.625) +
    2 * (8.29 * u ^ 2 + 147 * u) * Real.exp (-87.5) +
    0.7235 * 2102 * Real.exp (-21.875) +
    0.5 * 701 ^ 2 * Real.exp (-175) + 0.25 * 701 * Real.exp (-525)
  let B : ℝ := 44.88 * u ^ 3 * 700 * Real.exp (-0.125 * l)
  have hcalc : A * l + B < 0.56 * l := by
    dsimp [A, B]
    dyadic_interval [prec := 64]
  have heq : tailBound 700 = A + B / l := by
    dsimp [tailBound, A, B, u, l, tailU, tailLambda]
    norm_num
    ring
  rw [heq]
  have hclear : (A + B / l) * l < (14 / 25 : ℝ) * l := by
    field_simp
    nlinarith
  exact (mul_lt_mul_iff_of_pos_right hlpos).mp hclear

theorem tail_scaled_at_700 : (53 / 50 : ℝ) * tailBound 700 < 1 := by
  have h := tail_at_700
  linarith

end LegendreK6
