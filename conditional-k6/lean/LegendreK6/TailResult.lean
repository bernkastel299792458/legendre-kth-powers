import LegendreK6.TailArithmetic
import LegendreK6.TailMonotonic

/-!
# Infinite-range verification of the six-term tail expression

Both the threshold and the monotonicity are kernel-checked. This theorem concerns
the explicit real function `tailBound`; its connection to zeta zeros and a prime
interval still requires the separately recorded analytic bridge.
-/

namespace LegendreK6

theorem tailBound_eq_decay (L : ℝ) :
    tailBound L = tailDecayExpression (Real.log 2) L := by
  unfold tailBound tailU tailLambda tailDecayExpression
  have e0 : Real.exp (-3 * L / 32) = Real.exp (-(3 / 32) * L + 0) := by
    congr 1; ring
  have e1 : Real.exp (-(L / 4 - (8 / 3) * Real.log 2) / 8) =
      Real.exp (-(1 / 32) * L + Real.log 2 / 3) := by
    congr 1; ring
  have e2 : Real.exp (-L / 8) = Real.exp (-(1 / 8) * L + 0) := by
    congr 1; ring
  have eR : Real.exp (-L / 32) = Real.exp (-(1 / 32) * L + 0) := by
    congr 1; ring
  have eP : Real.exp (-L / 4) = Real.exp (-(1 / 4) * L + 0) := by
    congr 1; ring
  have eB : Real.exp (-3 * L / 4) = Real.exp (-(3 / 4) * L + 0) := by
    congr 1; ring
  rw [e0, e1, e2, eR, eP, eB]
  ring

theorem tailBound_antitone : AntitoneOn tailBound (Set.Ici 700) := by
  obtain ⟨hlo, hhi⟩ := log_two_bounds
  have h := tail_decay_antitone (Real.log 2) (by linarith) (by linarith)
  intro x hx y hy hxy
  rw [tailBound_eq_decay, tailBound_eq_decay]
  exact h hx hy hxy

theorem tail_bound_all {L : ℝ} (hL : 700 ≤ L) : tailBound L < (14 / 25 : ℝ) := by
  exact lt_of_le_of_lt (tailBound_antitone (by norm_num) hL hL) tail_at_700

theorem tail_scaled_bound_all {L : ℝ} (hL : 700 ≤ L) :
    (53 / 50 : ℝ) * tailBound L < 1 := by
  have h := tail_bound_all hL
  linarith

end LegendreK6
