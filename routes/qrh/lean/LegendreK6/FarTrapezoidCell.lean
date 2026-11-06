import LegendreK6.FarDomains
import LegendreK6.TrapezoidCell
import LegendreK6.TrapezoidHeightBound

/-!
# A trapezoid reduction for the fourth-power far segment

This is a new formal route to the original far-segment conclusion. The
historical polynomial weight and its frozen certificates are not changed.
The finite-grid budget is an explicit remaining numerical obligation in the
intermediate cell theorem; no completed far certificate is claimed here.
-/

namespace LegendreK6

/-- The existing actual trivial-zero series has the same uniform cell bound
for the fourth-power interval. -/
theorem far_trivial_zero_cell_le (A L : ℝ) (hA : 400 ≤ A) (hAL : A ≤ L) :
    ‖trapezoidTrivialDifference (farX L) (farH L) (1/32) (31/32)‖ ≤
      farH L * cellTrivialBudget A := by
  have hx := far_X_gt_one L (hA.trans hAL)
  have hh := norm_trapezoidTrivialDifference_le hx (farH_pos L)
    (by norm_num : (0:ℝ)<1/32) (by norm_num : (0:ℝ)<31/32) (by norm_num)
  have hpow (r : ℝ) : (farX L)^r = Real.exp (r*L) := by
    rw [Real.rpow_def_of_pos (farX_pos L), far_log_X, mul_comm]
  rw [hpow, hpow] at hh
  have he : farH L * Real.exp (-3*L) / (1-Real.exp (-2*L)) =
      farH L * cellTrivialBudget L := by unfold cellTrivialBudget; ring
  rw [he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (cellTrivialBudget_antitone (by linarith) hAL) (farH_pos L).le)

/-- Supply the actual prime-power and trivial-zero terms. The uniform zero
bound and scalar inequality remain explicit caller obligations. -/
theorem far_prime_of_zero_budget (H : IntegratedExplicitFormula)
    (A C L Z : ℝ) (hA : 400 ≤ A) (hAL : A ≤ L) (hLC : L ≤ C)
    (hZ : ∀ T : ℝ,
      ‖truncatedTrapezoidZeroSum (farX L) (farH L) (1/32) (31/32) T‖ ≤ farH L*Z)
    (hbudget : Z + farPrimePowerBudget A C + cellTrivialBudget A < 1) :
    ShortInterval4 (farX L) := by
  have hp := prime_of_trapezoid_budgets H (farX L) (farH L) (1/32) (31/32)
    (farY L) Z (farPrimePowerBudget A C) (cellTrivialBudget A)
    (far_X_gt_one L (hA.trans hAL))
    (by norm_num) (by norm_num) (by norm_num) (farH_pos L) (le_refl _)
    hZ (far_trivial_zero_cell_le A L hA hAL) (far_prime_power_le A C L hA hAL hLC) hbudget
  simpa only [ShortInterval4, farH_eq_rpow] using hp

/-- Full actual analytic reduction for one fourth-power far cell. Its only
project-specific premise is the displayed finite grid budget inequality. -/
theorem far_cell_of_grid_budget
    (HQ : QRHSevenEighths) (HC : CSv2) (HR : RosserZeroCount)
    (HF : IntegratedExplicitFormula)
    (s : ℕ → ℝ) (row : ℕ → Fin 12) (nSigma : ℕ)
    (A C : ℝ) (u : ℕ → ℝ) (nHeight : ℕ)
    (hA : 400 ≤ A) (hs : Monotone s) (hs0 : s 0 = 1/2) (hsn : 7/8 ≤ s nSigma)
    (hrows : ∀ j < nSigma, (16 + ((row j).val : ℝ))/32 ≤ s j ∧
      s j ≤ (17 + ((row j).val : ℝ))/32)
    (hu : Monotone u) (huH : 3000000000000 ≤ Real.exp (u 0)) (hu1 : 1 ≤ u 0)
    (hU : 6 ≤ u nHeight)
    (hstart : trapezoidHeightKernel (1+Real.exp (C/4)/4) (Real.exp (u 0)) = 1)
    (hbudget : 2*trapezoidHeightBudget s row nSigma A (1+Real.exp (C/4)/4) u nHeight +
      farPrimePowerBudget A C + cellTrivialBudget A < 1)
    (x : ℝ) (hx : 0 < x) (hxA : A ≤ Real.log x) (hxC : Real.log x ≤ C) :
    ShortInterval4 x := by
  have hh := far_prime_of_zero_budget HF A C (Real.log x)
    (2*trapezoidHeightBudget s row nSigma A (1+Real.exp (C/4)/4) u nHeight)
    hA hxA hxC
    (fun T => norm_truncatedTrapezoidZeroSum_le_heightBudget HQ HC HR s row nSigma
      (Real.log x) A (farH (Real.log x)) (1+Real.exp (C/4)/4) T u nHeight
      (farH_pos _) (by linarith) hxA (by positivity)
      (far_q_cell_le (Real.log x) C hxC) hs hs0 hsn hrows hu huH hu1 hU hstart)
    hbudget
  simpa only [farX, Real.exp_log hx] using hh

/-- A freely enlarged common q permits exact exponential translation of the
height grid without identifying q with the endpoint ratio. -/
theorem far_cell_of_grid_budget_with_q
    (HQ : QRHSevenEighths) (HC : CSv2) (HR : RosserZeroCount)
    (HF : IntegratedExplicitFormula)
    (s : ℕ → ℝ) (row : ℕ → Fin 12) (nSigma : ℕ)
    (A C q : ℝ) (u : ℕ → ℝ) (nHeight : ℕ)
    (hA : 400 ≤ A) (hq : 1+Real.exp (C/4)/4 ≤ q) (hs : Monotone s) (hs0 : s 0 = 1/2) (hsn : 7/8 ≤ s nSigma)
    (hrows : ∀ j < nSigma, (16 + ((row j).val : ℝ))/32 ≤ s j ∧
      s j ≤ (17 + ((row j).val : ℝ))/32)
    (hu : Monotone u) (huH : 3000000000000 ≤ Real.exp (u 0)) (hu1 : 1 ≤ u 0)
    (hU : 6 ≤ u nHeight)
    (hstart : trapezoidHeightKernel q (Real.exp (u 0)) = 1)
    (hbudget : 2*trapezoidHeightBudget s row nSigma A q u nHeight +
      farPrimePowerBudget A C + cellTrivialBudget A < 1)
    (x : ℝ) (hx : 0 < x) (hxA : A ≤ Real.log x) (hxC : Real.log x ≤ C) :
    ShortInterval4 x := by
  have hh := far_prime_of_zero_budget HF A C (Real.log x)
    (2*trapezoidHeightBudget s row nSigma A q u nHeight)
    hA hxA hxC
    (fun T => norm_truncatedTrapezoidZeroSum_le_heightBudget HQ HC HR s row nSigma
      (Real.log x) A (farH (Real.log x)) q T u nHeight
      (farH_pos _) (by linarith) hxA ((show 0 ≤ 1+Real.exp (C/4)/4 by positivity).trans hq)
      ((far_q_cell_le (Real.log x) C hxC).trans hq) hs hs0 hsn hrows hu huH hu1 hU hstart)
    hbudget
  simpa only [farX, Real.exp_log hx] using hh

end LegendreK6
