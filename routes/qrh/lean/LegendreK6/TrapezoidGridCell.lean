import LegendreK6.TrapezoidCell
import LegendreK6.TrapezoidHeightBound

/-!
# A full analytic reduction for one middle cell

Only explicitly named literature inputs and numerical statements about the
displayed finite grid expression occur below. There is no assumed weighted
zero estimate or local prime conclusion. The pilot numerical module must
discharge all finite grid and budget conditions to close milestone 2.
-/

namespace LegendreK6

theorem middle_cell_of_grid_budget
    (HQ : QRHSevenEighths) (HC : CSv2) (HR : RosserZeroCount)
    (HF : IntegratedExplicitFormula)
    (s : ℕ → ℝ) (row : ℕ → Fin 12) (nSigma : ℕ)
    (A C : ℝ) (u : ℕ → ℝ) (nHeight : ℕ)
    (hA : 167 ≤ A) (hs : Monotone s) (hs0 : s 0 = 1/2) (hsn : 7/8 ≤ s nSigma)
    (hrows : ∀ j < nSigma, (16 + ((row j).val : ℝ))/32 ≤ s j ∧
      s j ≤ (17 + ((row j).val : ℝ))/32)
    (hu : Monotone u) (huH : 3000000000000 ≤ Real.exp (u 0)) (hu1 : 1 ≤ u 0)
    (hU : 6 ≤ u nHeight)
    (hstart : trapezoidHeightKernel (1+Real.exp (C/6)/6) (Real.exp (u 0)) = 1)
    (hbudget : 2*trapezoidHeightBudget s row nSigma A (1+Real.exp (C/6)/6) u nHeight +
      middlePrimePowerBudget A C + cellTrivialBudget A < 1)
    (x : ℝ) (hx : 0 < x) (hxA : A ≤ Real.log x) (hxC : Real.log x ≤ C) :
    ShortInterval6 x := by
  have hh := middle_prime_of_zero_budget HF A C (Real.log x)
    (2*trapezoidHeightBudget s row nSigma A (1+Real.exp (C/6)/6) u nHeight)
    hA hxA hxC
    (fun T => norm_truncatedTrapezoidZeroSum_le_heightBudget HQ HC HR s row nSigma
      (Real.log x) A (middleH (Real.log x)) (1+Real.exp (C/6)/6) T u nHeight
      (middleH_pos _) (by linarith) hxA (by positivity)
      (middle_q_cell_le (Real.log x) C hxC) hs hs0 hsn hrows hu huH hu1 hU hstart)
    hbudget
  simpa only [middleX, Real.exp_log hx] using hh

end LegendreK6
