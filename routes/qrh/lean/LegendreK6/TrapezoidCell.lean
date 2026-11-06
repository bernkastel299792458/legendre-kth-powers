import LegendreK6.TrapezoidPrime
import LegendreK6.TrapezoidTrivial

/-! Uniform real-variable cell budgets; no numerical certificate is assumed. -/

namespace LegendreK6

noncomputable def cellTrivialBudget (A : ℝ) : ℝ :=
  Real.exp (-3*A) / (1 - Real.exp (-2*A))

theorem cellTrivialBudget_nonneg (A : ℝ) (hA : 0 < A) :
    0 ≤ cellTrivialBudget A := by
  have he : Real.exp (-2*A) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  unfold cellTrivialBudget
  exact div_nonneg (Real.exp_nonneg _) (by linarith)

theorem cellTrivialBudget_antitone {A L : ℝ} (hA : 0 < A) (hAL : A ≤ L) :
    cellTrivialBudget L ≤ cellTrivialBudget A := by
  have hdenA : 0 < 1 - Real.exp (-2*A) := by
    have he : Real.exp (-2*A) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hnum : Real.exp (-3*L) ≤ Real.exp (-3*A) := Real.exp_le_exp.mpr (by linarith)
  have hden : 1 - Real.exp (-2*A) ≤ 1 - Real.exp (-2*L) := by
    have he : Real.exp (-2*L) ≤ Real.exp (-2*A) := Real.exp_le_exp.mpr (by linarith)
    linarith
  exact div_le_div₀ (Real.exp_nonneg _) hnum hdenA hden

theorem middle_trivial_zero_cell_le (A L : ℝ) (hA : 167 ≤ A) (hAL : A ≤ L) :
    ‖trapezoidTrivialDifference (middleX L) (middleH L) (1/32) (31/32)‖ ≤
      middleH L * cellTrivialBudget A := by
  have hx := middle_X_gt_one L (hA.trans hAL)
  have hh := norm_trapezoidTrivialDifference_le hx (middleH_pos L)
    (by norm_num : (0:ℝ)<1/32) (by norm_num : (0:ℝ)<31/32) (by norm_num)
  have hpow (r : ℝ) : (middleX L)^r = Real.exp (r*L) := by
    rw [Real.rpow_def_of_pos (middleX_pos L), middle_log_X, mul_comm]
  rw [hpow, hpow] at hh
  have he : middleH L * Real.exp (-3*L) / (1-Real.exp (-2*L)) =
      middleH L * cellTrivialBudget L := by unfold cellTrivialBudget; ring
  rw [he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (cellTrivialBudget_antitone (by linarith) hAL) (middleH_pos L).le)

theorem middle_prime_of_zero_budget (H : IntegratedExplicitFormula)
    (A C L Z : ℝ) (hA : 167 ≤ A) (hAL : A ≤ L) (hLC : L ≤ C)
    (hZ : ∀ T : ℝ,
      ‖truncatedTrapezoidZeroSum (middleX L) (middleH L) (1/32) (31/32) T‖ ≤ middleH L*Z)
    (hbudget : Z + middlePrimePowerBudget A C + cellTrivialBudget A < 1) :
    ShortInterval6 (middleX L) :=
  middle_prime_of_trapezoid_budgets H A C L Z (cellTrivialBudget A) hA hAL hLC
    hZ (middle_trivial_zero_cell_le A L hA hAL) hbudget

end LegendreK6
