import LegendreK6.IntegratedPsi
import LegendreK6.PrimePowerBudget

/-!
# Actual sixth-power middle parameters and the cell prime-power budget

The budget is exactly equation (20) of the manuscript. Its upper bound is
proved for every real parameter in a closed cell, not just for the endpoints.
-/

namespace LegendreK6

noncomputable def middleX (L : ℝ) : ℝ := Real.exp L
noncomputable def middleH (L : ℝ) : ℝ := 6 * Real.exp (5 * L / 6)
noncomputable def middleY (L : ℝ) : ℝ := middleX L + middleH L
noncomputable def middleQ (L : ℝ) : ℝ := middleY L / middleH L
noncomputable def middleEpsilon (A : ℝ) : ℝ := 6 * Real.exp (-A / 6)
noncomputable def middlePrimePowerBudget (A C : ℝ) : ℝ :=
  (32 / 31) * Real.sqrt (1 + middleEpsilon A) *
    (C + Real.log (1 + middleEpsilon A)) ^ 2 / (12 * Real.log 2) * Real.exp (-A / 3)

theorem middleX_pos (L : ℝ) : 0 < middleX L := Real.exp_pos _
theorem middleH_pos (L : ℝ) : 0 < middleH L := by unfold middleH; positivity
theorem middleY_pos (L : ℝ) : 0 < middleY L := add_pos (middleX_pos L) (middleH_pos L)
theorem middleEpsilon_pos (L : ℝ) : 0 < middleEpsilon L := by unfold middleEpsilon; positivity

theorem middle_log_X (L : ℝ) : Real.log (middleX L) = L := Real.log_exp L

theorem middleH_eq_rpow (L : ℝ) : middleH L = 6 * (middleX L) ^ ((5 : ℝ) / 6) := by
  rw [Real.rpow_def_of_pos (middleX_pos L), middle_log_X]
  unfold middleH
  congr 2
  ring

theorem middle_X_lt_Y (L : ℝ) : middleX L < middleY L := by
  unfold middleY
  exact lt_add_of_pos_right _ (middleH_pos L)

theorem middle_X_gt_one (L : ℝ) (hL : 167 ≤ L) : 1 < middleX L :=
  Real.one_lt_exp_iff.mpr (by linarith)

theorem middle_Y_ge_one (L : ℝ) (hL : 167 ≤ L) : 1 ≤ middleY L :=
  (middle_X_gt_one L hL).le.trans (middle_X_lt_Y L).le

theorem middle_Y_factor (L : ℝ) : middleY L = middleX L * (1 + middleEpsilon L) := by
  have he : Real.exp L * Real.exp (-L / 6) = Real.exp (5 * L / 6) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold middleY middleX middleH middleEpsilon
  rw [← he]
  ring

theorem middle_sqrt_X (L : ℝ) : Real.sqrt (middleX L) = Real.exp (L / 2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (middleX_pos L), middle_log_X]
  congr 1
  ring

theorem middle_sqrt_Y (L : ℝ) :
    Real.sqrt (middleY L) = Real.exp (L / 2) * Real.sqrt (1 + middleEpsilon L) := by
  rw [middle_Y_factor, Real.sqrt_mul (middleX_pos L).le, middle_sqrt_X]

theorem middle_log_Y (L : ℝ) : Real.log (middleY L) = L + Real.log (1 + middleEpsilon L) := by
  rw [middle_Y_factor, Real.log_mul (middleX_pos L).ne'
    (show 1 + middleEpsilon L ≠ 0 by have h := middleEpsilon_pos L; positivity), middle_log_X]

theorem middle_epsilon_antitone : Antitone middleEpsilon := by
  intro A L hAL
  unfold middleEpsilon
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)

theorem middle_q_eq (L : ℝ) : middleQ L = 1 + Real.exp (L / 6) / 6 := by
  have he : Real.exp L / Real.exp (5 * L / 6) = Real.exp (L / 6) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  unfold middleQ middleY
  rw [add_div, div_self (middleH_pos L).ne']
  unfold middleX middleH
  calc
    _ = 1 + (Real.exp L / Real.exp (5 * L / 6)) / 6 := by ring
    _ = _ := by rw [he]

theorem middle_q_cell_le (L C : ℝ) (hLC : L ≤ C) :
    middleQ L ≤ 1 + Real.exp (C / 6) / 6 := by
  rw [middle_q_eq]
  gcongr

theorem middle_log_Y_cell_le (A C L : ℝ) (hAL : A ≤ L) (hLC : L ≤ C) :
    Real.log (middleY L) ≤ C + Real.log (1 + middleEpsilon A) := by
  rw [middle_log_Y]
  have hm := middle_epsilon_antitone hAL
  have hp : 0 < 1 + middleEpsilon L := by have h := middleEpsilon_pos L; positivity
  exact add_le_add hLC (Real.log_le_log hp (by linarith))

theorem middle_log_Y_budget_domain (L : ℝ) (hL : 167 ≤ L) :
    4 * Real.log 2 ≤ Real.log (middleY L) := by
  have hl := Real.log_le_log (middleX_pos L) (middle_X_lt_Y L).le
  rw [middle_log_X] at hl
  have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  linarith

/-- Exact normalized square-root factor before imposing a cell envelope. -/
theorem middle_sqrt_Y_div_H (L : ℝ) :
    Real.sqrt (middleY L) / middleH L =
      Real.sqrt (1 + middleEpsilon L) * Real.exp (-L / 3) / 6 := by
  have he : Real.exp (L / 2) / Real.exp (5 * L / 6) = Real.exp (-L / 3) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [middle_sqrt_Y]
  unfold middleH
  calc
    _ = Real.sqrt (1 + middleEpsilon L) *
        (Real.exp (L / 2) / Real.exp (5 * L / 6)) / 6 := by ring
    _ = _ := by rw [he]

theorem middle_sqrt_Y_div_H_cell_le (A L : ℝ) (hAL : A ≤ L) :
    Real.sqrt (middleY L) / middleH L ≤
      Real.sqrt (1 + middleEpsilon A) * Real.exp (-A / 3) / 6 := by
  rw [middle_sqrt_Y_div_H]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply mul_le_mul
  · exact Real.sqrt_le_sqrt (by linarith [middle_epsilon_antitone hAL])
  · exact Real.exp_le_exp.mpr (by linarith)
  · exact Real.exp_nonneg _
  · exact Real.sqrt_nonneg _

/-- The true normalized nonprime contribution is bounded by the exact paper
cell budget for every L in the cell. No saved certificate value is imported. -/
theorem middle_prime_power_normalized_le (A C L : ℝ)
    (hA : 167 ≤ A) (hAL : A ≤ L) (hLC : L ≤ C) :
    weightedNonprime (Finset.Ioc 0 ⌊middleY L⌋₊)
        (fun m => trapezoidWeight (middleX L) (middleH L) (1 / 32) (31 / 32) (m : ℝ)) /
        middleH L ≤ middlePrimePowerBudget A C := by
  have hL : 167 ≤ L := hA.trans hAL
  have hW : ∀ m ∈ Finset.Ioc 0 ⌊middleY L⌋₊,
      trapezoidWeight (middleX L) (middleH L) (1 / 32) (31 / 32) (m : ℝ) ≤ (32 / 31 : ℝ) := by
    intro m _
    have hb := (trapezoidWeight_bounds (middleX L) (middleH L) (1 / 32) (31 / 32)
      (m : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (middleH_pos L)).2
    norm_num at hb
    exact hb
  have hraw := weightedNonprime_le_manuscript_budget (Finset.Ioc 0 ⌊middleY L⌋₊)
    (fun m => trapezoidWeight (middleX L) (middleH L) (1 / 32) (31 / 32) (m : ℝ))
    (middleY L) (32 / 31) (middle_Y_ge_one L hL) (by norm_num)
    (middle_log_Y_budget_domain L hL) (fun _ h => h) hW
  have hsqrt := middle_sqrt_Y_div_H_cell_le A L hAL
  have hlog0 : 0 ≤ Real.log (middleY L) := Real.log_nonneg (middle_Y_ge_one L hL)
  have hlog := middle_log_Y_cell_le A C L hAL hLC
  have hlog2 : (Real.log (middleY L)) ^ 2 ≤
      (C + Real.log (1 + middleEpsilon A)) ^ 2 := by
    nlinarith
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsqrt0 : 0 ≤ Real.sqrt (middleY L) / middleH L :=
    div_nonneg (Real.sqrt_nonneg _) (middleH_pos L).le
  calc
    _ ≤ ((32 / 31 : ℝ) * Real.sqrt (middleY L) * (Real.log (middleY L)) ^ 2 /
        (2 * Real.log 2)) / middleH L := div_le_div_of_nonneg_right hraw (middleH_pos L).le
    _ = ((32 / 31 : ℝ) / (2 * Real.log 2)) *
        (Real.sqrt (middleY L) / middleH L) * (Real.log (middleY L)) ^ 2 := by ring
    _ ≤ ((32 / 31 : ℝ) / (2 * Real.log 2)) *
        (Real.sqrt (1 + middleEpsilon A) * Real.exp (-A / 3) / 6) *
        (C + Real.log (1 + middleEpsilon A)) ^ 2 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrt (by positivity)) hlog2
        (sq_nonneg _) (by positivity)
    _ = middlePrimePowerBudget A C := by unfold middlePrimePowerBudget; ring

theorem middle_prime_power_le (A C L : ℝ)
    (hA : 167 ≤ A) (hAL : A ≤ L) (hLC : L ≤ C) :
    weightedNonprime (Finset.Ioc 0 ⌊middleY L⌋₊)
        (fun m => trapezoidWeight (middleX L) (middleH L) (1 / 32) (31 / 32) (m : ℝ)) ≤
      middleH L * middlePrimePowerBudget A C := by
  have h := (div_le_iff₀ (middleH_pos L)).mp (middle_prime_power_normalized_le A C L hA hAL hLC)
  simpa only [mul_comm] using h

end LegendreK6
