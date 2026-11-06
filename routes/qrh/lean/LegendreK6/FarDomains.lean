import LegendreK6.IntegratedPsi
import LegendreK6.PrimePowerBudget

/-!
# Actual fourth-power far-segment parameters and prime-power budget

The far formalization reuses the proved trapezoid weight with a=1/32 and
b=31/32. It is a new proof of the same far-segment conclusion, not a
line-by-line translation of the historical polynomial-kernel certificate.
All budget inequalities below refer to actual weighted von Mangoldt sums.
-/

namespace LegendreK6

noncomputable def farX (L : ℝ) : ℝ := Real.exp L
noncomputable def farH (L : ℝ) : ℝ := 4 * Real.exp (3 * L / 4)
noncomputable def farY (L : ℝ) : ℝ := farX L + farH L
noncomputable def farQ (L : ℝ) : ℝ := farY L / farH L
noncomputable def farEpsilon (A : ℝ) : ℝ := 4 * Real.exp (-A / 4)
noncomputable def farPrimePowerBudget (A C : ℝ) : ℝ :=
  (32 / 31) * Real.sqrt (1 + farEpsilon A) *
    (C + Real.log (1 + farEpsilon A)) ^ 2 / (8 * Real.log 2) * Real.exp (-A / 4)

theorem farX_pos (L : ℝ) : 0 < farX L := Real.exp_pos _
theorem farH_pos (L : ℝ) : 0 < farH L := by unfold farH; positivity
theorem farY_pos (L : ℝ) : 0 < farY L := add_pos (farX_pos L) (farH_pos L)
theorem farEpsilon_pos (L : ℝ) : 0 < farEpsilon L := by unfold farEpsilon; positivity

theorem far_log_X (L : ℝ) : Real.log (farX L) = L := Real.log_exp L

theorem farH_eq_rpow (L : ℝ) : farH L = 4 * (farX L) ^ ((3 : ℝ) / 4) := by
  rw [Real.rpow_def_of_pos (farX_pos L), far_log_X]
  unfold farH
  congr 2
  ring

theorem far_X_lt_Y (L : ℝ) : farX L < farY L := by
  unfold farY
  exact lt_add_of_pos_right _ (farH_pos L)

theorem far_X_gt_one (L : ℝ) (hL : 400 ≤ L) : 1 < farX L :=
  Real.one_lt_exp_iff.mpr (by linarith)

theorem far_Y_ge_one (L : ℝ) (hL : 400 ≤ L) : 1 ≤ farY L :=
  (far_X_gt_one L hL).le.trans (far_X_lt_Y L).le

theorem far_Y_factor (L : ℝ) : farY L = farX L * (1 + farEpsilon L) := by
  have he : Real.exp L * Real.exp (-L / 4) = Real.exp (3 * L / 4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold farY farX farH farEpsilon
  rw [← he]
  ring

theorem far_sqrt_X (L : ℝ) : Real.sqrt (farX L) = Real.exp (L / 2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (farX_pos L), far_log_X]
  congr 1
  ring

theorem far_sqrt_Y (L : ℝ) :
    Real.sqrt (farY L) = Real.exp (L / 2) * Real.sqrt (1 + farEpsilon L) := by
  rw [far_Y_factor, Real.sqrt_mul (farX_pos L).le, far_sqrt_X]

theorem far_log_Y (L : ℝ) : Real.log (farY L) = L + Real.log (1 + farEpsilon L) := by
  rw [far_Y_factor, Real.log_mul (farX_pos L).ne'
    (show 1 + farEpsilon L ≠ 0 by have h := farEpsilon_pos L; positivity), far_log_X]

theorem far_epsilon_antitone : Antitone farEpsilon := by
  intro A L hAL
  unfold farEpsilon
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)

theorem far_q_eq (L : ℝ) : farQ L = 1 + Real.exp (L / 4) / 4 := by
  have he : Real.exp L / Real.exp (3 * L / 4) = Real.exp (L / 4) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  unfold farQ farY
  rw [add_div, div_self (farH_pos L).ne']
  unfold farX farH
  calc
    _ = 1 + (Real.exp L / Real.exp (3 * L / 4)) / 4 := by ring
    _ = _ := by rw [he]

theorem far_q_cell_le (L C : ℝ) (hLC : L ≤ C) :
    farQ L ≤ 1 + Real.exp (C / 4) / 4 := by
  rw [far_q_eq]
  gcongr

theorem far_log_Y_cell_le (A C L : ℝ) (hAL : A ≤ L) (hLC : L ≤ C) :
    Real.log (farY L) ≤ C + Real.log (1 + farEpsilon A) := by
  rw [far_log_Y]
  have hm := far_epsilon_antitone hAL
  have hp : 0 < 1 + farEpsilon L := by have h := farEpsilon_pos L; positivity
  exact add_le_add hLC (Real.log_le_log hp (by linarith))

theorem far_log_Y_budget_domain (L : ℝ) (hL : 400 ≤ L) :
    4 * Real.log 2 ≤ Real.log (farY L) := by
  have hl := Real.log_le_log (farX_pos L) (far_X_lt_Y L).le
  rw [far_log_X] at hl
  have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  linarith

/-- Exact normalized square-root factor before imposing a cell envelope. -/
theorem far_sqrt_Y_div_H (L : ℝ) :
    Real.sqrt (farY L) / farH L =
      Real.sqrt (1 + farEpsilon L) * Real.exp (-L / 4) / 4 := by
  have he : Real.exp (L / 2) / Real.exp (3 * L / 4) = Real.exp (-L / 4) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [far_sqrt_Y]
  unfold farH
  calc
    _ = Real.sqrt (1 + farEpsilon L) *
        (Real.exp (L / 2) / Real.exp (3 * L / 4)) / 4 := by ring
    _ = _ := by rw [he]

theorem far_sqrt_Y_div_H_cell_le (A L : ℝ) (hAL : A ≤ L) :
    Real.sqrt (farY L) / farH L ≤
      Real.sqrt (1 + farEpsilon A) * Real.exp (-A / 4) / 4 := by
  rw [far_sqrt_Y_div_H]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply mul_le_mul
  · exact Real.sqrt_le_sqrt (by linarith [far_epsilon_antitone hAL])
  · exact Real.exp_le_exp.mpr (by linarith)
  · exact Real.exp_nonneg _
  · exact Real.sqrt_nonneg _

/-- The true normalized nonprime contribution is bounded by the explicit trapezoid
cell budget for every L in the cell. No saved certificate value is imported. -/
theorem far_prime_power_normalized_le (A C L : ℝ)
    (hA : 400 ≤ A) (hAL : A ≤ L) (hLC : L ≤ C) :
    weightedNonprime (Finset.Ioc 0 ⌊farY L⌋₊)
        (fun m => trapezoidWeight (farX L) (farH L) (1 / 32) (31 / 32) (m : ℝ)) /
        farH L ≤ farPrimePowerBudget A C := by
  have hL : 400 ≤ L := hA.trans hAL
  have hW : ∀ m ∈ Finset.Ioc 0 ⌊farY L⌋₊,
      trapezoidWeight (farX L) (farH L) (1 / 32) (31 / 32) (m : ℝ) ≤ (32 / 31 : ℝ) := by
    intro m _
    have hb := (trapezoidWeight_bounds (farX L) (farH L) (1 / 32) (31 / 32)
      (m : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (farH_pos L)).2
    norm_num at hb
    exact hb
  have hraw := weightedNonprime_le_manuscript_budget (Finset.Ioc 0 ⌊farY L⌋₊)
    (fun m => trapezoidWeight (farX L) (farH L) (1 / 32) (31 / 32) (m : ℝ))
    (farY L) (32 / 31) (far_Y_ge_one L hL) (by norm_num)
    (far_log_Y_budget_domain L hL) (fun _ h => h) hW
  have hsqrt := far_sqrt_Y_div_H_cell_le A L hAL
  have hlog0 : 0 ≤ Real.log (farY L) := Real.log_nonneg (far_Y_ge_one L hL)
  have hlog := far_log_Y_cell_le A C L hAL hLC
  have hlog2 : (Real.log (farY L)) ^ 2 ≤
      (C + Real.log (1 + farEpsilon A)) ^ 2 := by
    nlinarith
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsqrt0 : 0 ≤ Real.sqrt (farY L) / farH L :=
    div_nonneg (Real.sqrt_nonneg _) (farH_pos L).le
  calc
    _ ≤ ((32 / 31 : ℝ) * Real.sqrt (farY L) * (Real.log (farY L)) ^ 2 /
        (2 * Real.log 2)) / farH L := div_le_div_of_nonneg_right hraw (farH_pos L).le
    _ = ((32 / 31 : ℝ) / (2 * Real.log 2)) *
        (Real.sqrt (farY L) / farH L) * (Real.log (farY L)) ^ 2 := by ring
    _ ≤ ((32 / 31 : ℝ) / (2 * Real.log 2)) *
        (Real.sqrt (1 + farEpsilon A) * Real.exp (-A / 4) / 4) *
        (C + Real.log (1 + farEpsilon A)) ^ 2 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrt (by positivity)) hlog2
        (sq_nonneg _) (by positivity)
    _ = farPrimePowerBudget A C := by unfold farPrimePowerBudget; ring

theorem far_prime_power_le (A C L : ℝ)
    (hA : 400 ≤ A) (hAL : A ≤ L) (hLC : L ≤ C) :
    weightedNonprime (Finset.Ioc 0 ⌊farY L⌋₊)
        (fun m => trapezoidWeight (farX L) (farH L) (1 / 32) (31 / 32) (m : ℝ)) ≤
      farH L * farPrimePowerBudget A C := by
  have h := (div_le_iff₀ (farH_pos L)).mp (far_prime_power_normalized_le A C L hA hAL hLC)
  simpa only [mul_comm] using h

end LegendreK6
