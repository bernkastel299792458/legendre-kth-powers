import LegendreK6.M3FarExpression

/-! A kernel-checked upper bound for all auxiliary density terms of the pilot.
The two grid sums telescope; only the final scalar exponentials are enclosed
by rational dyadic intervals. No numerical-program status is assumed. -/

namespace LegendreK6.M3Far

open scoped BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem csB2_aux_bounds (j : Fin 12) : 0 ≤ csB2 j ∧ csB2 j ≤ 10 := by
  fin_cases j <;> norm_num [csB2]

theorem csB3_aux_bounds (j : Fin 12) : 0 ≤ csB3 j ∧ csB3 j ≤ 168 := by
  fin_cases j <;> norm_num [csB3]

theorem sum_sigmaWeight :
    (∑ j : Fin 384, sigmaWeight j) = Real.exp (-left / 8) - Real.exp (-left / 2) := by
  simp_rw [sigmaWeight, sigmaLo_eq_s, sigmaHi_eq_s_succ]
  rw [Fin.sum_univ_eq_sum_range
    (fun j => Real.exp ((s (j + 1) - 1) * left) - Real.exp ((s j - 1) * left)),
    Finset.sum_range_sub (fun j => Real.exp ((s j - 1) * left))]
  rw [s_zero, s_end]
  congr 2 <;> ring

theorem sum_sigmaWeight_le :
    (∑ j : Fin 384, sigmaWeight j) ≤ Real.exp (-left / 8) := by
  rw [sum_sigmaWeight]
  exact sub_le_self _ (Real.exp_nonneg _)

theorem densityD_nonneg : 0 ≤ densityD := by
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (csB2_aux_bounds (row j)).1 (sigmaWeight_nonneg j)

theorem densityE_nonneg : 0 ≤ densityE := by
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (csB3_aux_bounds (row j)).1 (sigmaWeight_nonneg j)

theorem densityD_le : densityD ≤ 10 * Real.exp (-left / 8) := by
  calc
    densityD ≤ ∑ j : Fin 384, 10 * sigmaWeight j :=
      Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (csB2_aux_bounds (row j)).2 (sigmaWeight_nonneg j)
    _ = 10 * ∑ j : Fin 384, sigmaWeight j := (Finset.mul_sum _ _ _).symm
    _ ≤ 10 * Real.exp (-left / 8) :=
      mul_le_mul_of_nonneg_left sum_sigmaWeight_le (by norm_num)

theorem densityE_le : densityE ≤ 168 * Real.exp (-left / 8) := by
  calc
    densityE ≤ ∑ j : Fin 384, 168 * sigmaWeight j :=
      Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (csB3_aux_bounds (row j)).2 (sigmaWeight_nonneg j)
    _ = 168 * ∑ j : Fin 384, sigmaWeight j := (Finset.mul_sum _ _ _).symm
    _ ≤ 168 * Real.exp (-left / 8) :=
      mul_le_mul_of_nonneg_left sum_sigmaWeight_le (by norm_num)

theorem sum_heightMass :
    (∑ i : Fin 125, heightMass i) = 1 - logKernel U := by
  simp_rw [heightMass_eq_node]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => logKernel (node i) - logKernel (node (i + 1))), Finset.sum_range_sub']
  rw [node_start, node_end, start_logKernel_eq_one]

theorem logKernel_nonneg (u : ℝ) : 0 ≤ logKernel u := by
  unfold logKernel zKernel
  apply le_min (by norm_num)
  apply le_min
  · exact mul_nonneg (by norm_num) (heightZ_nonneg u)
  · exact mul_nonneg (by norm_num) (sq_nonneg _)

theorem sum_heightMass_le_one : (∑ i : Fin 125, heightMass i) ≤ 1 := by
  rw [sum_heightMass]
  exact sub_le_self _ (logKernel_nonneg U)

theorem end_heightCoefficient_extra_le_one :
    32 * (4096 / 31 : ℝ) * (heightZ U) ^ 2 * U ^ 2 ≤ 1 := by
  have h : (32 : ℝ) * (((4096 / 31 : ℚ) : ℝ)) *
      (Real.exp (((-115 : ℚ) : ℝ)) +
        (((1 / 4 : ℚ) : ℝ)) * Real.exp (((-239 / 16 : ℚ) : ℝ))) ^ 2 *
      (((115 : ℚ) : ℝ)) ^ 2 ≤ 1 := by
    dyadic_interval [prec := 64]
  norm_num [heightZ, U, right] at *
  convert h using 1; ring

theorem sum_heightCoefficient_le : (∑ i : Fin 125, heightCoefficient i) ≤ 30000 := by
  have hsq (i : Fin 125) : 2 * height i ^ 2 ≤ 26450 := by
    obtain ⟨hlo, hhi⟩ := height_bounds i
    have hp := height_pos i
    have hle : height i ≤ (115 : ℝ) := by linarith
    nlinarith [mul_self_le_mul_self hp.le hle]
  have hfinite : (∑ i : Fin 125, 2 * height i ^ 2 * heightMass i) ≤ 26450 := by
    calc
      _ ≤ ∑ i : Fin 125, 26450 * heightMass i := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (hsq i) (heightMass_nonneg i)
      _ = 26450 * ∑ i : Fin 125, heightMass i := (Finset.mul_sum _ _ _).symm
      _ ≤ 26450 * 1 := mul_le_mul_of_nonneg_left sum_heightMass_le_one (by norm_num)
      _ = 26450 := by ring
  have hextra :
      (∑ i : Fin 125, if i.val = 124 then
        32 * (4096 / 31 : ℝ) * (heightZ (height i)) ^ 2 * (height i) ^ 2 else 0) ≤ 1 := by
    have heq (i : Fin 125) : (i.val = 124) ↔ i = (124 : Fin 125) := by
      simpa using (Fin.ext_iff (a := i) (b := (124 : Fin 125))).symm
    simp_rw [heq]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, height_last]
    exact end_heightCoefficient_extra_le_one
  unfold heightCoefficient
  rw [Finset.sum_add_distrib]
  linarith

theorem auxiliary_term_le (i : Fin 125) :
    densityD + densityE / height i + Real.exp (-left / 2 + height i) / height i ≤
      16 * Real.exp (-left / 8) + Real.exp (-left / 2 + U) / 28 := by
  have h28 : (28 : ℝ) ≤ height i := by have := (height_bounds i).1; linarith
  have hU : height i ≤ U := (height_bounds i).2
  have hE : densityE / height i ≤ 6 * Real.exp (-left / 8) := by
    calc
      _ ≤ (168 * Real.exp (-left / 8)) / height i :=
        div_le_div_of_nonneg_right densityE_le (height_pos i).le
      _ ≤ (168 * Real.exp (-left / 8)) / 28 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) h28
      _ = 6 * Real.exp (-left / 8) := by ring
  have hx : Real.exp (-left / 2 + height i) / height i ≤
      Real.exp (-left / 2 + U) / 28 := by
    calc
      _ ≤ Real.exp (-left / 2 + U) / height i :=
        div_le_div_of_nonneg_right
          (Real.exp_le_exp.mpr (by linarith only [hU])) (height_pos i).le
      _ ≤ Real.exp (-left / 2 + U) / 28 :=
        div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num) h28
  linarith [densityD_le]

theorem auxiliaryBudget_le_conservative :
    auxiliaryBudget ≤
      30000 * (16 * Real.exp (-left / 8) + Real.exp (-left / 2 + U) / 28) := by
  let B := 16 * Real.exp (-left / 8) + Real.exp (-left / 2 + U) / 28
  have hB : 0 ≤ B := by dsimp [B]; positivity
  calc
    auxiliaryBudget ≤ ∑ i : Fin 125, heightCoefficient i * B :=
      Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (auxiliary_term_le i) (heightCoefficient_nonneg i)
    _ = (∑ i : Fin 125, heightCoefficient i) * B := (Finset.sum_mul _ _ _).symm
    _ ≤ 30000 * B := mul_le_mul_of_nonneg_right sum_heightCoefficient_le hB

theorem auxiliary_scalar_le_small :
    30000 * (16 * Real.exp (-left / 8) + Real.exp (-left / 2 + U) / 28) ≤
      (1 / 50000 : ℝ) := by
  have h : (30000 : ℝ) * (16 * Real.exp (((-50 : ℚ) : ℝ)) +
      (((1 / 28 : ℚ) : ℝ)) * Real.exp (((-85 : ℚ) : ℝ))) ≤
      (((1 / 50000 : ℚ) : ℝ)) := by
    dyadic_interval [prec := 64]
  norm_num [left, U] at *
  convert h using 1; ring

theorem auxiliaryBudget_le_small : auxiliaryBudget ≤ (1 / 50000 : ℝ) :=
  auxiliaryBudget_le_conservative.trans auxiliary_scalar_le_small

end LegendreK6.M3Far
