import LegendreK6.TailArithmetic

/-!
# Domains of the actual tail parameters

Here `tailHeight` is the actual height `2*T`. The previously defined `tailU`
is its logarithm. All statements in this file hold throughout `L >= 700`.
-/

namespace LegendreK6

noncomputable def tailX (L : ℝ) : ℝ := Real.exp L
noncomputable def tailH (L : ℝ) : ℝ := 4 * Real.exp (3 * L / 4)
noncomputable def tailY (L : ℝ) : ℝ := tailX L + tailH L
noncomputable def tailT (L : ℝ) : ℝ := Real.exp (9 * L / 32)
noncomputable def tailHeight (L : ℝ) : ℝ := 2 * tailT L

theorem tailX_pos (L : ℝ) : 0 < tailX L := Real.exp_pos _
theorem tailH_pos (L : ℝ) : 0 < tailH L := by unfold tailH; positivity
theorem tailT_pos (L : ℝ) : 0 < tailT L := Real.exp_pos _
theorem tailY_pos (L : ℝ) : 0 < tailY L := add_pos (tailX_pos L) (tailH_pos L)

theorem tail_log_X (L : ℝ) : Real.log (tailX L) = L := Real.log_exp L

theorem tailH_eq_rpow (L : ℝ) : tailH L = 4 * (tailX L) ^ ((3 : ℝ) / 4) := by
  rw [Real.rpow_def_of_pos (tailX_pos L), tail_log_X]
  unfold tailH
  congr 2
  ring

theorem tailT_eq_rpow (L : ℝ) : tailT L = (tailX L) ^ ((9 : ℝ) / 32) := by
  rw [Real.rpow_def_of_pos (tailX_pos L), tail_log_X]
  unfold tailT
  congr 1
  ring

theorem tail_sqrt_X (L : ℝ) : Real.sqrt (tailX L) = Real.exp (L / 2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (tailX_pos L), tail_log_X]
  congr 1
  ring

theorem tail_log_height (L : ℝ) : Real.log (tailHeight L) = tailU L := by
  unfold tailHeight tailT tailU
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp]
  ring

theorem tail_X_ge_one (L : ℝ) (hL : 700 ≤ L) : 1 ≤ tailX L :=
  Real.one_le_exp (by linarith)

theorem tail_Y_ge_one (L : ℝ) (hL : 700 ≤ L) : 1 ≤ tailY L := by
  have hx := tail_X_ge_one L hL
  have hh := tailH_pos L
  unfold tailY
  linarith

theorem tail_X_lt_Y (L : ℝ) : tailX L < tailY L := by
  unfold tailY
  exact lt_add_of_pos_right _ (tailH_pos L)

theorem tail_T_gt_51 (L : ℝ) (hL : 700 ≤ L) : 51 < tailT L := by
  have h := Real.add_one_le_exp (9 * L / 32)
  unfold tailT
  linarith

theorem tail_log_sq_lt_T (L : ℝ) (hL : 700 ≤ L) : L ^ 2 < tailT L := by
  have he := Real.pow_div_factorial_le_exp (9 * L / 32)
    (show 0 ≤ 9 * L / 32 by linarith) 3
  norm_num at he
  have hcube := mul_nonneg (sq_nonneg L) (sub_nonneg.mpr hL)
  have hs : 0 < L ^ 2 := sq_pos_of_pos (by linarith)
  unfold tailT
  nlinarith

theorem tail_T_lt_truncation_limit (L : ℝ) (hL : 700 ≤ L) :
    tailT L < (Real.exp (L / 2) - 2) / 4 := by
  have ht := tail_T_gt_51 L hL
  have he := Real.add_one_le_exp (7 * L / 32)
  have he6 : 6 < Real.exp (7 * L / 32) := by linarith
  have hprod : Real.exp (L / 2) = tailT L * Real.exp (7 * L / 32) := by
    unfold tailT
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hprod]
  nlinarith

theorem tail_T_lt_sqrt_limit (L : ℝ) (hL : 700 ≤ L) :
    tailT L < (Real.sqrt (tailX L) - 2) / 4 := by
  rw [tail_sqrt_X]
  exact tail_T_lt_truncation_limit L hL

theorem tail_T_ge_RH (L : ℝ) (hL : 700 ≤ L) :
    (3000000000000 : ℝ) ≤ tailT L := by
  have hb := Real.pow_div_factorial_le_exp 100 (show (0 : ℝ) ≤ 100 by norm_num) 10
  norm_num at hb
  have hm : Real.exp 100 ≤ tailT L := Real.exp_le_exp.mpr (by linarith)
  linarith

theorem tail_height_ge_RH (L : ℝ) (hL : 700 ≤ L) :
    (3000000000000 : ℝ) ≤ tailHeight L := by
  have hm := tail_T_ge_RH L hL
  unfold tailHeight
  linarith

theorem tail_U_gt_one (L : ℝ) (hL : 700 ≤ L) : 1 < tailU L := by
  have hlog := log_two_bounds.1
  unfold tailU
  linarith

theorem tail_lambda_pos (L : ℝ) (hL : 700 ≤ L) : 0 < tailLambda L := by
  have hlog := log_two_bounds.2
  unfold tailLambda
  linarith

theorem tail_H_le_X (L : ℝ) (hL : 700 ≤ L) : tailH L ≤ tailX L := by
  have hq := Real.add_one_le_exp (L / 4)
  have hq4 : (4 : ℝ) ≤ Real.exp (L / 4) := by linarith
  have he : Real.exp L = Real.exp (3 * L / 4) * Real.exp (L / 4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold tailH tailX
  rw [he, mul_comm (4 : ℝ)]
  exact mul_le_mul_of_nonneg_left hq4 (Real.exp_nonneg _)

theorem tail_Y_le_two_X (L : ℝ) (hL : 700 ≤ L) : tailY L ≤ 2 * tailX L := by
  have h := tail_H_le_X L hL
  unfold tailY
  linarith

theorem tail_log_Y_le (L : ℝ) (hL : 700 ≤ L) : Real.log (tailY L) ≤ L + 1 := by
  have hm := Real.log_le_log (tailY_pos L) (tail_Y_le_two_X L hL)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt (tailX_pos L)),
    tail_log_X] at hm
  have hlog := log_two_bounds.2
  linarith

theorem tail_log_Y_ge (L : ℝ) : L ≤ Real.log (tailY L) := by
  calc
    L = Real.log (tailX L) := (tail_log_X L).symm
    _ ≤ Real.log (tailY L) := Real.log_le_log (tailX_pos L) (tail_X_lt_Y L).le

theorem tail_sqrt_Y_le (L : ℝ) (hL : 700 ≤ L) :
    Real.sqrt (tailY L) ≤ 2 * Real.sqrt (tailX L) := by
  have hy := tail_Y_le_two_X L hL
  have hx0 := (tailX_pos L).le
  have hx := Real.sq_sqrt hx0
  have hy2 := Real.sq_sqrt (tailY_pos L).le
  have hsx := Real.sqrt_nonneg (tailX L)
  have hsy := Real.sqrt_nonneg (tailY L)
  nlinarith

theorem tail_log_Y_budget_domain (L : ℝ) (hL : 700 ≤ L) :
    4 * Real.log 2 ≤ Real.log (tailY L) := by
  have hy := tail_log_Y_ge L
  have hlog := log_two_bounds.2
  linarith

end LegendreK6
