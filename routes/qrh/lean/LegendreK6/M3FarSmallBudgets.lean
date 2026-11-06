import LegendreK6.M3FarBudgetDefinitions
import LegendreK6.M3FarConstants

/-! Deliberately loose, kernel-checked bounds for the pilot's two tiny budgets. -/

namespace LegendreK6.M3Far

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem exp_neg_fifty_small : Real.exp (-50) ≤ (0.000000000001 : ℝ) := by
  dyadic_interval [prec := 64]

private theorem log_two_ge_half : (1 / 2 : ℝ) ≤ Real.log 2 := by
  apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 2)).2
  have h : Real.exp (((1 / 2 : ℚ) : ℝ)) ≤ 2 := by dyadic_interval [prec := 64]
  norm_num at h
  exact h

theorem prime_power_budget_small :
    farPrimePowerBudget left right ≤ (1 / 1000000 : ℝ) := by
  let e := farEpsilon left
  have he0 : 0 ≤ e := (farEpsilon_pos left).le
  have he1 : e ≤ 1 := by
    have hn : 4 * Real.exp (-2) ≤ (1 : ℝ) := by dyadic_interval [prec := 64]
    have hm : Real.exp (-left / 4) ≤ Real.exp (-2) := by
      apply Real.exp_le_exp.mpr
      norm_num [left]
    dsimp [e, farEpsilon]
    linarith
  have hs0 := Real.sqrt_nonneg (1 + e)
  have hs2 : Real.sqrt (1 + e) ≤ 2 := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 + e by linarith)
    nlinarith
  have hl0 : 0 ≤ Real.log (1 + e) := Real.log_nonneg (by linarith)
  have hl1 : Real.log (1 + e) ≤ 1 := by
    have hl := Real.log_le_sub_one_of_pos (show 0 < 1 + e by linarith)
    linarith
  have hnum : (32 / 31 : ℝ) * Real.sqrt (1 + e) * ((1601/4) + Real.log (1 + e)) ^ 2 ≤
      646416 := by
    calc
      _ ≤ 2 * 2 * 402 ^ 2 :=
        mul_le_mul (mul_le_mul (by norm_num) hs2 hs0 (by norm_num))
          (pow_le_pow_left₀ (by linarith) (by linarith) 2) (sq_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hd : 4 ≤ 8 * Real.log 2 := by linarith [log_two_ge_half]
  have hd0 : 0 < 8 * Real.log 2 := by linarith
  have hquot : (32 / 31 : ℝ) * Real.sqrt (1 + e) *
      ((1601/4) + Real.log (1 + e)) ^ 2 / (8 * Real.log 2) ≤ 161604 := by
    apply (div_le_iff₀ hd0).mpr
    nlinarith
  have hexp : Real.exp (-left / 4) ≤ (0.000000000001 : ℝ) := by
    apply le_trans _ exp_neg_fifty_small
    apply Real.exp_le_exp.mpr
    norm_num [left]
  change (32 / 31 : ℝ) * Real.sqrt (1 + e) * ((1601/4) + Real.log (1 + e)) ^ 2 /
    (8 * Real.log 2) * Real.exp (-left / 4) ≤ (1 / 1000000 : ℝ)
  have hp := mul_le_mul_of_nonneg_right hquot (Real.exp_nonneg (-left / 4))
  nlinarith

theorem trivial_budget_small : cellTrivialBudget left ≤ (1 / 1000000 : ℝ) := by
  have hnum : Real.exp (-3 * left) ≤ (0.000000000001 : ℝ) := by
    apply le_trans _ exp_neg_fifty_small
    apply Real.exp_le_exp.mpr
    norm_num [left]
  have hden : (1 / 2 : ℝ) ≤ 1 - Real.exp (-2 * left) := by
    have hm : Real.exp (-2 * left) ≤ Real.exp (-2) := by
      apply Real.exp_le_exp.mpr
      norm_num [left]
    have hb : Real.exp (-2) ≤ (0.5 : ℝ) := by dyadic_interval [prec := 64]
    linarith
  unfold cellTrivialBudget
  apply (div_le_iff₀ (by linarith : 0 < 1 - Real.exp (-2 * left))).mpr
  nlinarith

end LegendreK6.M3Far
