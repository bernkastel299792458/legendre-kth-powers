import LegendreK6.M2PilotConstants
import LegendreK6.TrapezoidCell

/-! Uniform elementary bounds on the entire lower-middle interval.
All ground exponential estimates below are checked by Lean's interval tactic. -/

namespace LegendreK6.M3Lower

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def scaling (L : ℝ) : ℝ := Real.exp ((L-M2Pilot.left)/6)

theorem scaling_pos (L : ℝ) : 0 < scaling L := Real.exp_pos _
theorem scaling_nonneg (L : ℝ) : 0 ≤ scaling L := (scaling_pos L).le

theorem scaling_le_one (L : ℝ) (hL : L ≤ M2Pilot.left) : scaling L ≤ 1 := by
  exact Real.exp_le_one_iff.mpr (by linarith)

theorem middleQ_eq_scaling (L : ℝ) :
    middleQ L = scaling L *
      (Real.exp ((M2Pilot.left-L)/6) + Real.exp (M2Pilot.left/6)/6) := by
  have h1 : scaling L * Real.exp ((M2Pilot.left-L)/6) = 1 := by
    unfold scaling
    rw [← Real.exp_add, show (L-M2Pilot.left)/6+(M2Pilot.left-L)/6 = 0 by ring,
      Real.exp_zero]
  have h2 : scaling L * Real.exp (M2Pilot.left/6) = Real.exp (L/6) := by
    unfold scaling
    rw [← Real.exp_add]
    congr 1
    ring
  rw [mul_add, ← mul_div_assoc, h1, h2, middle_q_eq]

theorem middleQ_le_scaling_cap (L : ℝ) (hL : 167 ≤ L) :
    middleQ L ≤ scaling L *
      (Real.exp (47/24) + Real.exp (M2Pilot.left/6)/6) := by
  rw [middleQ_eq_scaling]
  apply mul_le_mul_of_nonneg_left _ (scaling_nonneg L)
  apply add_le_add _ le_rfl
  apply Real.exp_le_exp.mpr
  norm_num [M2Pilot.left]
  linarith

private theorem cap_le_reference :
    Real.exp (47/24) + Real.exp (M2Pilot.left/6)/6 ≤ M2Pilot.q := by
  have h : Real.exp (((47/24 : ℚ) : ℝ)) +
      (((1/6 : ℚ) : ℝ))*Real.exp (((715/24 : ℚ) : ℝ)) ≤
      1 + (((1/6 : ℚ) : ℝ))*Real.exp (((179/6 : ℚ) : ℝ)) := by
    dyadic_interval [prec := 64]
  norm_num [M2Pilot.q, M2Pilot.left, M2Pilot.right] at *
  convert h using 1 <;> ring

private theorem cap_le_linear_threshold :
    Real.exp (47/24) + Real.exp (M2Pilot.left/6)/6 ≤
      (3000000000000 : ℝ) / (64/31) := by
  have h : Real.exp (((47/24 : ℚ) : ℝ)) +
      (((1/6 : ℚ) : ℝ))*Real.exp (((715/24 : ℚ) : ℝ)) ≤
      (1453125000000 : ℝ) := by
    dyadic_interval [prec := 64]
  norm_num [M2Pilot.left] at *
  convert h using 1; ring

theorem middleQ_le_scaling_q (L : ℝ) (hL : 167 ≤ L) :
    middleQ L ≤ scaling L*M2Pilot.q :=
  (middleQ_le_scaling_cap L hL).trans
    (mul_le_mul_of_nonneg_left cap_le_reference (scaling_nonneg L))

theorem middleQ_linear_le_scaling (L : ℝ) (hL : 167 ≤ L) :
    (64/31 : ℝ)*middleQ L/3000000000000 ≤ scaling L := by
  have hc := (middleQ_le_scaling_cap L hL).trans
    (mul_le_mul_of_nonneg_left cap_le_linear_threshold (scaling_nonneg L))
  linarith

private theorem exp_neg_fifty_small : Real.exp (-50) ≤ (0.00000000001 : ℝ) := by
  dyadic_interval [prec := 64]

theorem low_zero_budget_small (L : ℝ) (hL : 167 ≤ L) :
    2*Real.exp (-L/2)*3000000000000*Real.log 3000000000000 ≤
      (1/1000000 : ℝ) := by
  have he : Real.exp (-L/2) ≤ Real.exp (-80) := Real.exp_le_exp.mpr (by linarith)
  have hl : Real.log (3000000000000 : ℝ) ≤ 3000000000000 :=
    (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have hn : 2*(3000000000000 : ℝ)^2*Real.exp (-80) ≤
      (((1/1000000 : ℚ) : ℝ)) := by
    dyadic_interval [prec := 160]
  norm_num at hn
  have hp1 := mul_le_mul_of_nonneg_left he (show (0:ℝ) ≤ 2*3000000000000^2 by norm_num)
  have hp2 := mul_le_mul_of_nonneg_left hl
    (show 0 ≤ 2*Real.exp (-L/2)*3000000000000 by positivity)
  nlinarith only [hn, hp1, hp2]

private theorem log_two_ge_half : (1/2 : ℝ) ≤ Real.log 2 := by
  apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 2)).2
  have h : Real.exp (((1/2 : ℚ) : ℝ)) ≤ 2 := by dyadic_interval [prec := 64]
  norm_num at h
  exact h

theorem prime_power_budget_small (L : ℝ) (hlo : 167 ≤ L) (hhi : L ≤ M2Pilot.left) :
    middlePrimePowerBudget L L ≤ (1/1000000 : ℝ) := by
  let e := middleEpsilon L
  have he0 : 0 ≤ e := (middleEpsilon_pos L).le
  have he1 : e ≤ 1 := by
    have hn : 6*Real.exp (-2) ≤ (1 : ℝ) := by dyadic_interval [prec := 64]
    have hm : Real.exp (-L/6) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
    dsimp [e, middleEpsilon]
    linarith
  have hs0 := Real.sqrt_nonneg (1+e)
  have hs2 : Real.sqrt (1+e) ≤ 2 := by
    have hs := Real.sq_sqrt (show 0 ≤ 1+e by linarith)
    nlinarith
  have hl0 : 0 ≤ Real.log (1+e) := Real.log_nonneg (by linarith)
  have hl1 : Real.log (1+e) ≤ 1 := by
    have hl := Real.log_le_sub_one_of_pos (show 0 < 1+e by linarith)
    linarith
  have h179 : L ≤ 179 := by norm_num [M2Pilot.left] at hhi; linarith
  have hnum : (32/31 : ℝ)*Real.sqrt (1+e)*(L+Real.log (1+e))^2 ≤ 129600 := by
    calc
      _ ≤ 2*2*180^2 := mul_le_mul
        (mul_le_mul (by norm_num) hs2 hs0 (by norm_num))
        (pow_le_pow_left₀ (by linarith) (by linarith) 2) (sq_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hd : 6 ≤ 12*Real.log 2 := by linarith [log_two_ge_half]
  have hd0 : 0 < 12*Real.log 2 := by linarith
  have hquot : (32/31 : ℝ)*Real.sqrt (1+e)*(L+Real.log (1+e))^2 /
      (12*Real.log 2) ≤ 21600 := by
    apply (div_le_iff₀ hd0).mpr
    nlinarith
  have hexp : Real.exp (-L/3) ≤ (0.00000000001 : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith : -L/3 ≤ -50)).trans exp_neg_fifty_small
  change (32/31 : ℝ)*Real.sqrt (1+e)*(L+Real.log (1+e))^2 /
    (12*Real.log 2)*Real.exp (-L/3) ≤ (1/1000000 : ℝ)
  have hp := mul_le_mul_of_nonneg_right hquot (Real.exp_nonneg (-L/3))
  nlinarith

theorem trivial_budget_small (L : ℝ) (hL : 167 ≤ L) :
    cellTrivialBudget L ≤ (1/1000000 : ℝ) := by
  have hnum : Real.exp (-3*L) ≤ (0.00000000001 : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith : -3*L ≤ -50)).trans exp_neg_fifty_small
  have hden : (1/2 : ℝ) ≤ 1-Real.exp (-2*L) := by
    have hm : Real.exp (-2*L) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
    have hb : Real.exp (-2) ≤ (0.5 : ℝ) := by dyadic_interval [prec := 64]
    linarith
  unfold cellTrivialBudget
  apply (div_le_iff₀ (by linarith : 0 < 1-Real.exp (-2*L))).mpr
  nlinarith

end LegendreK6.M3Lower
