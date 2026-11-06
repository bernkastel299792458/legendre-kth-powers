import LegendreK6.M2PilotExpression
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Reverse log-x comparison for the entire finite-RH lower middle range.
The three rational factors apply to actual exponential grid weights. -/

namespace LegendreK6

theorem sigmaGridWeight_reverse_scaled_le (s : ℕ → ℝ) (A L : ℝ) (j : ℕ)
    (hL : 0 ≤ L) (hLA : L ≤ A) (hs : s j ≤ s (j+1)) :
    Real.exp ((L-A)/6)*sigmaGridWeight s L j ≤
      Real.exp ((5/6-s j)*(A-L))*sigmaGridWeight s A j := by
  have hint (X : ℝ) : IntervalIntegrable
      (fun v : ℝ => X*Real.exp ((v-1)*X)) MeasureTheory.volume (s j) (s (j+1)) :=
    (continuous_const.mul
      (Real.continuous_exp.comp ((continuous_id.sub continuous_const).mul continuous_const))).intervalIntegrable _ _
  unfold sigmaGridWeight
  rw [← exact_sigma_weight L, ← exact_sigma_weight A,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hs ((hint L).const_mul _) ((hint A).const_mul _)
  intro v hv
  have he : Real.exp ((L-A)/6 + (v-1)*L) ≤
      Real.exp ((5/6-s j)*(A-L) + (v-1)*A) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hv.1) (sub_nonneg.mpr hLA)]
  calc
    _ = L*Real.exp ((L-A)/6 + (v-1)*L) := by rw [Real.exp_add]; ring
    _ ≤ A*Real.exp ((5/6-s j)*(A-L) + (v-1)*A) :=
      mul_le_mul hLA he (Real.exp_nonneg _) (by linarith)
    _ = _ := by rw [Real.exp_add]; ring

namespace M3Lower

def multiplierNat (j : ℕ) : ℕ := if j < 1229 then 128 else if j < 1366 then 3 else 2

noncomputable def multiplier (j : Fin 1536) : ℝ := (multiplierNat j.val : ℝ)/2

theorem multiplier_nonneg (j : Fin 1536) : 0 ≤ multiplier j := by
  unfold multiplier
  positivity

theorem multiplier_le_64 (j : Fin 1536) : multiplier j ≤ 64 := by
  unfold multiplier multiplierNat
  split_ifs <;> norm_num

private theorem exp_large_cap : Real.exp (((47/12 : ℚ) : ℝ)) ≤ 64 := by
  dyadic_interval [prec := 64]

private theorem exp_small_cap : Real.exp (((47/120 : ℚ) : ℝ)) ≤ (3/2 : ℝ) := by
  have h : Real.exp (((47/120 : ℚ) : ℝ)) ≤ (((3/2 : ℚ) : ℝ)) := by
    dyadic_interval [prec := 64]
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
  exact h

theorem reverse_exponential_factor_le (L : ℝ) (hL : 167 ≤ L)
    (hLA : L ≤ M2Pilot.left) (j : Fin 1536) :
    Real.exp ((5/6-M2Pilot.s j.val)*(M2Pilot.left-L)) ≤ multiplier j := by
  have hd0 : 0 ≤ M2Pilot.left-L := by linarith
  have hd : M2Pilot.left-L ≤ 47/4 := by norm_num [M2Pilot.left] at *; linarith
  have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  unfold multiplier multiplierNat
  split_ifs with hj hk
  · norm_num
    apply le_trans _ exp_large_cap
    apply Real.exp_le_exp.mpr
    have hs : (1/2 : ℝ) ≤ M2Pilot.s j.val := by unfold M2Pilot.s; linarith
    norm_num
    nlinarith
  · norm_num
    apply le_trans _ exp_small_cap
    apply Real.exp_le_exp.mpr
    have hj' : (1229 : ℝ) ≤ j.val := by exact_mod_cast (show 1229 ≤ j.val by omega)
    have hs : (4/5 : ℝ) ≤ M2Pilot.s j.val := by unfold M2Pilot.s; linarith
    norm_num
    nlinarith
  · norm_num
    have hj' : (1366 : ℝ) ≤ j.val := by exact_mod_cast (show 1366 ≤ j.val by omega)
    have hs : (5/6 : ℝ) ≤ M2Pilot.s j.val := by unfold M2Pilot.s; linarith
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hd0

theorem scaled_sigma_weight_le (L : ℝ) (hL : 167 ≤ L)
    (hLA : L ≤ M2Pilot.left) (j : Fin 1536) :
    Real.exp ((L-M2Pilot.left)/6)*sigmaGridWeight M2Pilot.s L j.val ≤
      multiplier j*M2Pilot.sigmaWeight j := by
  have hh := sigmaGridWeight_reverse_scaled_le M2Pilot.s M2Pilot.left L j.val
    (by linarith) hLA (M2Pilot.s_monotone (Nat.le_succ _))
  rw [← M2Pilot.sigmaWeight_eq_grid j] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (reverse_exponential_factor_le L hL hLA j)
    (M2Pilot.sigmaWeight_nonneg j))

theorem scaled_baseline_le (L u : ℝ) (hL : 167 ≤ L)
    (hLA : L ≤ M2Pilot.left) (hu : 0 ≤ u) :
    Real.exp ((L-M2Pilot.left)/6)*(Real.exp (-L/2+u)*u) ≤
      64*(Real.exp (-M2Pilot.left/2+u)*u) := by
  have he : Real.exp ((M2Pilot.left-L)/3) ≤ (64 : ℝ) := by
    apply le_trans _ exp_large_cap
    apply Real.exp_le_exp.mpr
    norm_num [M2Pilot.left]
    linarith
  calc
    _ = Real.exp ((M2Pilot.left-L)/3)*(Real.exp (-M2Pilot.left/2+u)*u) := by
      rw [← mul_assoc, ← Real.exp_add, ← mul_assoc, ← Real.exp_add]
      congr 2 <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_right he (by positivity)

end M3Lower
end LegendreK6
