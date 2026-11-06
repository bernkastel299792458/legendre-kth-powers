import Mathlib

/-!
# Analytic and algebraic lemmas proved without a numerical oracle

These are components of the written proof, not a proof of its zeta explicit
formula or the complete zero-density-to-prime bridge. No omitted bridge is
registered as an axiom in this file.
-/

namespace LegendreK6

theorem trapezoid_constants :
    (1 / 32 : ℝ) + 31 / 32 = 1 ∧
    2 / (31 / 32 : ℝ) = 64 / 31 ∧
    4 / ((1 / 32 : ℝ) * (31 / 32)) = 4096 / 31 := by norm_num

theorem four_point_quadratic (x h a b : ℝ) (hab : a + b = 1)
    (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    (x ^ 2 / 2 - (x + a * h) ^ 2 / 2 - (x + b * h) ^ 2 / 2 +
      (x + h) ^ 2 / 2) / (a * b * h) = h := by
  have hbval : b = 1 - a := by linarith
  apply (div_eq_iff (mul_ne_zero (mul_ne_zero ha hb) hh)).2
  rw [hbval]
  ring

theorem four_point_affine (x h a b c d : ℝ) (hab : a + b = 1) :
    (c * x + d) - (c * (x + a * h) + d) -
      (c * (x + b * h) + d) + (c * (x + h) + d) = 0 := by
  have hbval : b = 1 - a := by linarith
  rw [hbval]
  ring

theorem exact_sigma_weight (L s t : ℝ) :
    (∫ v in s..t, L * Real.exp ((v - 1) * L)) =
      Real.exp ((t - 1) * L) - Real.exp ((s - 1) * L) := by
  have hd : ∀ v : ℝ, HasDerivAt (fun w : ℝ => Real.exp ((w - 1) * L))
      (L * Real.exp ((v - 1) * L)) v := by
    intro v
    simpa only [id, one_mul, mul_one, sub_zero, mul_comm] using
      (((hasDerivAt_id v).sub_const 1).mul_const L).exp
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v)
  exact (continuous_const.mul
    (Real.continuous_exp.comp ((continuous_id.sub continuous_const).mul continuous_const))).intervalIntegrable _ _

theorem sigma_weight_nonneg {L s t : ℝ} (hL : 0 ≤ L) (hst : s ≤ t) :
    0 ≤ Real.exp ((t - 1) * L) - Real.exp ((s - 1) * L) := by
  apply sub_nonneg.mpr
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (by linarith) hL

theorem log_ratio_bound {U u : ℝ} (hU : 0 < U) (hu : 0 < u) :
    Real.log (u / U) ≤ (u - U) / U := by
  have h := Real.log_le_sub_one_of_pos (div_pos hu hU)
  convert h using 1 <;> field_simp

theorem cs_density_exponent_bound {s : ℝ} (hs : s ≤ 7 / 8) :
    3 / (2 - s) ≤ (8 / 3 : ℝ) := by
  apply (div_le_iff₀ (by linarith : 0 < 2 - s)).2
  linarith

theorem cs_log_exponent_bound {s : ℝ} (hlo : 1 / 2 ≤ s) (hhi : s ≤ 7 / 8) :
    3 * (1 - s) / (2 - s) + 2 ≤ 3 := by
  have hd : 0 < 2 - s := by linarith
  have h : 3 * (1 - s) / (2 - s) ≤ 1 := (div_le_iff₀ hd).2 (by linarith)
  linarith

theorem common_zero_weight {beta a L g h : ℝ} (hb : beta ≤ 1) (ha : a ≤ L)
    (hg : 0 ≤ g) (hgh : g ≤ h) :
    Real.exp ((beta - 1) * L) * g ≤ Real.exp ((beta - 1) * a) * h := by
  have he : Real.exp ((beta - 1) * L) ≤ Real.exp ((beta - 1) * a) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left ha (by linarith)
  exact mul_le_mul he hgh hg (Real.exp_nonneg _)

theorem coefficient_scaling_criterion {D E c : ℝ} (hD : 0 < D) :
    c * D + E < 1 ↔ c < (1 - E) / D := by
  rw [lt_div_iff₀ hD]
  constructor <;> intro h <;> linarith

theorem conservative_scaling {D E c : ℝ} (hE : 0 ≤ E) (hc : 1 ≤ c) :
    c * D + E ≤ c * (D + E) := by
  have h := mul_nonneg (sub_nonneg.mpr hc) hE
  nlinarith

end LegendreK6
