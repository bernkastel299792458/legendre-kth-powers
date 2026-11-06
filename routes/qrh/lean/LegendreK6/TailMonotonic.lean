import Mathlib

/-!
# Analytic monotonicity for polynomial times exponential decay

This file proves the analytic decay criterion used in the six-term tail. It does
not accept a sampled monotonicity flag or a derivative sign as an unexplained
assumption: the derivative is computed, and its sign follows from the displayed
endpoint conditions.
-/

namespace LegendreK6

theorem affine_power_exp_antitone (A B c d L₀ : ℝ) (k : ℕ)
    (hA : 0 ≤ A) (hc : 0 ≤ c) (hbase : 0 ≤ A * L₀ + B)
    (hdecay : ((k + 1 : ℕ) : ℝ) * A ≤ c * (A * L₀ + B)) :
    AntitoneOn (fun L : ℝ => (A * L + B) ^ (k + 1) * Real.exp (-c * L + d))
      (Set.Ici L₀) := by
  let f : ℝ → ℝ := fun L => (A * L + B) ^ (k + 1) * Real.exp (-c * L + d)
  let f' : ℝ → ℝ := fun L =>
    (A * L + B) ^ k * Real.exp (-c * L + d) *
      (((k + 1 : ℕ) : ℝ) * A - c * (A * L + B))
  have hderiv (L : ℝ) : HasDerivAt f (f' L) L := by
    have ha : HasDerivAt (fun z : ℝ => A * z + B) A L := by
      convert ((hasDerivAt_id L).const_mul A).add_const B using 1 <;> simp
    have he : HasDerivAt (fun z : ℝ => Real.exp (-c * z + d))
        (Real.exp (-c * L + d) * (-c)) L := by
      apply HasDerivAt.exp
      convert ((hasDerivAt_id L).const_mul (-c)).add_const d using 1 <;> simp
    convert (ha.pow (k + 1)).mul he using 1
    dsimp [f']
    simp only [pow_succ]
    ring
  apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := f') (convex_Ici L₀)
  · exact (continuous_iff_continuousAt.mpr (fun L => (hderiv L).continuousAt)).continuousOn
  · intro L _
    exact (hderiv L).hasDerivWithinAt
  · intro L hL
    have hL₀ : L₀ ≤ L := (interior_subset hL)
    have hbaseL : 0 ≤ A * L + B := by nlinarith
    have hdecayL : ((k + 1 : ℕ) : ℝ) * A - c * (A * L + B) ≤ 0 := by
      nlinarith [mul_nonneg hc (mul_nonneg hA (sub_nonneg.mpr hL₀))]
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (pow_nonneg hbaseL k) (Real.exp_pos _).le) hdecayL

/-- The only rational factor in the density main term is decreasing. -/
theorem tail_ratio_antitone (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    AntitoneOn (fun L : ℝ => L / (L / 4 - (8 / 3) * b)) (Set.Ici 700) := by
  intro x hx y hy hxy
  have hx' : 700 ≤ x := hx
  have hy' : 700 ≤ y := hy
  have hdx : 0 < x / 4 - (8 / 3) * b := by linarith
  have hdy : 0 < y / 4 - (8 / 3) * b := by linarith
  apply (div_le_div_iff₀ hdy hdx).2
  nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hxy)]

/-- Algebraically normalized six-term tail, with `b = log 2` left as a parameter. -/
noncomputable def tailDecayExpression (b L : ℝ) : ℝ :=
  4 * (((9 / 32) * L + b) ^ 1 * Real.exp (-(3 / 32) * L + 0)) +
  (1122 / 25) *
    ((((9 / 32) * L + b) ^ 3 * Real.exp (-(1 / 32) * L + b / 3)) *
      (L / (L / 4 - (8 / 3) * b))) +
  (2 * (829 / 100)) * (((9 / 32) * L + b) ^ 2 * Real.exp (-(1 / 8) * L + 0)) +
  (2 * 147) * (((9 / 32) * L + b) ^ 1 * Real.exp (-(1 / 8) * L + 0)) +
  (1447 / 2000) * ((3 * L + 2) ^ 1 * Real.exp (-(1 / 32) * L + 0)) +
  (1 / 2) * ((1 * L + 1) ^ 2 * Real.exp (-(1 / 4) * L + 0)) +
  (1 / 4) * ((1 * L + 1) ^ 1 * Real.exp (-(3 / 4) * L + 0))

/-- Continuous infinite-range decay, proved by derivatives and order algebra. -/
theorem tail_decay_antitone (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    AntitoneOn (tailDecayExpression b) (Set.Ici 700) := by
  have h0 := affine_power_exp_antitone (9 / 32) b (3 / 32) 0 700 0
    (by norm_num) (by norm_num) (by linarith) (by norm_num; linarith)
  have h1 := affine_power_exp_antitone (9 / 32) b (1 / 32) (b / 3) 700 2
    (by norm_num) (by norm_num) (by linarith) (by norm_num; linarith)
  have h2a := affine_power_exp_antitone (9 / 32) b (1 / 8) 0 700 1
    (by norm_num) (by norm_num) (by linarith) (by norm_num; linarith)
  have h2b := affine_power_exp_antitone (9 / 32) b (1 / 8) 0 700 0
    (by norm_num) (by norm_num) (by linarith) (by norm_num; linarith)
  have hR := affine_power_exp_antitone 3 2 (1 / 32) 0 700 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hP := affine_power_exp_antitone 1 1 (1 / 4) 0 700 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hB := affine_power_exp_antitone 1 1 (3 / 4) 0 700 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  intro x hx y hy hxy
  have hx' : 700 ≤ x := hx
  have hy' : 700 ≤ y := hy
  have hux : 0 ≤ (9 / 32) * x + b := by linarith
  have hdy : 0 ≤ y / 4 - (8 / 3) * b := by linarith
  have hratio := tail_ratio_antitone b hb0 hb1 hx hy hxy
  have hprod := mul_le_mul (h1 hx hy hxy) hratio
    (div_nonneg (by linarith : 0 ≤ y) hdy)
    (mul_nonneg (pow_nonneg hux 3) (Real.exp_pos _).le)
  have hz0 := h0 hx hy hxy
  have hz2a := h2a hx hy hxy
  have hz2b := h2b hx hy hxy
  have hzR := hR hx hy hxy
  have hzP := hP hx hy hxy
  have hzB := hB hx hy hxy
  unfold tailDecayExpression
  norm_num only [Nat.reduceAdd] at hprod hz0 hz2a hz2b hzR hzP hzB
  linarith

end LegendreK6
