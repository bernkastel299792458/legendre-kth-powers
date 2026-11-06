import LegendreK6.DensityGridGrowth

/-! Simultaneous translation of the log-x and log-height density grid.
All comparisons are proved for the original exponential weights and powers.
The final theorem has only grid and numerical domain hypotheses. -/

namespace LegendreK6

open scoped BigOperators

theorem exp_power_shift_rate_le {u v p r : ℝ} (hu : 0 < u) (hv : 0 ≤ v)
    (hr : 0 ≤ r) :
    Real.exp (p*(u+v)) * (u+v)^r ≤
      Real.exp ((p+r/u)*v) * (Real.exp (p*u)*u^r) := by
  have huv : 0 < u+v := by linarith
  have hl := log_ratio_bound hu huv
  rw [Real.log_div (ne_of_gt huv) (ne_of_gt hu)] at hl
  have hm := mul_le_mul_of_nonneg_left hl hr
  rw [Real.rpow_def_of_pos huv, Real.rpow_def_of_pos hu]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he : r*((u+v-u)/u) = (r/u)*v := by ring
  rw [he] at hm
  nlinarith

theorem linear_exp_translation_le {A d β b : ℝ} (hA : 0 < A)
    (hd : 0 ≤ d) (hβ : β ≤ b) :
    (A+d)*Real.exp ((β-1)*(A+d)) ≤
      Real.exp ((1/A+b-1)*d)*(A*Real.exp ((β-1)*A)) := by
  have he := Real.add_one_le_exp (d/A)
  have hlin : A+d ≤ A*Real.exp (d/A) := by
    have hm := mul_le_mul_of_nonneg_left he hA.le
    field_simp at hm
    nlinarith
  have hb : Real.exp ((β-1)*d) ≤ Real.exp ((b-1)*d) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hd)
  rw [show (β-1)*(A+d) = (β-1)*A+(β-1)*d by ring, Real.exp_add]
  calc
    _ ≤ (A*Real.exp (d/A)) * (Real.exp ((β-1)*A)*Real.exp ((b-1)*d)) := by
      exact mul_le_mul hlin (mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _))
        (by positivity) (by positivity)
    _ = _ := by
      rw [show (1/A+b-1)*d = d/A+(b-1)*d by ring, Real.exp_add]
      ring

theorem sigmaGridWeight_translation_le (s : ℕ → ℝ) (A d : ℝ) (j : ℕ)
    (hA : 0 < A) (hd : 0 ≤ d) (hs : s j ≤ s (j+1)) :
    sigmaGridWeight s (A+d) j ≤
      Real.exp ((1/A+s (j+1)-1)*d)*sigmaGridWeight s A j := by
  have hint (L : ℝ) : IntervalIntegrable
      (fun v : ℝ => L*Real.exp ((v-1)*L)) MeasureTheory.volume (s j) (s (j+1)) :=
    (continuous_const.mul
      (Real.continuous_exp.comp ((continuous_id.sub continuous_const).mul continuous_const))).intervalIntegrable _ _
  unfold sigmaGridWeight
  rw [← exact_sigma_weight (A+d), ← exact_sigma_weight A,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hs (hint (A+d))
    ((hint A).const_mul _)
  intro β hβ
  exact linear_exp_translation_le hA hd hβ.2

theorem grid_translation_rate_nonpos {A u k lo hi p r : ℝ}
    (hA : 167 ≤ A) (hu : 28 ≤ u) (hk : 4 ≤ k)
    (_hlohi : lo ≤ hi) (hhi : hi ≤ 7/8) (hwidth : hi-lo ≤ 1/1024)
    (hp : 0 ≤ p) (hpc : p ≤ (8/3)*(1-lo)) (_hr : 0 ≤ r) (hr3 : r ≤ 3) :
    1/A+hi-1+(p+r/u)/k ≤ 0 := by
  have hA0 : 0 < A := by linarith
  have hu0 : 0 < u := by linarith
  have hk0 : 0 < k := by linarith
  have ha : 1/A ≤ 1/167 := one_div_le_one_div_of_le (by norm_num) hA
  have hr_u : r/u ≤ 3/28 := (div_le_iff₀ hu0).2 (by nlinarith)
  have hnum : 0 ≤ p+3/28 := by linarith
  have hdiv : (p+r/u)/k ≤ (p+3/28)/4 := by
    apply (div_le_iff₀ hk0).2
    have hm := mul_le_mul_of_nonneg_left hk (show 0 ≤ (p+3/28)/4 by positivity)
    nlinarith
  nlinarith

theorem sigmaGridWeight_exp_power_translation_le (s : ℕ → ℝ) (j : ℕ)
    (A u d k p r : ℝ) (hA : 0 < A) (hu : 0 < u) (hd : 0 ≤ d) (hk : 0 < k)
    (hs : s j ≤ s (j+1)) (hr : 0 ≤ r)
    (hrate : 1/A+s (j+1)-1+(p+r/u)/k ≤ 0) :
    sigmaGridWeight s (A+d) j * (Real.exp (p*(u+d/k))*(u+d/k)^r) ≤
      sigmaGridWeight s A j * (Real.exp (p*u)*u^r) := by
  have hw0 : 0 ≤ sigmaGridWeight s A j := sigma_weight_nonneg hA.le hs
  have hbase : 0 ≤ sigmaGridWeight s A j * (Real.exp (p*u)*u^r) := by positivity
  have hw := sigmaGridWeight_translation_le s A d j hA hd hs
  have hf := exp_power_shift_rate_le (p := p) hu (div_nonneg hd hk.le) hr
  have hm := mul_le_mul hw hf (by positivity)
    (mul_nonneg (Real.exp_nonneg _) hw0)
  calc
    _ ≤ (Real.exp ((1/A+s (j+1)-1)*d)*sigmaGridWeight s A j) *
        (Real.exp ((p+r/u)*(d/k))*(Real.exp (p*u)*u^r)) := hm
    _ = Real.exp ((1/A+s (j+1)-1+(p+r/u)/k)*d) *
        (sigmaGridWeight s A j*(Real.exp (p*u)*u^r)) := by
      rw [show (1/A+s (j+1)-1+(p+r/u)/k)*d =
        (1/A+s (j+1)-1)*d+(p+r/u)*(d/k) by ring, Real.exp_add]
      ring
    _ ≤ 1*(sigmaGridWeight s A j*(Real.exp (p*u)*u^r)) := by
      apply mul_le_mul_of_nonneg_right _ hbase
      calc
        _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (mul_nonpos_of_nonpos_of_nonneg hrate hd)
        _ = 1 := Real.exp_zero
    _ = _ := one_mul _

theorem sigmaGridWeight_cs_translation_le (s : ℕ → ℝ) (j : ℕ) (row : Fin 12)
    (A u d k : ℝ) (hA : 167 ≤ A) (hu : 28 ≤ u) (hd : 0 ≤ d) (hk : 4 ≤ k)
    (hlo : 1/2 ≤ s j) (hs : s j ≤ s (j+1)) (hhi : s (j+1) ≤ 7/8)
    (hwidth : s (j+1)-s j ≤ 1/1024) :
    sigmaGridWeight s (A+d) j * csLogHeightBound row (s j) (u+d/k) ≤
      sigmaGridWeight s A j * csLogHeightBound row (s j) u := by
  have hσ : s j ≤ 7/8 := hs.trans hhi
  obtain ⟨hp0,hp1⟩ := csExponent_range hlo hσ
  have hpc : csExponent (s j) ≤ (8/3)*(1-s j) := by
    calc
      _ = (3/(2-s j))*(1-s j) := by unfold csExponent; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (cs_density_exponent_bound hσ) (by linarith)
  have hA0 : 0 < A := by linarith
  have hu0 : 0 < u := by linarith
  have hk0 : 0 < k := by linarith
  have hm := sigmaGridWeight_exp_power_translation_le s j A u d k
    (csExponent (s j)) (csExponent (s j)+2) hA0 hu0 hd hk0 hs (by linarith)
    (grid_translation_rate_nonpos hA hu hk hs hhi hwidth hp0 hpc (by linarith) (by linarith))
  have hs2 := sigmaGridWeight_exp_power_translation_le s j A u d k 0 2
    hA0 hu0 hd hk0 hs (by norm_num)
    (grid_translation_rate_nonpos hA hu hk hs hhi hwidth (by norm_num)
      (hp0.trans hpc) (by norm_num) (by norm_num))
  have hs1 := sigmaGridWeight_exp_power_translation_le s j A u d k 0 1
    hA0 hu0 hd hk0 hs (by norm_num)
    (grid_translation_rate_nonpos hA hu hk hs hhi hwidth (by norm_num)
      (hp0.trans hpc) (by norm_num) (by norm_num))
  norm_num only [zero_mul, Real.exp_zero, one_mul, Real.rpow_two, Real.rpow_one] at hs2 hs1
  obtain ⟨h1,h2,h3⟩ := cs_row_constants_nonneg row
  have hh1 := mul_le_mul_of_nonneg_left hm h1
  have hh2 := mul_le_mul_of_nonneg_left hs2 h2
  have hh3 := mul_le_mul_of_nonneg_left hs1 h3
  unfold csLogHeightBound
  nlinarith only [hh1,hh2,hh3]

theorem densityGridBase_translation_le (A u d k : ℝ)
    (hu : 28 ≤ u) (hd : 0 ≤ d) (hk : 4 ≤ k) :
    Real.exp (-(A+d)/2+(u+d/k))*(u+d/k) ≤ Real.exp (-A/2+u)*u := by
  have hu0 : 0 < u := by linarith
  have hk0 : 0 < k := by linarith
  have hv : 0 ≤ d/k := div_nonneg hd hk0.le
  have huv : 0 < u+d/k := by linarith
  have hlog := log_ratio_bound hu0 huv
  rw [Real.log_div (ne_of_gt huv) (ne_of_gt hu0)] at hlog
  have hdk : d/k ≤ d/4 := div_le_div_of_nonneg_left hd (by norm_num) hk
  have hdu : (d/k)/u ≤ d/112 := by
    apply (div_le_iff₀ hu0).2
    have hm := mul_nonneg hd (show 0 ≤ u-28 by linarith)
    nlinarith
  have hexp (X v : ℝ) (hv0 : 0 < v) :
      Real.exp (-X/2+v)*v = Real.exp (-X/2+v+Real.log v) := by
    rw [Real.exp_add (-X/2+v) (Real.log v), Real.exp_log hv0]
  rw [hexp (A+d) (u+d/k) huv, hexp A u hu0]
  apply Real.exp_le_exp.mpr
  have hlog' : Real.log (u+d/k)-Real.log u ≤ (d/k)/u := by
    convert hlog using 1 <;> ring
  nlinarith

/-- A fixed density grid improves under simultaneous log-x/log-height
translation for every real `k ≥ 4`. Thus both the sixth-power and the
fourth-power height scalings are covered by the same proved inequality. -/
theorem densityGridPhi_translation_le (s : ℕ → ℝ) (row : ℕ → Fin 12)
    (n : ℕ) (A u d k : ℝ) (hA : 167 ≤ A) (hu : 28 ≤ u) (hd : 0 ≤ d) (hk : 4 ≤ k)
    (hgrid : ∀ j < n, 1/2 ≤ s j ∧ s j ≤ s (j+1) ∧ s (j+1) ≤ 7/8 ∧
      s (j+1)-s j ≤ 1/1024) :
    densityGridPhi s row n (A+d) (u+d/k) ≤ densityGridPhi s row n A u := by
  unfold densityGridPhi
  apply add_le_add (densityGridBase_translation_le A u d k hu hd hk)
  apply Finset.sum_le_sum
  intro j hj
  obtain ⟨hlo,hs,hhi,hw⟩ := hgrid j (Finset.mem_range.mp hj)
  exact sigmaGridWeight_cs_translation_le s j (row j) A u d k hA hu hd hk hlo hs hhi hw

theorem densityGridPhi_translation_six_le (s : ℕ → ℝ) (row : ℕ → Fin 12)
    (n : ℕ) (A u d : ℝ) (hA : 167 ≤ A) (hu : 28 ≤ u) (hd : 0 ≤ d)
    (hgrid : ∀ j < n, 1/2 ≤ s j ∧ s j ≤ s (j+1) ∧ s (j+1) ≤ 7/8 ∧
      s (j+1)-s j ≤ 1/1024) :
    densityGridPhi s row n (A+d) (u+d/6) ≤ densityGridPhi s row n A u :=
  densityGridPhi_translation_le s row n A u d 6 hA hu hd (by norm_num) hgrid

theorem densityGridPhi_translation_four_le (s : ℕ → ℝ) (row : ℕ → Fin 12)
    (n : ℕ) (A u d : ℝ) (hA : 167 ≤ A) (hu : 28 ≤ u) (hd : 0 ≤ d)
    (hgrid : ∀ j < n, 1/2 ≤ s j ∧ s j ≤ s (j+1) ∧ s (j+1) ≤ 7/8 ∧
      s (j+1)-s j ≤ 1/1024) :
    densityGridPhi s row n (A+d) (u+d/4) ≤ densityGridPhi s row n A u :=
  densityGridPhi_translation_le s row n A u d 4 hA hu hd (by norm_num) hgrid

end LegendreK6
