import LegendreK6.FiniteDensityGrid

/-! Growth of the explicit grid envelope, used for a geometric height tail. -/

namespace LegendreK6

open scoped BigOperators

theorem exp_power_shift_le {U v p r : ℝ} (hU : 6 ≤ U) (hv : 0 ≤ v)
    (hp : p ≤ 1) (hr0 : 0 ≤ r) (hr : r ≤ 3) :
    Real.exp (p * (U+v)) * (U+v)^r ≤
      Real.exp (3/2*v) * (Real.exp (p*U) * U^r) := by
  have hU0 : 0 < U := by linarith
  have hUv : 0 < U+v := by linarith
  have hl := log_ratio_bound hU0 hUv
  rw [Real.log_div (ne_of_gt hUv) (ne_of_gt hU0)] at hl
  have hrU : r / U ≤ 1/2 := (div_le_iff₀ hU0).2 (by linarith)
  have hrl := mul_le_mul_of_nonneg_left hl hr0
  have hrv := mul_le_mul_of_nonneg_right hrU hv
  have hpv := mul_le_mul_of_nonneg_right hp hv
  rw [Real.rpow_def_of_pos hUv, Real.rpow_def_of_pos hU0]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have heq : r*((U+v-U)/U) = (r/U)*v := by ring
  rw [heq] at hrl
  nlinarith

theorem cs_row_constants_nonneg (i : Fin 12) :
    0 ≤ csB1 i ∧ 0 ≤ csB2 i ∧ 0 ≤ csB3 i := by
  fin_cases i <;> norm_num [csB1, csB2, csB3]

theorem csExponent_range {σ : ℝ} (hlo : 1/2 ≤ σ) (hhi : σ ≤ 7/8) :
    0 ≤ csExponent σ ∧ csExponent σ ≤ 1 := by
  unfold csExponent
  constructor
  · apply div_nonneg <;> linarith
  · exact (div_le_iff₀ (by linarith : 0 < 2-σ)).2 (by linarith)

theorem csLogHeightBound_nonneg (i : Fin 12) (σ u : ℝ) (hu : 0 ≤ u) :
    0 ≤ csLogHeightBound i σ u := by
  obtain ⟨h1,h2,h3⟩ := cs_row_constants_nonneg i
  unfold csLogHeightBound
  positivity

theorem csLogHeightBound_shift_le (i : Fin 12) (σ U v : ℝ)
    (hlo : 1/2 ≤ σ) (hhi : σ ≤ 7/8) (hU : 6 ≤ U) (hv : 0 ≤ v) :
    csLogHeightBound i σ (U+v) ≤ Real.exp (3/2*v) * csLogHeightBound i σ U := by
  obtain ⟨hp0,hp1⟩ := csExponent_range hlo hhi
  obtain ⟨h1,h2,h3⟩ := cs_row_constants_nonneg i
  have hm := exp_power_shift_le (p := csExponent σ) (r := csExponent σ+2)
    hU hv hp1 (by linarith) (by linarith)
  have hsq := exp_power_shift_le (p := 0) (r := 2) hU hv (by norm_num)
    (by norm_num) (by norm_num)
  have hlin := exp_power_shift_le (p := 0) (r := 1) hU hv (by norm_num)
    (by norm_num) (by norm_num)
  norm_num only [zero_mul, Real.exp_zero, one_mul, Real.rpow_two, Real.rpow_one] at hsq hlin
  have hh1 := mul_le_mul_of_nonneg_left hm h1
  have hh2 := mul_le_mul_of_nonneg_left hsq h2
  have hh3 := mul_le_mul_of_nonneg_left hlin h3
  unfold csLogHeightBound
  nlinarith

theorem densityGridPhi_nonneg (s : ℕ → ℝ) (row : ℕ → Fin 12)
    (n : ℕ) (L U : ℝ) (hs : Monotone s) (hL : 0 ≤ L) (hU : 0 ≤ U) :
    0 ≤ densityGridPhi s row n L U := by
  unfold densityGridPhi
  apply add_nonneg (mul_nonneg (Real.exp_nonneg _) hU)
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (sigmaGridWeight_nonneg s L j hs hL)
    (csLogHeightBound_nonneg (row j) (s j) U hU)

theorem densityGridPhi_shift_le (s : ℕ → ℝ) (row : ℕ → Fin 12)
    (n : ℕ) (L U v : ℝ) (hs : Monotone s) (hL : 0 ≤ L)
    (hσ : ∀ j < n, 1/2 ≤ s j ∧ s j ≤ 7/8) (hU : 6 ≤ U) (hv : 0 ≤ v) :
    densityGridPhi s row n L (U+v) ≤ Real.exp (3/2*v)*densityGridPhi s row n L U := by
  unfold densityGridPhi
  rw [mul_add (Real.exp (3/2*v)), Finset.mul_sum]
  apply add_le_add
  · have hb := exp_power_shift_le (p := 1) (r := 1) hU hv (by norm_num)
      (by norm_num) (by norm_num)
    norm_num only [one_mul, Real.rpow_one] at hb
    have hm := mul_le_mul_of_nonneg_left hb (Real.exp_nonneg (-L/2))
    simpa only [Real.exp_add, mul_assoc, mul_left_comm, mul_comm] using hm
  · apply Finset.sum_le_sum
    intro j hj
    obtain ⟨hlo,hhi⟩ := hσ j (Finset.mem_range.mp hj)
    have hm := mul_le_mul_of_nonneg_left
      (csLogHeightBound_shift_le (row j) (s j) U v hlo hhi hU hv)
      (sigmaGridWeight_nonneg s L j hs hL)
    simpa only [mul_assoc, mul_left_comm] using hm

theorem exp_nat_log_four (U : ℝ) (k : ℕ) :
    Real.exp (U + (k:ℝ)*Real.log 4) = Real.exp U * (4:ℝ)^k := by
  rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<4)]

theorem exp_three_halves_nat_log_four (k : ℕ) :
    Real.exp (3/2*((k:ℝ)*Real.log 4)) = (8:ℝ)^k := by
  have hlog : Real.log 4 = 2*Real.log 2 := by
    have h4 : (4:ℝ) = 2^2 := by norm_num
    rw [h4, Real.log_pow]
    norm_num
  have he : Real.exp ((3:ℝ)*Real.log 2) = 8 := by
    have hh := Real.exp_nat_mul (Real.log 2) 3
    norm_num [Real.exp_log (by norm_num : (0:ℝ)<2)] at hh
    exact hh
  rw [show 3/2*((k:ℝ)*Real.log 4) = (k:ℝ)*(3*Real.log 2) by rw [hlog]; ring,
    Real.exp_nat_mul, he]

theorem densityGridPhi_geometric_le (s : ℕ → ℝ) (row : ℕ → Fin 12)
    (n : ℕ) (L U : ℝ) (k : ℕ) (hs : Monotone s) (hL : 0 ≤ L)
    (hσ : ∀ j < n, 1/2 ≤ s j ∧ s j ≤ 7/8) (hU : 6 ≤ U) :
    densityGridPhi s row n L (U+(k:ℝ)*Real.log 4) ≤
      densityGridPhi s row n L U * (8:ℝ)^k := by
  have hv : 0 ≤ (k:ℝ)*Real.log 4 := mul_nonneg (Nat.cast_nonneg _)
    (Real.log_nonneg (by norm_num))
  have hh := densityGridPhi_shift_le s row n L U ((k:ℝ)*Real.log 4) hs hL hσ hU hv
  rw [exp_three_halves_nat_log_four] at hh
  simpa only [mul_comm] using hh

end LegendreK6
