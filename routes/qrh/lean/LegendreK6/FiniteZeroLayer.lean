import LegendreK6.AnalyticBounds

/-!
# A finite, multiplicity-aware real-part layer bound

The upper layer uses the closed condition `σ ≤ β`, including `β = b`.
Terms below the splitting line `a` are bounded by the base exponential.
The finite sum/integral interchange is justified by interval integrability.
This is a general finite-sum lemma; it asserts no density bound about zeta.
-/

namespace LegendreK6

open scoped BigOperators
open MeasureTheory

/-- The elementary layer for a single real part, including either endpoint. -/
theorem exp_le_base_add_layer {L a b β : ℝ} (hL : 0 ≤ L)
    (hab : a ≤ b) (hβ : β ≤ b) :
    Real.exp ((β - 1) * L) ≤ Real.exp ((a - 1) * L) +
      ∫ σ in a..b, if σ ≤ β then L * Real.exp ((σ - 1) * L) else 0 := by
  by_cases haβ : a ≤ β
  · change Real.exp ((β - 1) * L) ≤ Real.exp ((a - 1) * L) +
      ∫ σ in a..b, (Set.indicator {σ | σ ≤ β})
        (fun σ => L * Real.exp ((σ - 1) * L)) σ
    rw [intervalIntegral.integral_indicator ⟨haβ, hβ⟩, exact_sigma_weight]
    linarith
  · have hbase : Real.exp ((β - 1) * L) ≤ Real.exp ((a - 1) * L) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (by linarith) hL
    have hnonneg : 0 ≤ ∫ σ in a..b,
        if σ ≤ β then L * Real.exp ((σ - 1) * L) else 0 := by
      apply intervalIntegral.integral_nonneg_of_forall hab
      intro σ
      split_ifs
      · exact mul_nonneg hL (Real.exp_nonneg _)
      · exact le_rfl
    linarith

/-- The closed single-point layer is integrable on every finite interval. -/
theorem intervalIntegrable_exp_layer (L a b β : ℝ) :
    IntervalIntegrable
      (fun σ => if σ ≤ β then L * Real.exp ((σ - 1) * L) else 0)
      volume a b := by
  have hc : Continuous (fun σ => L * Real.exp ((σ - 1) * L)) := by fun_prop
  have hf : IntervalIntegrable (fun σ => L * Real.exp ((σ - 1) * L)) volume a b :=
    hc.intervalIntegrable a b
  change IntervalIntegrable ((Set.Iic β).indicator
    (fun σ => L * Real.exp ((σ - 1) * L))) volume a b
  exact ⟨hf.1.indicator measurableSet_Iic, hf.2.indicator measurableSet_Iic⟩

/-- Count finite real parts with natural multiplicities above a closed line. -/
noncomputable def finiteLayerCount {ι : Type*} (s : Finset ι) (β : ι → ℝ)
    (multiplicity : ι → ℕ) (σ : ℝ) : ℝ :=
  ∑ i ∈ s, if σ ≤ β i then (multiplicity i : ℝ) else 0

/-- The layer count is the real cast of the filtered natural multiplicity sum. -/
theorem finiteLayerCount_eq_cast_sum_filter {ι : Type*} (s : Finset ι)
    (β : ι → ℝ) (multiplicity : ι → ℕ) (σ : ℝ) :
    finiteLayerCount s β multiplicity σ =
      ((∑ i ∈ s.filter (fun i => σ ≤ β i), multiplicity i : ℕ) : ℝ) := by
  classical
  simp [finiteLayerCount, Finset.sum_filter]

/-- The complete finite layer integrand is interval integrable, without a
sign or ordering condition on the numerical parameters. -/
theorem intervalIntegrable_finite_exp_layer {ι : Type*} (s : Finset ι)
    (β : ι → ℝ) (multiplicity : ι → ℕ) (L a b : ℝ) :
    IntervalIntegrable (fun σ => L * Real.exp ((σ - 1) * L) *
      finiteLayerCount s β multiplicity σ) volume a b := by
  classical
  have hi : ∀ i ∈ s, IntervalIntegrable
      (fun σ => (multiplicity i : ℝ) *
        (if σ ≤ β i then L * Real.exp ((σ - 1) * L) else 0)) volume a b := by
    intro i _
    exact (intervalIntegrable_exp_layer L a b (β i)).const_mul _
  have heq : (fun σ => L * Real.exp ((σ - 1) * L) *
      finiteLayerCount s β multiplicity σ) =
      ∑ i ∈ s, (fun σ => (multiplicity i : ℝ) *
        (if σ ≤ β i then L * Real.exp ((σ - 1) * L) else 0)) := by
    funext σ
    simp only [Finset.sum_apply, finiteLayerCount, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  rw [heq]
  exact IntervalIntegrable.sum s hi

/-- Finite real-part layer integration with full natural multiplicities. -/
theorem finite_exp_layer_bound {ι : Type*} (s : Finset ι) (β : ι → ℝ)
    (multiplicity : ι → ℕ) {L a b : ℝ}
    (hL : 0 ≤ L) (hab : a ≤ b) (hβ : ∀ i ∈ s, β i ≤ b) :
    (∑ i ∈ s, (multiplicity i : ℝ) * Real.exp ((β i - 1) * L)) ≤
      (∑ i ∈ s, (multiplicity i : ℝ)) * Real.exp ((a - 1) * L) +
      ∫ σ in a..b, L * Real.exp ((σ - 1) * L) *
        finiteLayerCount s β multiplicity σ := by
  classical
  have hi : ∀ i ∈ s, IntervalIntegrable
      (fun σ => (multiplicity i : ℝ) *
        (if σ ≤ β i then L * Real.exp ((σ - 1) * L) else 0)) volume a b := by
    intro i _
    exact (intervalIntegrable_exp_layer L a b (β i)).const_mul _
  have hsum :
      (∑ i ∈ s, (multiplicity i : ℝ) * Real.exp ((β i - 1) * L)) ≤
      ∑ i ∈ s, (multiplicity i : ℝ) * (Real.exp ((a - 1) * L) +
        ∫ σ in a..b, if σ ≤ β i then L * Real.exp ((σ - 1) * L) else 0) := by
    apply Finset.sum_le_sum
    intro i hmem
    exact mul_le_mul_of_nonneg_left (exp_le_base_add_layer hL hab (hβ i hmem))
      (Nat.cast_nonneg _)
  calc
    _ ≤ _ := hsum
    _ = (∑ i ∈ s, (multiplicity i : ℝ)) * Real.exp ((a - 1) * L) +
        ∫ σ in a..b, ∑ i ∈ s, (multiplicity i : ℝ) *
          (if σ ≤ β i then L * Real.exp ((σ - 1) * L) else 0) := by
      rw [intervalIntegral.integral_finsetSum hi]
      simp_rw [intervalIntegral.integral_const_mul, mul_add]
      rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro σ _
      unfold finiteLayerCount
      dsimp only
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> ring

end LegendreK6
