import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The actual complex-power term in a truncated explicit formula

This module bounds `(y^ρ - x^ρ) / ρ` for positive real endpoints and
`Re ρ ≤ 1`. The powers are Mathlib's complex powers. No assertion about
zeta zeros, density bounds, or prime intervals is assumed here.
-/

namespace LegendreK6

open scoped BigOperators

/-- The normalized complex-power increment is bounded by its derivative at
the left endpoint when `Re ρ ≤ 1`. -/
theorem norm_cpow_sub_div_le {x y : ℝ} {ρ : ℂ}
    (hx : 0 < x) (hxy : x ≤ y) (hρ : ρ ≠ 0) (hre : ρ.re ≤ 1) :
    ‖((y : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ‖ ≤
      (y - x) * x ^ (ρ.re - 1) := by
  have hderiv : ∀ t ∈ Set.Icc x y,
      HasDerivWithinAt (fun u : ℝ => (u : ℂ) ^ ρ / ρ)
        ((t : ℂ) ^ (ρ - 1)) (Set.Icc x y) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le hx ht.1)
    have he : ρ - 1 ≠ -1 := by
      intro h
      apply hρ
      linear_combination h
    simpa only [sub_add_cancel] using
      (hasDerivAt_ofReal_cpow_const' ht0 he).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico x y,
      ‖(t : ℂ) ^ (ρ - 1)‖ ≤ x ^ (ρ.re - 1) := by
    intro t ht
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le hx ht.1),
      Complex.sub_re, Complex.one_re]
    exact Real.rpow_le_rpow_of_nonpos hx ht.1 (sub_nonpos.mpr hre)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound y
    (show y ∈ Set.Icc x y from ⟨hxy, le_rfl⟩)
  simpa only [← sub_div, mul_comm] using h

/-- Summing the actual complex-power increments with natural multiplicities
reduces their norm to a positive real sum. This applies to a finite truncation
of zeta zeros once its membership conditions have been established. -/
theorem norm_sum_cpow_sub_div_le {ι : Type*} (s : Finset ι)
    (ρ : ι → ℂ) (multiplicity : ι → ℕ) {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y)
    (hρ : ∀ i ∈ s, ρ i ≠ 0) (hre : ∀ i ∈ s, (ρ i).re ≤ 1) :
    ‖∑ i ∈ s, (multiplicity i : ℂ) *
      (((y : ℂ) ^ ρ i - (x : ℂ) ^ ρ i) / ρ i)‖ ≤
      (y - x) * ∑ i ∈ s, (multiplicity i : ℝ) * x ^ ((ρ i).re - 1) := by
  calc
    _ ≤ ∑ i ∈ s, ‖(multiplicity i : ℂ) *
        (((y : ℂ) ^ ρ i - (x : ℂ) ^ ρ i) / ρ i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, (multiplicity i : ℝ) *
        ((y - x) * x ^ ((ρ i).re - 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left
        (norm_cpow_sub_div_le hx hxy (hρ i hi) (hre i hi)) (Nat.cast_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end LegendreK6
