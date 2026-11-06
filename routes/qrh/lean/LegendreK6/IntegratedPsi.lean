import LegendreK6.PrimeExtraction
import LegendreK6.AnalyticBounds

/-!
# Actual integrated Chebyshev sums and the trapezoid weight

The integrated sum is a finite sum of Mathlib's actual von Mangoldt values.
Extending its cutoff replaces each linear factor by its positive part. This
gives the four-point trapezoid identity before any explicit formula is used.
-/

namespace LegendreK6

open scoped BigOperators

/-- The classical integrated Chebyshev sum `Psi_1(t)`. Including the term at
`m=t` is harmless, since its linear factor vanishes. -/
noncomputable def integratedPsi (t : ℝ) : ℝ :=
  ∑ m ∈ Finset.Ioc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt m * (t - (m : ℝ))

/-- Extend the finite cutoff to any larger real endpoint by taking positive
parts. No positivity condition on t is necessary. -/
theorem integratedPsi_eq_sum_up_to (t Y : ℝ) (htY : t ≤ Y) :
    integratedPsi t = ∑ m ∈ Finset.Ioc 0 ⌊Y⌋₊,
      ArithmeticFunction.vonMangoldt m * max (t - (m : ℝ)) 0 := by
  classical
  have hsub : Finset.Ioc 0 ⌊t⌋₊ ⊆ Finset.Ioc 0 ⌊Y⌋₊ :=
    Finset.Ioc_subset_Ioc_right (Nat.floor_mono htY)
  calc
    _ = ∑ m ∈ Finset.Ioc 0 ⌊t⌋₊,
        ArithmeticFunction.vonMangoldt m * max (t - (m : ℝ)) 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      obtain ⟨hm0, hmt⟩ := Finset.mem_Ioc.mp hm
      have hmreal := (Nat.le_floor_iff' hm0.ne').mp hmt
      rw [max_eq_left (sub_nonneg.mpr hmreal)]
    _ = _ := by
      apply Finset.sum_subset hsub
      intro m hmY hmt
      have hm0 := (Finset.mem_Ioc.mp hmY).1
      have hfloor : ⌊t⌋₊ < m := by
        by_contra! h
        exact hmt (Finset.mem_Ioc.mpr ⟨hm0, h⟩)
      have hmreal := (Nat.floor_lt' hm0.ne').mp hfloor
      rw [max_eq_right (sub_nonpos.mpr hmreal.le), mul_zero]

theorem integratedPsi_nonneg (t : ℝ) : 0 ≤ integratedPsi t := by
  rw [integratedPsi_eq_sum_up_to t t le_rfl]
  apply Finset.sum_nonneg
  intro m _
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_max_right _ _)

/-- The four positive parts defining the normalized trapezoid on `[x,x+h]`. -/
noncomputable def trapezoidWeight (x h a b t : ℝ) : ℝ :=
  (max (x - t) 0 - max (x + a * h - t) 0 - max (x + b * h - t) 0 +
    max (x + h - t) 0) / (a * b * h)

theorem trapezoid_numerator_bounds (x h a b t : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (horder : a ≤ b) (hh : 0 < h) :
    0 ≤ max (x - t) 0 - max (x + a * h - t) 0 - max (x + b * h - t) 0 +
        max (x + h - t) 0 ∧
    max (x - t) 0 - max (x + a * h - t) 0 - max (x + b * h - t) 0 +
        max (x + h - t) 0 ≤ a * h := by
  have hah := mul_pos ha hh
  have hbh := mul_pos hb hh
  have hsum : a * h + b * h = h := by nlinarith [hab]
  have hord := mul_le_mul_of_nonneg_right horder hh.le
  simp only [max_def]
  split_ifs <;> constructor <;> nlinarith

/-- The normalized weight is nonnegative and bounded by its plateau height. -/
theorem trapezoidWeight_bounds (x h a b t : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (horder : a ≤ b) (hh : 0 < h) :
    0 ≤ trapezoidWeight x h a b t ∧ trapezoidWeight x h a b t ≤ 1 / b := by
  obtain ⟨hn0, hna⟩ := trapezoid_numerator_bounds x h a b t ha hb hab horder hh
  have hden : 0 < a * b * h := mul_pos (mul_pos ha hb) hh
  constructor
  · exact div_nonneg hn0 hden.le
  · unfold trapezoidWeight
    calc
      _ ≤ (a * h) / (a * b * h) := div_le_div_of_nonneg_right hna hden.le
      _ = 1 / b := by field_simp

theorem trapezoidWeight_eq_zero_left (x h a b t : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hh : 0 < h) (ht : t ≤ x) :
    trapezoidWeight x h a b t = 0 := by
  have hah := mul_pos ha hh
  have hbh := mul_pos hb hh
  have hsum : a * h + b * h = h := by nlinarith [hab]
  unfold trapezoidWeight
  rw [max_eq_left (by linarith : 0 ≤ x - t),
    max_eq_left (by linarith : 0 ≤ x + a * h - t),
    max_eq_left (by linarith : 0 ≤ x + b * h - t),
    max_eq_left (by linarith : 0 ≤ x + h - t)]
  have hz : x - t - (x + a * h - t) - (x + b * h - t) + (x + h - t) = 0 := by
    linarith
  rw [hz, zero_div]

theorem trapezoidWeight_eq_zero_right (x h a b t : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hh : 0 < h) (ht : x + h ≤ t) :
    trapezoidWeight x h a b t = 0 := by
  have hah := mul_pos ha hh
  have hbh := mul_pos hb hh
  have hsum : a * h + b * h = h := by nlinarith [hab]
  unfold trapezoidWeight
  rw [max_eq_right (by linarith : x - t ≤ 0),
    max_eq_right (by linarith : x + a * h - t ≤ 0),
    max_eq_right (by linarith : x + b * h - t ≤ 0),
    max_eq_right (by linarith : x + h - t ≤ 0)]
  norm_num

/-- Nonzero weight forces strict interior support, including exclusion of both
endpoints. This form applies directly to the finite prime-extraction theorem. -/
theorem trapezoidWeight_support (x h a b t : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hh : 0 < h)
    (hw : trapezoidWeight x h a b t ≠ 0) : x < t ∧ t < x + h := by
  constructor
  · by_contra! ht
    exact hw (trapezoidWeight_eq_zero_left x h a b t ha hb hab hh ht)
  · by_contra! ht
    exact hw (trapezoidWeight_eq_zero_right x h a b t ha hb hab hh ht)

theorem trapezoidWeight_pos_support (x h a b t : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hh : 0 < h)
    (hw : 0 < trapezoidWeight x h a b t) : x < t ∧ t < x + h :=
  trapezoidWeight_support x h a b t ha hb hab hh (ne_of_gt hw)

/-- The actual finite weighted Mangoldt sum equals the four-point difference
of the actual integrated Chebyshev sums. This is a finite algebraic identity,
independent of any explicit formula or zero-counting input. -/
theorem weightedMangoldt_trapezoid_eq (x h a b Y : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hh : 0 < h)
    (hY : x + h ≤ Y) :
    weightedMangoldt (Finset.Ioc 0 ⌊Y⌋₊) (fun m => trapezoidWeight x h a b (m : ℝ)) =
      (integratedPsi x - integratedPsi (x + a * h) - integratedPsi (x + b * h) +
        integratedPsi (x + h)) / (a * b * h) := by
  have hah := mul_pos ha hh
  have hbh := mul_pos hb hh
  have hsum : a * h + b * h = h := by nlinarith [hab]
  rw [integratedPsi_eq_sum_up_to x Y (by linarith),
    integratedPsi_eq_sum_up_to (x + a * h) Y (by linarith),
    integratedPsi_eq_sum_up_to (x + b * h) Y (by linarith),
    integratedPsi_eq_sum_up_to (x + h) Y hY,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib, Finset.sum_div]
  unfold weightedMangoldt trapezoidWeight
  apply Finset.sum_congr rfl
  intro m _
  ring

end LegendreK6
