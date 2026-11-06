import LegendreK6.IntegratedExplicitFormula

/-!
# Trivial-zero series and its actual trapezoid budget

The primitive and differenced series below are controlled by convergent
geometric series on `x > 1`. All terms are the actual complex powers from
the integrated explicit formula.
-/

namespace LegendreK6

private theorem trivial_argument_re (j : ℕ) :
    (-2 * ((j + 1 : ℕ) : ℂ)).re = -2 * (j + 1 : ℝ) := by norm_num

private theorem trivial_rpow_geometric {x : ℝ} (hx : 0 < x) (c : ℝ) (j : ℕ) :
    x ^ (-2 * (j + 1 : ℝ) + c) = x ^ (c - 2) * (x ^ (-2 : ℝ)) ^ j := by
  rw [← Real.rpow_natCast (x ^ (-2 : ℝ)) j, ← Real.rpow_mul hx.le, ← Real.rpow_add hx]
  congr 1
  ring

private theorem trivial_ratio_lt_one {x : ℝ} (hx : 1 < x) : x ^ (-2 : ℝ) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg hx (by norm_num)

/-- Pointwise geometric domination for the actual integrated trivial-zero term. -/
theorem norm_trivial_zeroPrimitive_le {t : ℝ} (ht : 0 < t) (j : ℕ) :
    ‖zeroPrimitive (-2 * ((j + 1 : ℕ) : ℂ)) t‖ ≤
      t ^ (-1 : ℝ) * (t ^ (-2 : ℝ)) ^ j := by
  let ρ : ℂ := -2 * ((j + 1 : ℕ) : ℂ)
  have hre : ρ.re = -2 * (j + 1 : ℝ) := trivial_argument_re j
  have hn : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hn0 : 1 ≤ ‖ρ‖ := by
    have hr := Complex.abs_re_le_norm ρ
    rw [hre, abs_of_nonpos (by linarith)] at hr
    linarith
  have hn1 : 1 ≤ ‖ρ + 1‖ := by
    have hr := Complex.abs_re_le_norm (ρ + 1)
    rw [Complex.add_re, Complex.one_re, hre, abs_of_nonpos (by linarith)] at hr
    linarith
  have hden : 1 ≤ ‖ρ‖ * ‖ρ + 1‖ := by nlinarith
  change ‖zeroPrimitive ρ t‖ ≤ _
  rw [zeroPrimitive, norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.add_re, Complex.one_re]
  calc
    _ ≤ t ^ (ρ.re + 1) / 1 :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg ht.le _) zero_lt_one hden
    _ = _ := by rw [div_one, hre, trivial_rpow_geometric ht]; norm_num

/-- Each pointwise primitive series is genuinely summable on `t > 1`. -/
theorem summable_trivial_zeroPrimitive {t : ℝ} (ht : 1 < t) :
    Summable (fun j : ℕ => zeroPrimitive (-2 * ((j + 1 : ℕ) : ℂ)) t) := by
  have ht0 := zero_lt_one.trans ht
  have hg := (hasSum_geometric_of_lt_one (Real.rpow_nonneg ht0.le (-2))
    (trivial_ratio_lt_one ht)).summable.mul_left (t ^ (-1 : ℝ))
  exact hg.of_norm_bounded (norm_trivial_zeroPrimitive_le ht0)

/-- The base kernel estimate applies to all negative even arguments without dividing by height. -/
theorem norm_trivial_trapezoidKernel_le {x h a b : ℝ}
    (hx : 0 < x) (hh : 0 < h) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (j : ℕ) :
    ‖trapezoidKernel x h a b (-2 * ((j + 1 : ℕ) : ℂ))‖ ≤
      (h * x ^ (-3 : ℝ)) * (x ^ (-2 : ℝ)) ^ j := by
  let ρ : ℂ := -2 * ((j + 1 : ℕ) : ℂ)
  have hre : ρ.re = -2 * (j + 1 : ℝ) := trivial_argument_re j
  have hn : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hρ : ρ ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp only [Complex.zero_re, hre] at hr
    linarith
  have hρ1 : ρ + 1 ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re, hre] at hr
    linarith
  have hbnd := norm_trapezoidKernel_le_base hx hh ha hb hab hρ hρ1 (show ρ.re ≤ 1 by rw [hre]; linarith)
  calc
    _ ≤ h * x ^ (ρ.re - 1) := hbnd
    _ = _ := by
      rw [hre, sub_eq_add_neg, trivial_rpow_geometric hx]
      norm_num
      ring

/-- Actual differenced trivial-zero series is summable. -/
theorem summable_trivial_trapezoidKernel {x h a b : ℝ}
    (hx : 1 < x) (hh : 0 < h) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    Summable (fun j : ℕ => trapezoidKernel x h a b (-2 * ((j + 1 : ℕ) : ℂ))) := by
  have hx0 := zero_lt_one.trans hx
  have hg := (hasSum_geometric_of_lt_one (Real.rpow_nonneg hx0.le (-2))
    (trivial_ratio_lt_one hx)).summable.mul_left (h * x ^ (-3 : ℝ))
  exact hg.of_norm_bounded (norm_trivial_trapezoidKernel_le hx0 hh ha hb hab)

/-- Exact geometric budget, before identifying the sum with the four-point trivial difference. -/
theorem norm_tsum_trivial_trapezoidKernel_le {x h a b : ℝ}
    (hx : 1 < x) (hh : 0 < h) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    ‖∑' j : ℕ, trapezoidKernel x h a b (-2 * ((j + 1 : ℕ) : ℂ))‖ ≤
      h * x ^ (-3 : ℝ) / (1 - x ^ (-2 : ℝ)) := by
  have hx0 := zero_lt_one.trans hx
  have hf := summable_trivial_trapezoidKernel hx hh ha hb hab
  have hg := (hasSum_geometric_of_lt_one (Real.rpow_nonneg hx0.le (-2))
    (trivial_ratio_lt_one hx)).mul_left (h * x ^ (-3 : ℝ))
  calc
    _ ≤ ∑' j : ℕ, ‖trapezoidKernel x h a b (-2 * ((j + 1 : ℕ) : ℂ))‖ :=
      norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' j : ℕ, (h * x ^ (-3 : ℝ)) * (x ^ (-2 : ℝ)) ^ j :=
      Summable.tsum_le_tsum (norm_trivial_trapezoidKernel_le hx0 hh ha hb hab) hf.norm hg.summable
    _ = _ := by rw [hg.tsum_eq]; ring

/-- The four pointwise convergent primitive series may be combined term by term.
Only finite linear operations on `HasSum` are used. -/
theorem hasSum_trapezoidTrivialDifference {x h a b : ℝ}
    (hx : 1 < x) (hh : 0 < h) (ha : 0 < a) (hb : 0 < b) :
    HasSum (fun j : ℕ => trapezoidKernel x h a b (-2 * ((j + 1 : ℕ) : ℂ)))
      (trapezoidTrivialDifference x h a b) := by
  have h0 := (summable_trivial_zeroPrimitive hx).hasSum
  have h1 := (summable_trivial_zeroPrimitive (show 1 < x + a * h by nlinarith [mul_pos ha hh])).hasSum
  have h2 := (summable_trivial_zeroPrimitive (show 1 < x + b * h by nlinarith [mul_pos hb hh])).hasSum
  have h3 := (summable_trivial_zeroPrimitive (show 1 < x + h by linarith)).hasSum
  simpa only [trapezoidKernel, trapezoidTrivialDifference, trivialZeroPrimitiveSum] using
    (((h0.sub h1).sub h2).add h3).div_const (((a * b * h : ℝ) : ℂ))

theorem trapezoidTrivialDifference_eq_tsum {x h a b : ℝ}
    (hx : 1 < x) (hh : 0 < h) (ha : 0 < a) (hb : 0 < b) :
    trapezoidTrivialDifference x h a b =
      ∑' j : ℕ, trapezoidKernel x h a b (-2 * ((j + 1 : ℕ) : ℂ)) :=
  (hasSum_trapezoidTrivialDifference hx hh ha hb).tsum_eq.symm

/-- The actual trivial-zero contribution has exactly the budget used in the certificates. -/
theorem norm_trapezoidTrivialDifference_le {x h a b : ℝ}
    (hx : 1 < x) (hh : 0 < h) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    ‖trapezoidTrivialDifference x h a b‖ ≤
      h * x ^ (-3 : ℝ) / (1 - x ^ (-2 : ℝ)) := by
  rw [trapezoidTrivialDifference_eq_tsum hx hh ha hb]
  exact norm_tsum_trivial_trapezoidKernel_le hx hh ha hb hab

end LegendreK6
