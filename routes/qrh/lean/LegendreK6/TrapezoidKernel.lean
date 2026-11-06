import Mathlib
import LegendreK6.CpowInterval

/-!
# Four-point bounds for the actual integrated zeta-zero kernel

The trapezoid operator is a finite difference of the actual complex primitive.
Two applications of the real mean-value bound give its basic bound, while one
application and the four-value triangle inequality give the two decay bounds.
No distributional derivative, integral interchange, or numerical oracle is used.
-/

namespace LegendreK6

/-- The primitive occurring in the integrated explicit formula. -/
noncomputable def zeroPrimitive (ρ : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))

/-- The normalized four-point trapezoid operator applied to a zero primitive. -/
noncomputable def trapezoidKernel (x h a b : ℝ) (ρ : ℂ) : ℂ :=
  (zeroPrimitive ρ x - zeroPrimitive ρ (x + a * h) -
    zeroPrimitive ρ (x + b * h) + zeroPrimitive ρ (x + h)) / ((a * b * h : ℝ) : ℂ)

theorem hasDerivAt_zeroPrimitive {ρ : ℂ} {t : ℝ}
    (ht : 0 < t) (hρ1 : ρ + 1 ≠ 0) :
    HasDerivAt (zeroPrimitive ρ) ((t : ℂ) ^ ρ / ρ) t := by
  have he : ρ ≠ -1 := by
    intro he
    apply hρ1
    rw [he]
    ring
  have hf : zeroPrimitive ρ = fun u : ℝ => ((u : ℂ) ^ (ρ + 1) / (ρ + 1)) / ρ := by
    funext u
    simp only [zeroPrimitive, div_div, mul_comm ρ]
  rw [hf]
  exact (hasDerivAt_ofReal_cpow_const' ht.ne' he).div_const ρ

/-- Basic bound, also applicable to negative even integers used for the trivial-zero terms. -/
theorem norm_trapezoidKernel_le_base {x h a b : ℝ} {ρ : ℂ}
    (hx : 0 < x) (hh : 0 < h) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (hρ : ρ ≠ 0) (hρ1 : ρ + 1 ≠ 0) (hre : ρ.re ≤ 1) :
    ‖trapezoidKernel x h a b ρ‖ ≤ h * x ^ (ρ.re - 1) := by
  let A := a * h
  let B := b * h
  have hA : 0 < A := mul_pos ha hh
  have hB : 0 < B := mul_pos hb hh
  have hAB : A + B = h := by dsimp [A, B]; nlinarith [hab]
  let H : ℝ → ℂ := fun t => zeroPrimitive ρ (t + A) - zeroPrimitive ρ t
  let H' : ℝ → ℂ := fun t => (t + A : ℝ) ^ (ρ : ℂ) / ρ - (t : ℂ) ^ ρ / ρ
  have hderiv : ∀ t ∈ Set.Icc x (x + B), HasDerivWithinAt H (H' t) (Set.Icc x (x + B)) t := by
    intro t ht
    have htpos := hx.trans_le ht.1
    exact (((hasDerivAt_zeroPrimitive (add_pos htpos hA) hρ1).comp_add_const t A).sub
      (hasDerivAt_zeroPrimitive htpos hρ1)).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico x (x + B), ‖H' t‖ ≤ A * x ^ (ρ.re - 1) := by
    intro t ht
    have htpos := hx.trans_le ht.1
    dsimp [H']
    rw [← sub_div]
    calc
      _ ≤ ((t + A) - t) * t ^ (ρ.re - 1) :=
        norm_cpow_sub_div_le htpos (by linarith) hρ hre
      _ ≤ A * x ^ (ρ.re - 1) := by
        rw [add_sub_cancel_left]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hx ht.1 (by linarith)) hA.le
  have hm := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound (x + B)
    (show x + B ∈ Set.Icc x (x + B) from ⟨by linarith, le_rfl⟩)
  have hnum : H (x + B) - H x =
      zeroPrimitive ρ x - zeroPrimitive ρ (x + a * h) -
        zeroPrimitive ρ (x + b * h) + zeroPrimitive ρ (x + h) := by
    dsimp [H]
    have he : x + B + A = x + h := by linarith
    rw [he]
    dsimp [A, B]
    ring
  rw [hnum] at hm
  have hden : 0 < a * b * h := mul_pos (mul_pos ha hb) hh
  unfold trapezoidKernel
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]
  apply (div_le_iff₀ hden).mpr
  calc
    _ ≤ (A * x ^ (ρ.re - 1)) * ((x + B) - x) := hm
    _ = (h * x ^ (ρ.re - 1)) * (a * b * h) := by dsimp [A, B]; ring

private theorem rpow_shift_bound {x Y t r : ℝ} (hx : 0 < x)
    (hxt : x ≤ t) (htY : t ≤ Y) (hr : r ≤ 0) (j : ℕ) :
    t ^ (r + j) ≤ x ^ r * Y ^ j := by
  have ht : 0 < t := hx.trans_le hxt
  rw [Real.rpow_add ht, Real.rpow_natCast]
  exact mul_le_mul (Real.rpow_le_rpow_of_nonpos hx hxt hr)
    (pow_le_pow_left₀ ht.le htY j) (pow_nonneg ht.le j) (Real.rpow_nonneg hx.le _)

private theorem zeroPrimitive_deriv_norm_le {x Y t : ℝ} {ρ : ℂ}
    (hx : 0 < x) (hxt : x ≤ t) (htY : t ≤ Y) (hre : ρ.re ≤ 1) (him : ρ.im ≠ 0) :
    ‖(t : ℂ) ^ ρ / ρ‖ ≤ Y * x ^ (ρ.re - 1) / |ρ.im| := by
  have ht := hx.trans_le hxt
  have hg : 0 < |ρ.im| := abs_pos.mpr him
  have hnum : t ^ ρ.re ≤ Y * x ^ (ρ.re - 1) := by
    simpa only [sub_add_cancel, Nat.cast_one, pow_one, mul_comm] using
      rpow_shift_bound hx hxt htY (show ρ.re - 1 ≤ 0 by linarith) 1
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  calc
    _ ≤ t ^ ρ.re / |ρ.im| := div_le_div_of_nonneg_left
      (Real.rpow_nonneg ht.le _) hg (Complex.abs_im_le_norm ρ)
    _ ≤ Y * x ^ (ρ.re - 1) / |ρ.im| := div_le_div_of_nonneg_right hnum hg.le

private theorem zeroPrimitive_increment_le {x Y u v : ℝ} {ρ : ℂ}
    (hx : 0 < x) (hxu : x ≤ u) (huv : u ≤ v) (hvY : v ≤ Y)
    (hρ1 : ρ + 1 ≠ 0) (hre : ρ.re ≤ 1) (him : ρ.im ≠ 0) :
    ‖zeroPrimitive ρ v - zeroPrimitive ρ u‖ ≤
      (Y * x ^ (ρ.re - 1) / |ρ.im|) * (v - u) := by
  apply norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hasDerivAt_zeroPrimitive (hx.trans_le (hxu.trans ht.1)) hρ1).hasDerivWithinAt)
    (fun t ht => zeroPrimitive_deriv_norm_le hx (hxu.trans ht.1) (ht.2.le.trans hvY) hre him)
    v ⟨huv, le_rfl⟩

/-- First decay bound, using two increments of length `a*h`. -/
theorem norm_trapezoidKernel_le_first {x h a b : ℝ} {ρ : ℂ}
    (hx : 0 < x) (hh : 0 < h) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (hρ1 : ρ + 1 ≠ 0) (hre : ρ.re ≤ 1) (him : ρ.im ≠ 0) :
    ‖trapezoidKernel x h a b ρ‖ ≤
      h * x ^ (ρ.re - 1) * ((2 / b) * ((x + h) / h) / |ρ.im|) := by
  have hah : 0 < a * h := mul_pos ha hh
  have hbh : 0 < b * h := mul_pos hb hh
  have habh : a * h + b * h = h := by nlinarith [hab]
  have hfirst := zeroPrimitive_increment_le hx (le_refl x)
    (show x ≤ x + a * h by linarith) (show x + a * h ≤ x + h by linarith)
    hρ1 hre him
  have hsecond := zeroPrimitive_increment_le hx (show x ≤ x + b * h by linarith)
    (show x + b * h ≤ x + h by linarith) (le_refl (x + h)) hρ1 hre him
  rw [show x + a * h - x = a * h by ring] at hfirst
  rw [show x + h - (x + b * h) = a * h by linarith] at hsecond
  have hnum : ‖zeroPrimitive ρ x - zeroPrimitive ρ (x + a * h) -
      zeroPrimitive ρ (x + b * h) + zeroPrimitive ρ (x + h)‖ ≤
      2 * ((x + h) * x ^ (ρ.re - 1) / |ρ.im|) * (a * h) := by
    have he : zeroPrimitive ρ x - zeroPrimitive ρ (x + a * h) -
        zeroPrimitive ρ (x + b * h) + zeroPrimitive ρ (x + h) =
        (zeroPrimitive ρ (x + h) - zeroPrimitive ρ (x + b * h)) -
          (zeroPrimitive ρ (x + a * h) - zeroPrimitive ρ x) := by ring
    rw [he]
    calc
      _ ≤ ‖zeroPrimitive ρ (x + h) - zeroPrimitive ρ (x + b * h)‖ +
          ‖zeroPrimitive ρ (x + a * h) - zeroPrimitive ρ x‖ := norm_sub_le _ _
      _ ≤ ((x + h) * x ^ (ρ.re - 1) / |ρ.im|) * (a * h) +
          ((x + h) * x ^ (ρ.re - 1) / |ρ.im|) * (a * h) := add_le_add hsecond hfirst
      _ = _ := by ring
  have hden : 0 < a * b * h := mul_pos (mul_pos ha hb) hh
  unfold trapezoidKernel
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]
  calc
    _ ≤ (2 * ((x + h) * x ^ (ρ.re - 1) / |ρ.im|) * (a * h)) / (a * b * h) :=
      div_le_div_of_nonneg_right hnum hden.le
    _ = _ := by field_simp

/-- Pointwise quadratic-height bound for the actual primitive before differencing. -/
theorem zeroPrimitive_norm_le {x Y t : ℝ} {ρ : ℂ}
    (hx : 0 < x) (hxt : x ≤ t) (htY : t ≤ Y) (hre : ρ.re ≤ 1) (him : ρ.im ≠ 0) :
    ‖zeroPrimitive ρ t‖ ≤ Y ^ 2 * x ^ (ρ.re - 1) / |ρ.im| ^ 2 := by
  have ht := hx.trans_le hxt
  have hg : 0 < |ρ.im| := abs_pos.mpr him
  have hnum : t ^ (ρ.re + 1) ≤ Y ^ 2 * x ^ (ρ.re - 1) := by
    have he : ρ.re + 1 = ρ.re - 1 + (2 : ℕ) := by norm_num; ring
    rw [he]
    simpa only [mul_comm] using rpow_shift_bound hx hxt htY (show ρ.re - 1 ≤ 0 by linarith) 2
  have hden : |ρ.im| ^ 2 ≤ ‖ρ‖ * ‖ρ + 1‖ := by
    have h1 : |ρ.im| ≤ ‖ρ + 1‖ := by simpa using Complex.abs_im_le_norm (ρ + 1)
    simpa only [pow_two] using
      mul_le_mul (Complex.abs_im_le_norm ρ) h1 (abs_nonneg _) (norm_nonneg _)
  rw [zeroPrimitive, norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.add_re, Complex.one_re]
  calc
    _ ≤ t ^ (ρ.re + 1) / |ρ.im| ^ 2 := div_le_div_of_nonneg_left
      (Real.rpow_nonneg ht.le _) (sq_pos_of_pos hg) hden
    _ ≤ _ := div_le_div_of_nonneg_right hnum (sq_nonneg _)

/-- Second decay bound, using the four-value triangle inequality. -/
theorem norm_trapezoidKernel_le_second {x h a b : ℝ} {ρ : ℂ}
    (hx : 0 < x) (hh : 0 < h) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (hre : ρ.re ≤ 1) (him : ρ.im ≠ 0) :
    ‖trapezoidKernel x h a b ρ‖ ≤
      h * x ^ (ρ.re - 1) * ((4 / (a * b)) * ((x + h) / h) ^ 2 / |ρ.im| ^ 2) := by
  have hah : 0 < a * h := mul_pos ha hh
  have hbh : 0 < b * h := mul_pos hb hh
  have habh : a * h + b * h = h := by nlinarith [hab]
  let C := (x + h) ^ 2 * x ^ (ρ.re - 1) / |ρ.im| ^ 2
  have h0 : ‖zeroPrimitive ρ x‖ ≤ C :=
    zeroPrimitive_norm_le hx (le_refl x) (by linarith) hre him
  have h1 : ‖zeroPrimitive ρ (x + a * h)‖ ≤ C :=
    zeroPrimitive_norm_le hx (by linarith) (by linarith) hre him
  have h2 : ‖zeroPrimitive ρ (x + b * h)‖ ≤ C :=
    zeroPrimitive_norm_le hx (by linarith) (by linarith) hre him
  have h3 : ‖zeroPrimitive ρ (x + h)‖ ≤ C :=
    zeroPrimitive_norm_le hx (by linarith) (le_refl (x + h)) hre him
  have hnum : ‖zeroPrimitive ρ x - zeroPrimitive ρ (x + a * h) -
      zeroPrimitive ρ (x + b * h) + zeroPrimitive ρ (x + h)‖ ≤ 4 * C := by
    calc
      _ ≤ ‖zeroPrimitive ρ x - zeroPrimitive ρ (x + a * h) - zeroPrimitive ρ (x + b * h)‖ +
          ‖zeroPrimitive ρ (x + h)‖ := norm_add_le _ _
      _ ≤ (‖zeroPrimitive ρ x - zeroPrimitive ρ (x + a * h)‖ +
          ‖zeroPrimitive ρ (x + b * h)‖) + ‖zeroPrimitive ρ (x + h)‖ :=
        by
          have ht := norm_sub_le (zeroPrimitive ρ x - zeroPrimitive ρ (x + a * h))
            (zeroPrimitive ρ (x + b * h))
          linarith only [ht]
      _ ≤ ((‖zeroPrimitive ρ x‖ + ‖zeroPrimitive ρ (x + a * h)‖) +
          ‖zeroPrimitive ρ (x + b * h)‖) + ‖zeroPrimitive ρ (x + h)‖ :=
        by
          have ht := norm_sub_le (zeroPrimitive ρ x) (zeroPrimitive ρ (x + a * h))
          linarith only [ht]
      _ ≤ 4 * C := by linarith
  have hden : 0 < a * b * h := mul_pos (mul_pos ha hb) hh
  unfold trapezoidKernel
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]
  calc
    _ ≤ (4 * C) / (a * b * h) := div_le_div_of_nonneg_right hnum hden.le
    _ = _ := by dsimp [C]; field_simp

/-- The three bounds combined, in the same minimum order as the certificate kernel. -/
theorem norm_trapezoidKernel_le_min {x h a b : ℝ} {ρ : ℂ}
    (hx : 0 < x) (hh : 0 < h) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (hρ : ρ ≠ 0) (hρ1 : ρ + 1 ≠ 0)
    (hre : ρ.re ≤ 1) (him : ρ.im ≠ 0) :
    ‖trapezoidKernel x h a b ρ‖ ≤ h * x ^ (ρ.re - 1) *
      min (min 1 ((2 / b) * ((x + h) / h) / |ρ.im|))
        ((4 / (a * b)) * ((x + h) / h) ^ 2 / |ρ.im| ^ 2) := by
  have hc : 0 ≤ h * x ^ (ρ.re - 1) := mul_nonneg hh.le (Real.rpow_nonneg hx.le _)
  rw [mul_min_of_nonneg _ _ hc, mul_min_of_nonneg _ _ hc, mul_one]
  exact le_min (le_min (norm_trapezoidKernel_le_base hx hh ha hb hab hρ hρ1 hre)
    (norm_trapezoidKernel_le_first hx hh ha hb hab hρ1 hre him))
    (norm_trapezoidKernel_le_second hx hh ha hb hab hre him)

end LegendreK6
