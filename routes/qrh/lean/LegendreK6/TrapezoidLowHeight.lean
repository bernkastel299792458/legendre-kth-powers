import LegendreK6.FiniteRHInput
import LegendreK6.TrapezoidHeightBound

/-! Reuse a height grid at a larger reference q after separating the actual
low zeros. The finite RH premise applies only to the closed cutoff 3e12.
The remaining estimates follow from the existing real kernel and zero sums. -/

namespace LegendreK6

open scoped BigOperators

/-- Scaling below the linear cutoff controls all three pieces of the minimum. -/
theorem trapezoidHeightKernel_scale_le (q Q r t : ℝ)
    (hq : 0 ≤ q) (hr : 0 ≤ r) (hr1 : r ≤ 1) (ht : 0 < t)
    (hqQ : q ≤ r*Q) (hlinear : (64/31 : ℝ)*q/t ≤ r) :
    trapezoidHeightKernel q t ≤ r * trapezoidHeightKernel Q t := by
  have hl : trapezoidHeightKernel q t ≤ (64/31 : ℝ)*q/t :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hlin : (64/31 : ℝ)*q/t ≤ r*((64/31 : ℝ)*Q/t) := by
    calc
      _ ≤ (64/31 : ℝ)*(r*Q)/t :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hqQ (by norm_num)) ht.le
      _ = _ := by ring
  have hsq : q^2 ≤ r*Q^2 := by
    calc
      q^2 ≤ (r*Q)^2 := pow_le_pow_left₀ hq hqQ 2
      _ = r^2*Q^2 := mul_pow r Q 2
      _ ≤ r*Q^2 := mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg Q)
  have hquad : (4096/31 : ℝ)*q^2/t^2 ≤ r*((4096/31 : ℝ)*Q^2/t^2) := by
    calc
      _ ≤ (4096/31 : ℝ)*(r*Q^2)/t^2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsq (by norm_num)) (sq_nonneg t)
      _ = _ := by ring
  unfold trapezoidHeightKernel at ⊢
  rw [mul_min_of_nonneg _ _ hr, mul_one, mul_min_of_nonneg _ _ hr]
  exact le_min (hl.trans hlinear) (le_min (hl.trans hlin)
    ((trapezoidHeightKernel_le_quadratic q t).trans hquad))

/-- A common linear threshold at H applies to every height above H. -/
theorem trapezoidHeightKernel_scale_above_finiteRH (q Q r t : ℝ)
    (hq : 0 ≤ q) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hqQ : q ≤ r*Q) (hlinear : (64/31 : ℝ)*q/3000000000000 ≤ r)
    (ht : 3000000000000 ≤ t) :
    trapezoidHeightKernel q t ≤ r * trapezoidHeightKernel Q t := by
  apply trapezoidHeightKernel_scale_le q Q r t hq hr hr1 (by linarith) hqQ
  exact (div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hq)
    (by norm_num : (0 : ℝ) < 3000000000000) ht).trans hlinear

/-- All low-height zeros retain their actual analytic multiplicities. The high
part is enlarged to the whole reference-q sum, using nonnegative weights. -/
theorem positive_zero_envelope_le_scaled
    (HF : FiniteRH3e12) (HR : RosserZeroCount) (A q Q r T : ℝ)
    (hq : 0 ≤ q) (hQ : 0 ≤ Q) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hqQ : q ≤ r*Q) (hlinear : (64/31 : ℝ)*q/3000000000000 ≤ r) :
    (∑ ρ ∈ positiveZetaZeros T,
      (zetaMultiplicity ρ : ℝ)*Real.exp ((ρ.re-1)*A)*trapezoidHeightKernel q ρ.im) ≤
      Real.exp (-A/2)*3000000000000*Real.log 3000000000000 +
        r * ∑ ρ ∈ positiveZetaZeros T,
          (zetaMultiplicity ρ : ℝ)*Real.exp ((ρ.re-1)*A)*trapezoidHeightKernel Q ρ.im := by
  classical
  let w : ℂ → ℝ := fun ρ => (zetaMultiplicity ρ : ℝ)*Real.exp ((ρ.re-1)*A)
  have hw (ρ : ℂ) : 0 ≤ w ρ := mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hp (ρ : ℂ) (hρ : ρ ∈ positiveZetaZeros T) :
      w ρ * trapezoidHeightKernel q ρ.im ≤
        (if ρ.im ≤ 3000000000000 then w ρ else 0) +
          r*(w ρ * trapezoidHeightKernel Q ρ.im) := by
    have him := (mem_positiveZetaZeros.mp hρ).2.2.2.1
    by_cases hlow : ρ.im ≤ 3000000000000
    · rw [ite_eq_left hlow]
      have hh := mul_le_mul_of_nonneg_left (trapezoidHeightKernel_le_one q ρ.im) (hw ρ)
      have hnon := mul_nonneg hr (mul_nonneg (hw ρ) (trapezoidHeightKernel_nonneg hQ him))
      nlinarith only [hh, hnon]
    · rw [ite_eq_right hlow, zero_add]
      have hk := trapezoidHeightKernel_scale_above_finiteRH q Q r ρ.im hq hr hr1
        hqQ hlinear (le_of_not_ge hlow)
      simpa only [mul_assoc, mul_left_comm] using mul_le_mul_of_nonneg_left hk (hw ρ)
  calc
    _ ≤ ∑ ρ ∈ positiveZetaZeros T,
        ((if ρ.im ≤ 3000000000000 then w ρ else 0) +
          r*(w ρ * trapezoidHeightKernel Q ρ.im)) := Finset.sum_le_sum hp
    _ = (∑ ρ ∈ positiveZetaZeros T, if ρ.im ≤ 3000000000000 then w ρ else 0) +
        r * ∑ ρ ∈ positiveZetaZeros T, w ρ * trapezoidHeightKernel Q ρ.im := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := add_le_add (positiveZeroWeight_prefix_finiteRH_le HF HR A T) le_rfl

/-- Reuse the complete reference-q height budget, including its geometric tail. -/
theorem positive_zero_envelope_le_scaled_heightBudget
    (HQ : QRHSevenEighths) (HC : CSv2) (HR : RosserZeroCount) (HF : FiniteRH3e12)
    (s : ℕ → ℝ) (row : ℕ → Fin 12) (nSigma : ℕ)
    (A q Q r T : ℝ) (u : ℕ → ℝ) (nHeight : ℕ)
    (hA : 0 ≤ A) (hq : 0 ≤ q) (hQ : 0 ≤ Q) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hqQ : q ≤ r*Q) (hlinear : (64/31 : ℝ)*q/3000000000000 ≤ r)
    (hs : Monotone s) (hs0 : s 0 = 1/2) (hsn : 7/8 ≤ s nSigma)
    (hrows : ∀ j < nSigma, (16+((row j).val:ℝ))/32 ≤ s j ∧
      s j ≤ (17+((row j).val:ℝ))/32)
    (hu : Monotone u) (huH : 3000000000000 ≤ Real.exp (u 0)) (hu1 : 1 ≤ u 0)
    (hU : 6 ≤ u nHeight) (hstart : trapezoidHeightKernel Q (Real.exp (u 0)) = 1) :
    (∑ ρ ∈ positiveZetaZeros T,
      (zetaMultiplicity ρ : ℝ)*Real.exp ((ρ.re-1)*A)*trapezoidHeightKernel q ρ.im) ≤
      Real.exp (-A/2)*3000000000000*Real.log 3000000000000 +
        r * trapezoidHeightBudget s row nSigma A Q u nHeight := by
  apply (positive_zero_envelope_le_scaled HF HR A q Q r T hq hQ hr hr1 hqQ hlinear).trans
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left
    (positive_zero_envelope_le_heightBudget HQ HC HR s row nSigma A Q T u nHeight
      hA hQ hs hs0 hsn hrows hu huH hu1 hU hstart) hr

/-- The actual truncated zero sum, ready for the unchanged prime criterion. -/
theorem norm_truncatedTrapezoidZeroSum_le_scaled_heightBudget
    (HQ : QRHSevenEighths) (HC : CSv2) (HR : RosserZeroCount) (HF : FiniteRH3e12)
    (s : ℕ → ℝ) (row : ℕ → Fin 12) (nSigma : ℕ)
    (L A h q Q r T : ℝ) (u : ℕ → ℝ) (nHeight : ℕ)
    (hh : 0 < h) (hA : 0 ≤ A) (hAL : A ≤ L)
    (hq : 0 ≤ q) (hQ : 0 ≤ Q) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hqq : (Real.exp L+h)/h ≤ q) (hqQ : q ≤ r*Q)
    (hlinear : (64/31 : ℝ)*q/3000000000000 ≤ r)
    (hs : Monotone s) (hs0 : s 0 = 1/2) (hsn : 7/8 ≤ s nSigma)
    (hrows : ∀ j < nSigma, (16+((row j).val:ℝ))/32 ≤ s j ∧
      s j ≤ (17+((row j).val:ℝ))/32)
    (hu : Monotone u) (huH : 3000000000000 ≤ Real.exp (u 0)) (hu1 : 1 ≤ u 0)
    (hU : 6 ≤ u nHeight) (hstart : trapezoidHeightKernel Q (Real.exp (u 0)) = 1) :
    ‖truncatedTrapezoidZeroSum (Real.exp L) h (1/32) (31/32) T‖ ≤
      h * (2*Real.exp (-A/2)*3000000000000*Real.log 3000000000000 +
        2*r*trapezoidHeightBudget s row nSigma A Q u nHeight) := by
  have hp := positive_zero_envelope_le_scaled_heightBudget HQ HC HR HF s row nSigma
    A q Q r T u nHeight hA hq hQ hr hr1 hqQ hlinear hs hs0 hsn hrows hu huH hu1 hU hstart
  calc
    _ ≤ 2*h*∑ ρ ∈ positiveZetaZeros T,
        (zetaMultiplicity ρ : ℝ)*Real.exp ((ρ.re-1)*A)*trapezoidHeightKernel q ρ.im :=
      norm_truncatedTrapezoidZeroSum_le_envelope L A h q T hh hAL hq hqq
    _ ≤ 2*h*(Real.exp (-A/2)*3000000000000*Real.log 3000000000000 +
        r*trapezoidHeightBudget s row nSigma A Q u nHeight) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

end LegendreK6
