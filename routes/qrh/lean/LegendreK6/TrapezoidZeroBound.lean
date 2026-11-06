import LegendreK6.IntegratedExplicitFormula
import LegendreK6.HeightGrid

/-!
# The actual truncated zero sum is controlled by the common height envelope

The interval and parameter comparisons are proved before summing over the
actual zeta zeros. Conjugation and multiplicities are handled by the proved
zeta interface; no zero-density or prime-existence statement is an input.
-/

namespace LegendreK6

open scoped BigOperators

theorem trapezoidHeightKernel_mono_q {q Q T : ℝ}
    (hq : 0 ≤ q) (hqQ : q ≤ Q) (hT : 0 < T) :
    trapezoidHeightKernel q T ≤ trapezoidHeightKernel Q T := by
  unfold trapezoidHeightKernel
  apply min_le_min le_rfl
  apply min_le_min
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hqQ (by norm_num)) hT.le
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hq (hq.trans hqQ)).mpr hqQ) (by norm_num))
      (sq_nonneg T)

/-- Uniform single-zero envelope over a cell `A ≤ L`, with an upper choice of `q`. -/
theorem norm_trapezoidKernel_le_common_envelope (ρ : NontrivialZero)
    {L A h qplus : ℝ} (hh : 0 < h) (hAL : A ≤ L)
    (_hqplus : 0 ≤ qplus) (hqq : (Real.exp L + h) / h ≤ qplus) :
    ‖trapezoidKernel (Real.exp L) h (1/32) (31/32) ρ.1‖ ≤
      h * Real.exp ((ρ.1.re - 1) * A) * trapezoidHeightKernel qplus |ρ.1.im| := by
  have hx : 0 < Real.exp L := Real.exp_pos L
  have hre : ρ.1.re ≤ 1 := ρ.2.2.2.le
  have him : ρ.1.im ≠ 0 := nontrivialZero_im_ne_zero ρ
  have hρ1 : ρ.1 + 1 ≠ 0 := by
    intro heq
    have he := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at he
    linarith [ρ.2.2.1]
  have h0 := norm_trapezoidKernel_le_min hx hh (by norm_num : (0 : ℝ) < 1/32)
    (by norm_num : (0 : ℝ) < 31/32) (by norm_num : (1/32 : ℝ) + 31/32 = 1)
    (nontrivialZero_ne_zero ρ) hρ1 hre him
  have h0' : ‖trapezoidKernel (Real.exp L) h (1/32) (31/32) ρ.1‖ ≤
      h * (Real.exp L) ^ (ρ.1.re - 1) *
        trapezoidHeightKernel ((Real.exp L + h) / h) |ρ.1.im| := by
    convert h0 using 1; norm_num [trapezoidHeightKernel, min_assoc]
  have hT : 0 < |ρ.1.im| := abs_pos.mpr him
  have hq : 0 ≤ (Real.exp L + h) / h := (div_pos (add_pos hx hh) hh).le
  have hk := trapezoidHeightKernel_mono_q hq hqq hT
  have he : (Real.exp L) ^ (ρ.1.re - 1) ≤ Real.exp ((ρ.1.re - 1) * A) := by
    rw [← Real.exp_mul]
    apply Real.exp_le_exp.mpr
    have ht := mul_le_mul_of_nonpos_left hAL (show ρ.1.re - 1 ≤ 0 by linarith)
    simpa only [mul_comm] using ht
  exact h0'.trans (mul_le_mul (mul_le_mul_of_nonneg_left he hh.le) hk
    (trapezoidHeightKernel_nonneg hq hT) (mul_nonneg hh.le (Real.exp_nonneg _)))

/-- The actual finite zero sum is bounded by the positive-height envelope with multiplicity.
The factor of two uses the proved conjugation and real-axis nonvanishing theorems. -/
theorem norm_truncatedTrapezoidZeroSum_le_envelope
    (L A h qplus T : ℝ) (hh : 0 < h) (hAL : A ≤ L)
    (hqplus : 0 ≤ qplus) (hqq : (Real.exp L + h) / h ≤ qplus) :
    ‖truncatedTrapezoidZeroSum (Real.exp L) h (1/32) (31/32) T‖ ≤
      2 * h * ∑ ρ ∈ positiveZetaZeros T,
        (zetaMultiplicity ρ : ℝ) * Real.exp ((ρ.re - 1) * A) *
          trapezoidHeightKernel qplus ρ.im := by
  let f : ℂ → ℝ := fun ρ => Real.exp ((ρ.re - 1) * A) * trapezoidHeightKernel qplus |ρ.im|
  have hf : ∀ ρ : ℂ, f ((starRingEnd ℂ) ρ) = f ρ := by
    intro ρ
    simp [f]
  have hsum := sum_allZetaZeros_eq_twice T f hf
  have hpos : (∑ ρ ∈ positiveZetaZeros T, (zetaMultiplicity ρ : ℝ) * f ρ) =
      ∑ ρ ∈ positiveZetaZeros T,
        (zetaMultiplicity ρ : ℝ) * Real.exp ((ρ.re - 1) * A) *
          trapezoidHeightKernel qplus ρ.im := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    dsimp [f]
    rw [abs_of_pos (mem_positiveZetaZeros.mp hρ).2.2.2.1]
    ring
  calc
    _ ≤ ∑ ρ ∈ allZetaZeros T,
        ‖(zetaMultiplicity ρ : ℂ) * trapezoidKernel (Real.exp L) h (1/32) (31/32) ρ‖ :=
      norm_sum_le _ _
    _ ≤ ∑ ρ ∈ allZetaZeros T, (zetaMultiplicity ρ : ℝ) * (h * f ρ) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      obtain ⟨hz, hre0, hre1, _⟩ := mem_allZetaZeros.mp hρ
      have hp := norm_trapezoidKernel_le_common_envelope ⟨ρ, hz, hre0, hre1⟩ hh hAL hqplus hqq
      rw [norm_mul, Complex.norm_natCast]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      simpa only [f, mul_assoc] using hp
    _ = h * ∑ ρ ∈ allZetaZeros T, (zetaMultiplicity ρ : ℝ) * f ρ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ _
      ring
    _ = _ := by rw [hsum, hpos]; ring

/-- A prefix of an arbitrary finite cutoff is contained in the actual prefix at the new height.
No order between the two cutoffs is needed. -/
theorem positiveZeroWeight_prefix_le (A T v : ℝ) :
    (∑ ρ ∈ positiveZetaZeros T, if ρ.im ≤ v then
      (zetaMultiplicity ρ : ℝ) * Real.exp ((ρ.re - 1) * A) else 0) ≤
        positiveZeroWeight A v := by
  classical
  rw [← Finset.sum_filter]
  unfold positiveZeroWeight
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ρ hρ
    obtain ⟨hT, hv⟩ := Finset.mem_filter.mp hρ
    obtain ⟨hz, hre0, hre1, him0, _⟩ := mem_positiveZetaZeros.mp hT
    exact mem_positiveZetaZeros.mpr ⟨hz, hre0, hre1, him0, hv⟩
  · intro ρ _ _
    exact mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)

end LegendreK6
