import LegendreK6.TrapezoidZeroBound
import LegendreK6.DensityGridGrowth
import LegendreK6.GeometricHeightTail

/-!
# Actual positive-height sums, finite grids, and their geometric residual

Every cumulative weight below is the actual multiplicity-weighted zeta-zero
sum. QRH, the original CS rows and Rosser are the only literature inputs.
All remaining hypotheses describe finite grids or ordinary real parameters.
-/

namespace LegendreK6

open scoped BigOperators

theorem sigma_grid_range_of_rows (s : ℕ → ℝ) (row : ℕ → Fin 12) (n : ℕ)
    (hrows : ∀ j < n, (16 + ((row j).val : ℝ))/32 ≤ s j ∧
      s j ≤ (17 + ((row j).val : ℝ))/32) :
    ∀ j < n, 1/2 ≤ s j ∧ s j ≤ 7/8 := by
  intro j hj
  obtain ⟨hlo, hhi⟩ := hrows j hj
  have hi : (row j).val ≤ 11 := by have := (row j).isLt; omega
  have hi' : ((row j).val : ℝ) ≤ 11 := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ (row j).val := Nat.cast_nonneg _
  constructor <;> linarith

/-- The full quadratic residual of any actual finite zero cutoff, including
all lower heights, is bounded using the original density input and a geometric grid. -/
theorem positive_zero_quadratic_residual_le
    (HQ : QRHSevenEighths) (HC : CSv2) (HR : RosserZeroCount)
    (s : ℕ → ℝ) (row : ℕ → Fin 12) (n : ℕ) (A U q T : ℝ)
    (hA : 0 ≤ A) (hs : Monotone s) (hs0 : s 0 = 1/2) (hsn : 7/8 ≤ s n)
    (hrows : ∀ j < n, (16 + ((row j).val : ℝ))/32 ≤ s j ∧
      s j ≤ (17 + ((row j).val : ℝ))/32)
    (hU : 6 ≤ U) (hUH : 3000000000000 ≤ Real.exp U) :
    (∑ ρ ∈ positiveZetaZeros T,
      ((zetaMultiplicity ρ : ℝ) * Real.exp ((ρ.re - 1) * A)) *
        (((4096 : ℝ)/31) * q^2 / (max ρ.im (Real.exp U))^2)) ≤
      16 * (((4096 : ℝ)/31) * q^2) * Real.exp (-2*U) * densityGridPhi s row n A U := by
  have hσ := sigma_grid_range_of_rows s row n hrows
  have hB := densityGridPhi_nonneg s row n A U hs hA (by linarith)
  have hcount : ∀ k : ℕ,
      (∑ ρ ∈ positiveZetaZeros T,
        if ρ.im ≤ Real.exp U * (4 : ℝ)^(k+1) then
          (zetaMultiplicity ρ : ℝ) * Real.exp ((ρ.re - 1) * A) else 0) ≤
        densityGridPhi s row n A U * (8 : ℝ)^(k+1) := by
    intro k
    have hv : 0 ≤ ((k+1 : ℕ) : ℝ) * Real.log 4 :=
      mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
    have hheight : 3000000000000 ≤ Real.exp (U + ((k+1 : ℕ) : ℝ) * Real.log 4) :=
      hUH.trans (Real.exp_le_exp.mpr (by linarith))
    calc
      _ ≤ positiveZeroWeight A (Real.exp U * (4 : ℝ)^(k+1)) :=
        positiveZeroWeight_prefix_le A T _
      _ = positiveZeroWeight A (Real.exp (U + ((k+1 : ℕ) : ℝ) * Real.log 4)) := by
        rw [exp_nat_log_four]
      _ ≤ densityGridPhi s row n A (U + ((k+1 : ℕ) : ℝ) * Real.log 4) :=
        positiveZeroWeight_le_gridPhi HQ HC HR s row n A _ hA hs hs0 hsn hrows hheight (by linarith)
      _ ≤ _ := densityGridPhi_geometric_le s row n A U (k+1) hs hA hσ hU
  have ht := finite_quadratic_residual_bound (positiveZetaZeros T) Complex.im
    (fun ρ => (zetaMultiplicity ρ : ℝ) * Real.exp ((ρ.re - 1) * A))
    (Real.exp U) (((4096 : ℝ)/31) * q^2) (densityGridPhi s row n A U) T
    (Real.exp_pos U) (by positivity) hB
    (fun ρ _ => mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _))
    (fun ρ hρ => (mem_positiveZetaZeros.mp hρ).2.2.2.2) hcount
  calc
    _ ≤ 16 * ((((4096 : ℝ)/31) * q^2) / (Real.exp U)^2) * densityGridPhi s row n A U := ht
    _ = _ := by
      have he : (Real.exp U)^2 = Real.exp (2*U) := by
        simpa using (Real.exp_nat_mul U 2).symm
      rw [he, div_eq_mul_inv, ← Real.exp_neg]
      simp only [neg_mul]
      ring

/-- Explicit positive-height budget for a finite logarithmic grid and its full residual. -/
noncomputable def trapezoidHeightBudget (s : ℕ → ℝ) (row : ℕ → Fin 12) (nSigma : ℕ)
    (A q : ℝ) (u : ℕ → ℝ) (nHeight : ℕ) : ℝ :=
  (∑ j ∈ Finset.range nHeight,
    (trapezoidHeightKernel q (Real.exp (u j)) -
      trapezoidHeightKernel q (Real.exp (u (j+1)))) * densityGridPhi s row nSigma A (u (j+1))) +
    16 * (((4096 : ℝ)/31) * q^2) * Real.exp (-2 * u nHeight) *
      densityGridPhi s row nSigma A (u nHeight)

/-- Finite height masses and the geometric residual bound the actual positive-height sum. -/
theorem positive_zero_envelope_le_heightBudget
    (HQ : QRHSevenEighths) (HC : CSv2) (HR : RosserZeroCount)
    (s : ℕ → ℝ) (row : ℕ → Fin 12) (nSigma : ℕ)
    (A q T : ℝ) (u : ℕ → ℝ) (nHeight : ℕ)
    (hA : 0 ≤ A) (hq : 0 ≤ q) (hs : Monotone s)
    (hs0 : s 0 = 1/2) (hsn : 7/8 ≤ s nSigma)
    (hrows : ∀ j < nSigma, (16 + ((row j).val : ℝ))/32 ≤ s j ∧
      s j ≤ (17 + ((row j).val : ℝ))/32)
    (hu : Monotone u) (huH : 3000000000000 ≤ Real.exp (u 0)) (hu1 : 1 ≤ u 0)
    (hU : 6 ≤ u nHeight) (hstart : trapezoidHeightKernel q (Real.exp (u 0)) = 1) :
    (∑ ρ ∈ positiveZetaZeros T,
      (zetaMultiplicity ρ : ℝ) * Real.exp ((ρ.re - 1) * A) * trapezoidHeightKernel q ρ.im) ≤
        trapezoidHeightBudget s row nSigma A q u nHeight := by
  have hue : Monotone (fun j => Real.exp (u j)) := by
    intro i j hij
    exact Real.exp_le_exp.mpr (hu hij)
  have hw : ∀ ρ ∈ positiveZetaZeros T,
      0 ≤ (zetaMultiplicity ρ : ℝ) * Real.exp ((ρ.re - 1) * A) := by
    intro ρ _
    exact mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hh := finite_sum_kernel_le_height_grid (positiveZetaZeros T) Complex.im
    (fun ρ => (zetaMultiplicity ρ : ℝ) * Real.exp ((ρ.re - 1) * A))
    (trapezoidHeightKernel q) (fun j => Real.exp (u j)) nHeight hw
    (fun ρ hρ => (mem_positiveZetaZeros.mp hρ).2.2.2.1)
    (trapezoidHeightKernel_antitone hq) (fun t _ => trapezoidHeightKernel_le_one q t)
    hue (Real.exp_pos _) hstart
  apply hh.trans
  unfold trapezoidHeightBudget
  apply add_le_add
  · apply Finset.sum_le_sum
    intro j _
    have hnode0 : u 0 ≤ u (j+1) := hu (Nat.zero_le _)
    have hp := positiveZeroWeight_le_gridPhi HQ HC HR s row nSigma A (u (j+1))
      hA hs hs0 hsn hrows (huH.trans (Real.exp_le_exp.mpr hnode0)) (hu1.trans hnode0)
    have hc := (positiveZeroWeight_prefix_le A T (Real.exp (u (j+1)))).trans hp
    have hmass : 0 ≤ trapezoidHeightKernel q (Real.exp (u j)) -
        trapezoidHeightKernel q (Real.exp (u (j+1))) := by
      apply sub_nonneg.mpr
      exact trapezoidHeightKernel_antitone hq (Real.exp_pos _) (Real.exp_pos _) (hue (Nat.le_succ j))
    exact mul_le_mul_of_nonneg_left hc hmass
  · calc
      _ ≤ ∑ ρ ∈ positiveZetaZeros T,
          ((zetaMultiplicity ρ : ℝ) * Real.exp ((ρ.re - 1) * A)) *
            (((4096 : ℝ)/31) * q^2 / (max ρ.im (Real.exp (u nHeight)))^2) := by
        apply Finset.sum_le_sum
        intro ρ hρ
        exact mul_le_mul_of_nonneg_left (trapezoidHeightKernel_le_quadratic q _) (hw ρ hρ)
      _ ≤ _ := positive_zero_quadratic_residual_le HQ HC HR s row nSigma A (u nHeight) q T
        hA hs hs0 hsn hrows hU (huH.trans (hue (Nat.zero_le _)))

/-- Full actual truncated-zero bound with only the named literature inputs and numerical grid obligations. -/
theorem norm_truncatedTrapezoidZeroSum_le_heightBudget
    (HQ : QRHSevenEighths) (HC : CSv2) (HR : RosserZeroCount)
    (s : ℕ → ℝ) (row : ℕ → Fin 12) (nSigma : ℕ)
    (L A h q T : ℝ) (u : ℕ → ℝ) (nHeight : ℕ)
    (hh : 0 < h) (hA : 0 ≤ A) (hAL : A ≤ L) (hq : 0 ≤ q)
    (hqq : (Real.exp L + h) / h ≤ q) (hs : Monotone s)
    (hs0 : s 0 = 1/2) (hsn : 7/8 ≤ s nSigma)
    (hrows : ∀ j < nSigma, (16 + ((row j).val : ℝ))/32 ≤ s j ∧
      s j ≤ (17 + ((row j).val : ℝ))/32)
    (hu : Monotone u) (huH : 3000000000000 ≤ Real.exp (u 0)) (hu1 : 1 ≤ u 0)
    (hU : 6 ≤ u nHeight) (hstart : trapezoidHeightKernel q (Real.exp (u 0)) = 1) :
    ‖truncatedTrapezoidZeroSum (Real.exp L) h (1/32) (31/32) T‖ ≤
      h * (2 * trapezoidHeightBudget s row nSigma A q u nHeight) := by
  have hp := positive_zero_envelope_le_heightBudget HQ HC HR s row nSigma A q T u nHeight
    hA hq hs hs0 hsn hrows hu huH hu1 hU hstart
  calc
    _ ≤ 2 * h * ∑ ρ ∈ positiveZetaZeros T,
        (zetaMultiplicity ρ : ℝ) * Real.exp ((ρ.re - 1) * A) * trapezoidHeightKernel q ρ.im :=
      norm_truncatedTrapezoidZeroSum_le_envelope L A h q T hh hAL hq hqq
    _ ≤ 2 * h * trapezoidHeightBudget s row nSigma A q u nHeight :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

end LegendreK6
