import LegendreK6.DensityInput
import LegendreK6.FiniteZeroLayer
import LegendreK6.TailDomains

/-!
# The three density terms of the infinite tail

The sums below count the actual positive-height zeta zeros with their true
analytic multiplicities. QRH and the exact CS v2 table are explicit inputs.
The total zero count is a separate scalar hypothesis to be discharged from
the named total-count literature input at assembly time.
-/

namespace LegendreK6

open scoped BigOperators
open MeasureTheory

theorem zeta_finiteLayerCount_eq (σ U : ℝ) :
    finiteLayerCount (positiveZetaZeros U) Complex.re zetaMultiplicity σ =
      (densityZeroCount σ U : ℝ) := by
  rw [finiteLayerCount_eq_cast_sum_filter]
  rfl

/-- The finite layer theorem instantiated with the actual positive-height zeros. -/
theorem positive_zero_exp_layer (H : QRHSevenEighths) (L U : ℝ) (hL : 0 ≤ L) :
    (∑ ρ ∈ positiveZetaZeros U, (zetaMultiplicity ρ : ℝ) *
      Real.exp ((ρ.re - 1) * L)) ≤
      (totalZeroCount U : ℝ) * Real.exp (-3 * L / 8) +
      ∫ σ in (5 / 8 : ℝ)..(7 / 8 : ℝ),
        L * Real.exp ((σ - 1) * L) * (densityZeroCount σ U : ℝ) := by
  have hβ : ∀ ρ ∈ positiveZetaZeros U, ρ.re ≤ (7 / 8 : ℝ) := by
    intro ρ hρ
    obtain ⟨hz, hre0, hre1, _, _⟩ := mem_positiveZetaZeros.mp hρ
    exact H ⟨ρ, hz, hre0, hre1⟩
  have hh := finite_exp_layer_bound (positiveZetaZeros U) Complex.re zetaMultiplicity
    hL (show (5 / 8 : ℝ) ≤ 7 / 8 by norm_num) hβ
  simp only [zeta_finiteLayerCount_eq] at hh
  have hc : (∑ ρ ∈ positiveZetaZeros U, (zetaMultiplicity ρ : ℝ)) =
      (totalZeroCount U : ℝ) := by simp [totalZeroCount]
  rw [hc] at hh
  simpa only [show ((5 / 8 : ℝ) - 1) * L = -3 * L / 8 by ring] using hh

theorem density_exp_product {U : ℝ} (hU : 0 < U) (L σ : ℝ) :
    Real.exp ((σ - 1) * L) * U ^ ((8 / 3 : ℝ) * (1 - σ)) =
      Real.exp ((σ - 1) * (L - (8 / 3) * Real.log U)) := by
  rw [Real.rpow_def_of_pos hU, ← Real.exp_add]
  congr 1
  ring

/-- Exact integration of the two exponential pieces before dropping their
negative lower-endpoint contributions. -/
theorem integral_two_density_exponentials (C D L lam : ℝ) :
    (∫ σ in (5 / 8 : ℝ)..(7 / 8 : ℝ),
      C * (L / lam) * (lam * Real.exp ((σ - 1) * lam)) +
      D * (L * Real.exp ((σ - 1) * L))) =
      C * (L / lam) * (Real.exp (-lam / 8) - Real.exp (-3 * lam / 8)) +
      D * (Real.exp (-L / 8) - Real.exp (-3 * L / 8)) := by
  have hc : Continuous (fun σ => C * (L / lam) * (lam * Real.exp ((σ - 1) * lam))) := by
    fun_prop
  have hd : Continuous (fun σ => D * (L * Real.exp ((σ - 1) * L))) := by fun_prop
  rw [intervalIntegral.integral_add (hc.intervalIntegrable _ _) (hd.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul (C * (L / lam)), intervalIntegral.integral_const_mul D,
    exact_sigma_weight, exact_sigma_weight]
  rw [show ((7 / 8 : ℝ) - 1) * lam = -lam / 8 by ring,
    show ((5 / 8 : ℝ) - 1) * lam = -3 * lam / 8 by ring,
    show ((7 / 8 : ℝ) - 1) * L = -L / 8 by ring,
    show ((5 / 8 : ℝ) - 1) * L = -3 * L / 8 by ring]

/-- The elementary integral of the CS tail envelope, with lower endpoint
terms discarded only after their coefficient signs have been established. -/
theorem integral_cs_tail_envelope_le (L U : ℝ) (hL : 0 ≤ L)
    (hU : 0 < U) (hu : 0 ≤ Real.log U)
    (hlam : 0 < L - (8 / 3 : ℝ) * Real.log U) :
    (∫ σ in (5 / 8 : ℝ)..(7 / 8 : ℝ), L * Real.exp ((σ - 1) * L) *
      ((561 / 25 : ℝ) * U ^ ((8 / 3 : ℝ) * (1 - σ)) * (Real.log U) ^ 3 +
        (829 / 100 : ℝ) * (Real.log U) ^ 2 + 147 * Real.log U)) ≤
      (561 / 25 : ℝ) * (Real.log U) ^ 3 *
        (L / (L - (8 / 3) * Real.log U)) *
        Real.exp (-(L - (8 / 3) * Real.log U) / 8) +
      ((829 / 100 : ℝ) * (Real.log U) ^ 2 + 147 * Real.log U) * Real.exp (-L / 8) := by
  let C : ℝ := (561 / 25) * (Real.log U) ^ 3
  let D : ℝ := (829 / 100) * (Real.log U) ^ 2 + 147 * Real.log U
  let lam : ℝ := L - (8 / 3) * Real.log U
  have hlam0 : lam ≠ 0 := ne_of_gt hlam
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hCL : 0 ≤ C * (L / lam) := mul_nonneg hC (div_nonneg hL hlam.le)
  have heq (σ : ℝ) :
      L * Real.exp ((σ - 1) * L) *
        ((561 / 25 : ℝ) * U ^ ((8 / 3 : ℝ) * (1 - σ)) * (Real.log U) ^ 3 +
          (829 / 100 : ℝ) * (Real.log U) ^ 2 + 147 * Real.log U) =
      C * (L / lam) * (lam * Real.exp ((σ - 1) * lam)) +
        D * (L * Real.exp ((σ - 1) * L)) := by
    calc
      _ = C * L * (Real.exp ((σ - 1) * L) * U ^ ((8 / 3 : ℝ) * (1 - σ))) +
          D * (L * Real.exp ((σ - 1) * L)) := by dsimp [C, D]; ring
      _ = C * L * Real.exp ((σ - 1) * lam) +
          D * (L * Real.exp ((σ - 1) * L)) := by rw [density_exp_product hU]
      _ = _ := by
        rw [mul_assoc C (L / lam), ← mul_assoc (L / lam) lam,
          div_mul_cancel₀ _ hlam0]
        ring
  simp_rw [heq]
  rw [integral_two_density_exponentials]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (sub_le_self _ (Real.exp_nonneg _)) hCL)
    (mul_le_mul_of_nonneg_left (sub_le_self _ (Real.exp_nonneg _)) hD)

/-- The actual positive-height exponential sum, bounded from QRH, the exact
CS table, and an explicitly exposed total-count estimate. -/
theorem positive_zero_exp_bound (HQ : QRHSevenEighths) (HC : CSv2)
    (L U : ℝ) (hL : 0 ≤ L) (hU : 3000000000000 ≤ U)
    (hu : 1 ≤ Real.log U) (hlam : 0 < L - (8 / 3 : ℝ) * Real.log U)
    (hN : (totalZeroCount U : ℝ) ≤ U * Real.log U) :
    (∑ ρ ∈ positiveZetaZeros U, (zetaMultiplicity ρ : ℝ) *
      Real.exp ((ρ.re - 1) * L)) ≤
      U * Real.log U * Real.exp (-3 * L / 8) +
      (561 / 25 : ℝ) * (Real.log U) ^ 3 *
        (L / (L - (8 / 3) * Real.log U)) *
        Real.exp (-(L - (8 / 3) * Real.log U) / 8) +
      ((829 / 100 : ℝ) * (Real.log U) ^ 2 + 147 * Real.log U) * Real.exp (-L / 8) := by
  have hU0 : 0 < U := by linarith
  have hu0 : 0 ≤ Real.log U := by linarith
  have hfi : IntervalIntegrable
      (fun σ => L * Real.exp ((σ - 1) * L) * (densityZeroCount σ U : ℝ))
      volume (5 / 8) (7 / 8) := by
    simpa only [zeta_finiteLayerCount_eq] using
      intervalIntegrable_finite_exp_layer (positiveZetaZeros U) Complex.re
        zetaMultiplicity L (5 / 8) (7 / 8)
  have hgc : Continuous (fun σ => L * Real.exp ((σ - 1) * L) *
      ((561 / 25 : ℝ) * U ^ ((8 / 3 : ℝ) * (1 - σ)) * (Real.log U) ^ 3 +
        (829 / 100 : ℝ) * (Real.log U) ^ 2 + 147 * Real.log U)) := by
    fun_prop (disch := positivity)
  have hi := intervalIntegral.integral_mono_on (show (5 / 8 : ℝ) ≤ 7 / 8 by norm_num)
    hfi (hgc.intervalIntegrable (5 / 8) (7 / 8))
    (fun σ hσ => mul_le_mul_of_nonneg_left (cs_tail_density HC hσ.1 hσ.2 hU hu)
      (mul_nonneg hL (Real.exp_nonneg _)))
  have hb := mul_le_mul_of_nonneg_right hN (Real.exp_nonneg (-3 * L / 8))
  have hlayer := positive_zero_exp_layer HQ L U hL
  have henvelope := integral_cs_tail_envelope_le L U hL hU0 hu0 hlam
  linarith

theorem tail_lambda_eq_height (L : ℝ) :
    L - (8 / 3 : ℝ) * Real.log (tailHeight L) = tailLambda L := by
  rw [tail_log_height]
  unfold tailU tailLambda
  ring

/-- Equations (37)--(38): twice the actual positive-height weighted zero sum
is bounded by the first three terms of the previously verified tail function. -/
theorem tail_positive_zero_sum_bound (HQ : QRHSevenEighths) (HC : CSv2)
    (L : ℝ) (hL : 700 ≤ L)
    (hN : (totalZeroCount (tailHeight L) : ℝ) ≤
      tailHeight L * Real.log (tailHeight L)) :
    2 * (∑ ρ ∈ positiveZetaZeros (tailHeight L), (zetaMultiplicity ρ : ℝ) *
      Real.exp ((ρ.re - 1) * L)) ≤
      4 * tailU L * Real.exp (-3 * L / 32) +
      (1122 / 25 : ℝ) * (tailU L) ^ 3 * (L / tailLambda L) *
        Real.exp (-tailLambda L / 8) +
      2 * ((829 / 100 : ℝ) * (tailU L) ^ 2 + 147 * tailU L) * Real.exp (-L / 8) := by
  have hu : 1 ≤ Real.log (tailHeight L) := by
    rw [tail_log_height]
    exact (tail_U_gt_one L hL).le
  have hlam : 0 < L - (8 / 3 : ℝ) * Real.log (tailHeight L) := by
    rw [tail_lambda_eq_height]
    exact tail_lambda_pos L hL
  have h := positive_zero_exp_bound HQ HC L (tailHeight L) (by linarith)
    (tail_height_ge_RH L hL) hu hlam hN
  rw [tail_lambda_eq_height, tail_log_height] at h
  have hb : tailHeight L * tailU L * Real.exp (-3 * L / 8) =
      2 * tailU L * Real.exp (-3 * L / 32) := by
    unfold tailHeight tailT
    calc
      _ = 2 * tailU L * (Real.exp (9 * L / 32) * Real.exp (-3 * L / 8)) := by ring
      _ = _ := by
        rw [← Real.exp_add]
        congr 2
        ring
  rw [hb] at h
  linarith

end LegendreK6
