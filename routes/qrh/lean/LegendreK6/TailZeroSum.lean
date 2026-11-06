import LegendreK6.CpowInterval
import LegendreK6.TailDensity
import LegendreK6.LiteratureInputs

/-!
# The actual truncated zero contribution in the infinite tail

This module connects the complex zero increments to the three scalar density
terms. It handles arbitrary truncations bounded above by `tailHeight`, proves
the positive/negative-height factor of two using the actual zeta symmetry and
real-axis nonvanishing, and derives the required total count from Rosser's
explicit input. No weighted-zero bound is assumed.
-/

namespace LegendreK6

open scoped BigOperators

/-- The first three terms of the infinite-tail bound. -/
noncomputable def tailZeroBound (L : ℝ) : ℝ :=
  4 * tailU L * Real.exp (-3 * L / 32) +
  (1122 / 25 : ℝ) * (tailU L) ^ 3 * (L / tailLambda L) *
    Real.exp (-tailLambda L / 8) +
  2 * ((829 / 100 : ℝ) * (tailU L) ^ 2 + 147 * tailU L) * Real.exp (-L / 8)

/-- The true zeta-zero term at any admissible truncation is bounded by
the interval length times the first three explicit tail terms. -/
theorem tail_truncated_zero_bound (HQ : QRHSevenEighths) (HC : CSv2)
    (HR : RosserZeroCount) (L Tstar : ℝ) (hL : 700 ≤ L)
    (hT : Tstar ≤ tailHeight L) :
    ‖truncatedZeroIncrement (tailX L) (tailY L) Tstar‖ ≤
      tailH L * tailZeroBound L := by
  have hlog : 1 ≤ Real.log (tailHeight L) := by
    rw [tail_log_height]
    exact (tail_U_gt_one L hL).le
  have hN := totalZeroCount_le_mul_log HR (tail_height_ge_RH L hL) hlog
  have hpositive := tail_positive_zero_sum_bound HQ HC L hL hN
  change 2 * (∑ ρ ∈ positiveZetaZeros (tailHeight L),
    (zetaMultiplicity ρ : ℝ) * Real.exp ((ρ.re - 1) * L)) ≤ tailZeroBound L at hpositive
  have hsubset :
      (∑ ρ ∈ allZetaZeros Tstar, (zetaMultiplicity ρ : ℝ) *
        Real.exp ((ρ.re - 1) * L)) ≤
      ∑ ρ ∈ allZetaZeros (tailHeight L), (zetaMultiplicity ρ : ℝ) *
        Real.exp ((ρ.re - 1) * L) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (allZetaZeros_mono hT)
    intro ρ _ _
    exact mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)
  rw [sum_allZetaZeros_eq_twice (tailHeight L)
    (fun ρ => Real.exp ((ρ.re - 1) * L)) (by intro ρ; simp)] at hsubset
  have hsum := hsubset.trans hpositive
  have hρ : ∀ ρ ∈ allZetaZeros Tstar, ρ ≠ 0 := by
    intro ρ hρ hz
    have hr := (mem_allZetaZeros.mp hρ).2.1
    simp [hz] at hr
  have hre : ∀ ρ ∈ allZetaZeros Tstar, ρ.re ≤ 1 := by
    intro ρ hρ
    exact (mem_allZetaZeros.mp hρ).2.2.1.le
  have hraw := norm_sum_cpow_sub_div_le (allZetaZeros Tstar) id zetaMultiplicity
    (tailX_pos L) (tail_X_lt_Y L).le hρ hre
  have hlength : tailY L - tailX L = tailH L := by unfold tailY; ring
  have hpow (ρ : ℂ) : (tailX L) ^ (ρ.re - 1) = Real.exp ((ρ.re - 1) * L) := by
    rw [Real.rpow_def_of_pos (tailX_pos L), tail_log_X]
    congr 1
    ring
  simp only [id_eq, hlength] at hraw
  simp_rw [hpow] at hraw
  exact hraw.trans (mul_le_mul_of_nonneg_left hsum (tailH_pos L).le)

end LegendreK6
