import LegendreK6.IntegratedPsi
import LegendreK6.TrapezoidKernel
import LegendreK6.ZetaZeros

/-!
# The classical integrated explicit formula and its four-point consequence

The named external input below is the height-limit consequence of Hildebrand,
Introduction to Analytic Number Theory (2013-01-07), Theorem 5.18, equation
(5.32), printed p.166; absolute convergence is stated in (5.34), p.167.
Source:
https://eclass-b.uoa.gr/modules/document/file.php/MATH717/04.%20%CE%92%CE%BF%CE%B7%CE%B8%CE%AE%CE%BC%CE%B1%CF%84%CE%B1/Analytic-number-theory-Hildebrand.pdf

This module does not prove that classical formula. It proves its finite
four-point application to the actual integrated Chebyshev sums. The affine
terms use the literal zeta derivatives from the source and cancel exactly.
No weighted explicit formula or error budget is an external hypothesis.
No interchange of the trivial-zero infinite sum is asserted here.
-/

namespace LegendreK6

open scoped BigOperators
open Filter Topology

/-- The actual zero-primitive sum at a closed absolute-height cutoff. -/
noncomputable def integratedZeroSum (t T : ℝ) : ℂ :=
  ∑ ρ ∈ allZetaZeros T, (zetaMultiplicity ρ : ℂ) * zeroPrimitive ρ t

/-- The trivial-zero primitive series, indexed by positive integers `j+1`.
The denominator in each term is `2*(j+1)*(2*(j+1)-1)`. -/
noncomputable def trivialZeroPrimitiveSum (t : ℝ) : ℂ :=
  ∑' j : ℕ, zeroPrimitive (-2 * ((j + 1 : ℕ) : ℂ)) t

/-- The literal right side determining the nontrivial-zero sum in the
classical integrated explicit formula. -/
noncomputable def integratedFormulaValue (t : ℝ) : ℂ :=
  (t : ℂ) ^ 2 / 2 - (deriv riemannZeta 0 / riemannZeta 0) * (t : ℂ) +
    deriv riemannZeta (-1) / riemannZeta (-1) - trivialZeroPrimitiveSum t -
    (integratedPsi t : ℂ)

/-- Accepted classical input: the actual height-truncated nontrivial-zero
series converges to the value in the integrated explicit formula for `t>1`.
This is weaker than asserting the source's absolute convergence theorem. -/
def IntegratedExplicitFormula : Prop :=
  ∀ t : ℝ, 1 < t → Tendsto (integratedZeroSum t) atTop (𝓝 (integratedFormulaValue t))

/-- The actual height-truncated zero sum after the finite trapezoid operator. -/
noncomputable def truncatedTrapezoidZeroSum (x h a b T : ℝ) : ℂ :=
  ∑ ρ ∈ allZetaZeros T, (zetaMultiplicity ρ : ℂ) * trapezoidKernel x h a b ρ

/-- The four-point operation on the trivial-zero series. This definition
deliberately does not interchange that operation and the infinite sum. -/
noncomputable def trapezoidTrivialDifference (x h a b : ℝ) : ℂ :=
  (trivialZeroPrimitiveSum x - trivialZeroPrimitiveSum (x + a * h) -
    trivialZeroPrimitiveSum (x + b * h) + trivialZeroPrimitiveSum (x + h)) /
      ((a * b * h : ℝ) : ℂ)

theorem truncatedTrapezoidZeroSum_eq_four_point (x h a b T : ℝ) :
    truncatedTrapezoidZeroSum x h a b T =
      (integratedZeroSum x T - integratedZeroSum (x + a * h) T -
        integratedZeroSum (x + b * h) T + integratedZeroSum (x + h) T) /
        ((a * b * h : ℝ) : ℂ) := by
  unfold truncatedTrapezoidZeroSum integratedZeroSum trapezoidKernel
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ρ _
  ring

theorem four_point_quadratic_complex (x h a b : ℝ) (hab : a + b = 1)
    (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    ((x : ℂ) ^ 2 / 2 - ((x + a * h : ℝ) : ℂ) ^ 2 / 2 -
      ((x + b * h : ℝ) : ℂ) ^ 2 / 2 + ((x + h : ℝ) : ℂ) ^ 2 / 2) /
      ((a * b * h : ℝ) : ℂ) = (h : ℂ) := by
  exact_mod_cast four_point_quadratic x h a b hab ha hb hh

theorem four_point_affine_complex (x h a b : ℝ) (c d : ℂ) (hab : a + b = 1) :
    (c * (x : ℂ) + d) - (c * ((x + a * h : ℝ) : ℂ) + d) -
      (c * ((x + b * h : ℝ) : ℂ) + d) + (c * ((x + h : ℝ) : ℂ) + d) = 0 := by
  have hbval : b = 1 - a := by linarith
  rw [hbval]
  push_cast
  ring

/-- The finite algebraic consequence of the four literal source formulas. -/
theorem integratedFormulaValue_four_point (x h a b Y : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hh : 0 < h)
    (hY : x + h ≤ Y) :
    (integratedFormulaValue x - integratedFormulaValue (x + a * h) -
      integratedFormulaValue (x + b * h) + integratedFormulaValue (x + h)) /
      ((a * b * h : ℝ) : ℂ) =
      (h : ℂ) - (weightedMangoldt (Finset.Ioc 0 ⌊Y⌋₊)
        (fun m => trapezoidWeight x h a b (m : ℝ)) : ℂ) -
      trapezoidTrivialDifference x h a b := by
  have hquad := four_point_quadratic_complex x h a b hab ha.ne' hb.ne' hh.ne'
  have hlinear := four_point_affine_complex x h a b
    (-(deriv riemannZeta 0 / riemannZeta 0))
    (deriv riemannZeta (-1) / riemannZeta (-1)) hab
  have hpsi :
      ((integratedPsi x : ℂ) - (integratedPsi (x + a * h) : ℂ) -
        (integratedPsi (x + b * h) : ℂ) + (integratedPsi (x + h) : ℂ)) /
        ((a * b * h : ℝ) : ℂ) =
      (weightedMangoldt (Finset.Ioc 0 ⌊Y⌋₊)
        (fun m => trapezoidWeight x h a b (m : ℝ)) : ℂ) := by
    exact_mod_cast (weightedMangoldt_trapezoid_eq x h a b Y ha hb hab hh hY).symm
  unfold integratedFormulaValue trapezoidTrivialDifference
  linear_combination hquad - hpsi + hlinear / ((a * b * h : ℝ) : ℂ)

/-- The actual truncated trapezoid zero sum converges to the main term minus
the actual weighted Mangoldt sum and the unexchanged trivial-series difference.
Only the original classical formula is assumed; the weighted formula follows. -/
theorem trapezoid_zero_sum_tendsto (H : IntegratedExplicitFormula)
    (x h a b Y : ℝ) (hx : 1 < x) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (hh : 0 < h) (hY : x + h ≤ Y) :
    Tendsto (truncatedTrapezoidZeroSum x h a b) atTop
      (𝓝 ((h : ℂ) - (weightedMangoldt (Finset.Ioc 0 ⌊Y⌋₊)
        (fun m => trapezoidWeight x h a b (m : ℝ)) : ℂ) -
        trapezoidTrivialDifference x h a b)) := by
  have hxa : 1 < x + a * h := by nlinarith [mul_pos ha hh]
  have hxb : 1 < x + b * h := by nlinarith [mul_pos hb hh]
  have hxy : 1 < x + h := by linarith
  have ht := ((((H x hx).sub (H (x + a * h) hxa)).sub
    (H (x + b * h) hxb)).add (H (x + h) hxy)).div_const ((a * b * h : ℝ) : ℂ)
  have hf : (fun T =>
      (integratedZeroSum x T - integratedZeroSum (x + a * h) T -
        integratedZeroSum (x + b * h) T + integratedZeroSum (x + h) T) /
        ((a * b * h : ℝ) : ℂ)) = truncatedTrapezoidZeroSum x h a b := by
    funext T
    exact (truncatedTrapezoidZeroSum_eq_four_point x h a b T).symm
  rw [hf, integratedFormulaValue_four_point x h a b Y ha hb hab hh hY] at ht
  exact ht

end LegendreK6
