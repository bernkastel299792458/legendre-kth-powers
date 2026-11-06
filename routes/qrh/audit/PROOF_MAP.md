# Human review map for the downstream k=6 proof

Read [the formalization addendum](../paper/lean_formalization_addendum.md)
alongside the modules below. The final theorem accepts seven named literature
inputs; the actual source definitions and the full dependency audit are the
authority for their mathematical meaning.

| Proof obligation | Main source | What must be checked |
|---|---|---|
| Actual zeros and multiplicities | [ZetaZeros](../lean/LegendreK6/ZetaZeros.lean) | Actual ζ, analytic order, compact truncation, conjugation, absence of real strip zeros |
| Exact density inputs | [DensityInput](../lean/LegendreK6/DensityInput.lean) | QRH 7/8, CS **v2**, all twelve table rows and height domains |
| Classical tail inputs | [LiteratureInputs](../lean/LegendreK6/LiteratureInputs.lean) | Literal Rosser count and CHJII's common existential cutoff |
| Infinite tail | [TailFromInputs](../lean/LegendreK6/TailFromInputs.lean) | Actual zero sum and arithmetic bounds imply a strict prime interval |
| Integrated formula | [IntegratedExplicitFormula](../lean/LegendreK6/IntegratedExplicitFormula.lean) | Original unweighted source formula, actual Ψ₁, signs and height-limit convention |
| Trapezoid formula and Mellin estimates | [TrapezoidKernel](../lean/LegendreK6/TrapezoidKernel.lean), [TrapezoidPrime](../lean/LegendreK6/TrapezoidPrime.lean) | Actual four-point powers, support, prime-power subtraction and strict endpoints |
| Density/height reduction | [FiniteDensityGrid](../lean/LegendreK6/FiniteDensityGrid.lean), [TrapezoidHeightBound](../lean/LegendreK6/TrapezoidHeightBound.lean) | Closed beta cutoffs, nonnegative masses and residual contribution of low zeros |
| Certified height residual | [GeometricHeightTail](../lean/LegendreK6/GeometricHeightTail.lean) | Finite geometric prefix, heights ×4, cumulative bound ×8, kernel decay ×16 |
| Difficult pilot | [M2PilotResult](../lean/LegendreK6/M2PilotResult.lean) | Full actual budget ≤0.939772; no remaining numerical parameter |
| Exponential matrix numerics | [LowRankTaylor](../lean/LegendreK6/LowRankTaylor.lean), [LowRankInteger](../lean/LegendreK6/LowRankInteger.lean) | Actual Taylor remainder, positive finite sums, dyadic-to-integer equality |
| Continuous propagation | [DensityGridTranslation](../lean/LegendreK6/DensityGridTranslation.lean), [TrapezoidBudgetTranslation](../lean/LegendreK6/TrapezoidBudgetTranslation.lean) | Joint real-parameter shift, exact kernel invariance and proved density decrease |
| Finite-height RH | [FiniteRHInput](../lean/LegendreK6/FiniteRHInput.lean), [TrapezoidLowHeight](../lean/LegendreK6/TrapezoidLowHeight.lean) | Closed 3e12 cutoff, actual low/high zero split, proved scaled-kernel inequality |
| Lower middle | [M3LowerComparison](../lean/LegendreK6/M3LowerComparison.lean), [M3LowerResult](../lean/LegendreK6/M3LowerResult.lean) | Thresholds 1229/1366, factors 64/1.5/1, complete budget ≤0.966283 |
| Upper middle | [M3MiddleUpper](../lean/LegendreK6/M3MiddleUpper.lean) | Full interval [178.75,400] from the proved pilot |
| Far pilot and propagation | [M3FarResult](../lean/LegendreK6/M3FarResult.lean), [M3FarUpper](../lean/LegendreK6/M3FarUpper.lean) | New trapezoid budget ≤0.450022, full [400,700] fourth-power length |
| Integer lower range | [LowerRange](../lean/LegendreK6/LowerRange.lean) | Actual Pratt primality, corrected CHL rows, strict joins to L=167 |
| All historical cells | [FinalCellCoverage](../lean/LegendreK6/FinalCellCoverage.lean) | Every point of all 94+60 cells; saved rational maxima are not analytic premises |
| All positive integers | [FinalResult](../lean/LegendreK6/FinalResult.lean) | Exactly seven input types, all endpoints covered, actual `Nat.Prime` and strict powers |

The old polynomial-weight certificate is preserved as historical evidence.
The new far proof uses the trapezoid; the names of the saved far cells do not
change the weight used in the new proof.

Implementation cross-reviews are in `milestone1_review.md`,
`milestone2_analytic_review.md`, `milestone3_translation_review.md` and
`milestone3_final_review.md`. Each states its implementation overlap.
These are AI reviews, not recorded human expert peer review.
