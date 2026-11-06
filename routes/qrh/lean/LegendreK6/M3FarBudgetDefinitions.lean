import LegendreK6.M3FarDefinitions
import LegendreK6.FarTrapezoidCell

/-! Complete pilot expressions, prior to their numerical enclosure. -/

namespace LegendreK6.M3Far

open scoped BigOperators

noncomputable def sigmaWeight (j : Fin 384) : ℝ :=
  Real.exp ((sigmaHi j-1)*left) - Real.exp ((sigmaLo j-1)*left)

noncomputable def densityD : ℝ := ∑ j : Fin 384, csB2 (row j)*sigmaWeight j
noncomputable def densityE : ℝ := ∑ j : Fin 384, csB3 (row j)*sigmaWeight j

noncomputable def mainBudget : ℝ :=
  ∑ j : Fin 384, ∑ i : Fin 125,
    sigmaCoefficient j * heightCoefficient i * Real.exp (exponent j * heightV i)

noncomputable def auxiliaryBudget : ℝ :=
  ∑ i : Fin 125, heightCoefficient i *
    (densityD + densityE / height i + Real.exp (-left/2+height i) / height i)

noncomputable def completeBudget : ℝ := mainBudget + auxiliaryBudget +
  farPrimePowerBudget left right + cellTrivialBudget left

end LegendreK6.M3Far
