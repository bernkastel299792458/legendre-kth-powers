import LegendreK6.M3LowerComparison

namespace LegendreK6.M3Lower
open scoped BigOperators

noncomputable def weightedMain : ℝ :=
  ∑ j : Fin 1536, ∑ i : Fin 988,
    multiplier j * M2Pilot.sigmaCoefficient j * M2Pilot.heightCoefficient i *
      Real.exp (M2Pilot.exponent j*M2Pilot.heightV i)

end LegendreK6.M3Lower
