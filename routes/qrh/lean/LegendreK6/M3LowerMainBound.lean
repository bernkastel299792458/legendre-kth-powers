import LegendreK6.M3LowerInteger
import LegendreK6.M3LowerBudgetDefinitions

namespace LegendreK6.M3Lower
open scoped BigOperators
open M2Pilot

theorem weightedMain_le_lowRank : weightedMain ≤
    lowRankTaylor20 Finset.univ Finset.univ
      (fun j => multiplier j*sigmaFactor j) sigmaPower heightFactor heightPower := by
  have hh := shifted_exp_sum_le (Finset.univ : Finset (Fin 1536))
    (Finset.univ : Finset (Fin 988)) (fun j => multiplier j*sigmaCoefficient j)
    exponent heightCoefficient heightV shiftP shiftV
    (fun j _ => mul_nonneg (multiplier_nonneg j) (sigmaCoefficient_nonneg j))
    (fun j _ => sub_nonneg.mp (sigmaPower_bounds j).1)
    (fun i _ => heightCoefficient_nonneg i)
    (fun i _ => sub_nonneg.mp (heightPower_bounds i).1)
    (fun j _ i _ => (sigma_height_product_bounds j i).2)
  have he : (fun j : Fin 1536 => multiplier j*sigmaCoefficient j*
      Real.exp (exponent j*shiftV)) = (fun j => multiplier j*sigmaFactor j) := by
    funext j
    rw [sigmaFactor_eq]
    ring
  rw [he] at hh
  exact hh

theorem weightedMain_le : weightedMain ≤ (193/200 : ℝ) :=
  weightedMain_le_lowRank.trans weighted_lowRank_le

end LegendreK6.M3Lower
