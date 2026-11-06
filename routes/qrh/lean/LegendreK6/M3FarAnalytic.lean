import LegendreK6.FarTrapezoidCell
import LegendreK6.M3FarBudgetIdentity

/-! All analytic and grid obligations for the pilot, with its last numerical
inequality still exposed. The final pilot result must supply that inequality. -/

namespace LegendreK6.M3Far

theorem pilot_interval_of_complete_budget
    (HQ : QRHSevenEighths) (HC : CSv2) (HR : RosserZeroCount)
    (HF : IntegratedExplicitFormula) (hbudget : completeBudget < 1)
    (x : ℝ) (hx : 0 < x) (hlo : (400 : ℝ) ≤ Real.log x)
    (hhi : Real.log x ≤ 1601/4) : ShortInterval4 x := by
  have hheight : 3000000000000 ≤ Real.exp (node 0) := by
    rw [node_start]
    convert start_height_ge_RH using 1 <;> norm_num
  have hstart : trapezoidHeightKernel (1+Real.exp (right/4)/4) (Real.exp (node 0)) = 1 := by
    change trapezoidHeightKernel q (Real.exp (node 0)) = 1
    rw [← logKernel_eq, node_start]
    exact start_logKernel_eq_one
  apply far_cell_of_grid_budget HQ HC HR HF s rowNat 384 left right node 125
    (by norm_num [left]) s_monotone s_zero (le_of_eq s_end.symm) s_row
    node_monotone hheight (by norm_num [node]) (by norm_num [node]) hstart
  · change 2*trapezoidHeightBudget s rowNat 384 left q node 125 +
      farPrimePowerBudget left right + cellTrivialBudget left < 1
    rwa [analytic_budget_eq_completeBudget]
  · exact hx
  · exact hlo
  · exact hhi

end LegendreK6.M3Far
