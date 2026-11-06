import LegendreK6.M3FarAnalytic
import LegendreK6.M3FarLowRankBound
import LegendreK6.M3FarAuxiliary
import LegendreK6.M3FarSmallBudgets

/-! The fourth-power far pilot closes its actual finite numerical budget.
This new trapezoid proof preserves the original polynomial certificate. -/
namespace LegendreK6.M3Far

theorem zeroBudget_le :
    2*trapezoidHeightBudget s rowNat 384 left q node 125 ≤ (22501/50000 : ℝ) := by
  have hm := mainBudget_le_lowRank.trans lowRankTaylor20_le
  have ha := auxiliaryBudget_le_small
  rw [← weightedPhi_eq_twice_heightBudget, weightedPhi_eq_main_add_aux]
  linarith

theorem completeBudget_le : completeBudget ≤ (225011/500000 : ℝ) := by
  have hm := mainBudget_le_lowRank.trans lowRankTaylor20_le
  have ha := auxiliaryBudget_le_small
  have hp := prime_power_budget_small
  have hv := trivial_budget_small
  unfold completeBudget
  linarith

theorem completeBudget_lt_half : completeBudget < (1/2 : ℝ) :=
  completeBudget_le.trans_lt (by norm_num)

theorem pilot_short_interval_from_inputs
    (HQ : QRHSevenEighths) (HC : CSv2) (HR : RosserZeroCount)
    (HF : IntegratedExplicitFormula)
    (x : ℝ) (hx : 0 < x) (hlo : (400 : ℝ) ≤ Real.log x)
    (hhi : Real.log x ≤ 1601/4) : ShortInterval4 x :=
  pilot_interval_of_complete_budget HQ HC HR HF
    (completeBudget_lt_half.trans (by norm_num)) x hx hlo hhi

end LegendreK6.M3Far
