import LegendreK6.M2PilotAnalytic
import LegendreK6.M2PilotLowRankBound
import LegendreK6.M2PilotAuxiliary
import LegendreK6.M2PilotSmallBudgets

/-!
# The complete difficult-cell result

The numerical premise of `pilot_interval_of_complete_budget` is supplied
here by actual factor enclosures and exact integer-moment evaluation.
The resulting prime theorem has only four named external literature inputs,
plus the real-variable domain. It covers this pilot cell, not all of k=6.
-/

namespace LegendreK6.M2Pilot

theorem completeBudget_le : completeBudget ≤ (234943/250000 : ℝ) := by
  have hm := mainBudget_le_lowRank.trans lowRankTaylor20_le
  have ha := auxiliaryBudget_le_small
  have hp := prime_power_budget_small
  have hv := trivial_budget_small
  unfold completeBudget
  linarith

theorem completeBudget_lt_47_50 : completeBudget < (47/50 : ℝ) :=
  completeBudget_le.trans_lt (by norm_num)

theorem pilot_short_interval_from_inputs
    (HQ : QRHSevenEighths) (HC : CSv2) (HR : RosserZeroCount)
    (HF : IntegratedExplicitFormula)
    (x : ℝ) (hx : 0 < x) (hlo : (715/4 : ℝ) ≤ Real.log x)
    (hhi : Real.log x ≤ 179) : ShortInterval6 x :=
  pilot_interval_of_complete_budget HQ HC HR HF
    (completeBudget_lt_47_50.trans (by norm_num)) x hx hlo hhi

end LegendreK6.M2Pilot
