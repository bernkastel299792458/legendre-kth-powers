import LegendreK6.M3LowerMainBound
import LegendreK6.M3LowerExpression
import LegendreK6.TrapezoidLowHeight
import LegendreK6.M2PilotAuxiliary

/-! The complete lower middle interval, using finite RH only below its
explicit cutoff and actual CS/grid estimates above it. -/

namespace LegendreK6.M3Lower

theorem lower_middle_short_interval_from_inputs
    (HQ : QRHSevenEighths) (HC : CSv2) (HR : RosserZeroCount)
    (HI : IntegratedExplicitFormula) (HFR : FiniteRH3e12)
    (x : ℝ) (hx : 0 < x) (hlo : 167 ≤ Real.log x)
    (hhi : Real.log x ≤ 715/4) : ShortInterval6 x := by
  let L := Real.log x
  have hL : 167 ≤ L := hlo
  have hLA : L ≤ M2Pilot.left := hhi
  have hQ : 0 ≤ middleQ L := by rw [middle_q_eq]; positivity
  have hheight : 3000000000000 ≤ Real.exp (M2Pilot.node 0) := by
    rw [M2Pilot.node_start]
    convert M2Pilot.start_height_ge_RH using 1 <;> norm_num
  have hstart : trapezoidHeightKernel M2Pilot.q (Real.exp (M2Pilot.node 0)) = 1 := by
    rw [← M2Pilot.logKernel_eq, M2Pilot.node_start]
    exact M2Pilot.start_logKernel_eq_one
  let Z := 2*Real.exp (-L/2)*3000000000000*Real.log 3000000000000 +
    2*scaling L*trapezoidHeightBudget M2Pilot.s M2Pilot.rowNat 1536 L M2Pilot.q M2Pilot.node 988
  have hZ (T : ℝ) :
      ‖truncatedTrapezoidZeroSum (middleX L) (middleH L) (1/32) (31/32) T‖ ≤ middleH L*Z := by
    exact norm_truncatedTrapezoidZeroSum_le_scaled_heightBudget HQ HC HR HFR
      M2Pilot.s M2Pilot.rowNat 1536 L L (middleH L) (middleQ L) M2Pilot.q (scaling L)
      T M2Pilot.node 988 (middleH_pos L) (by linarith) le_rfl hQ M2Pilot.q_pos.le
      (scaling_nonneg L) (scaling_le_one L hLA) le_rfl
      (middleQ_le_scaling_q L hL) (middleQ_linear_le_scaling L hL)
      M2Pilot.s_monotone M2Pilot.s_zero (le_of_eq M2Pilot.s_end.symm) M2Pilot.s_row
      M2Pilot.node_monotone hheight (by norm_num [M2Pilot.node])
      (by norm_num [M2Pilot.node]) hstart
  have hb : Z + middlePrimePowerBudget L L + cellTrivialBudget L < 1 := by
    have hw := scaled_heightBudget_le L hL hLA
    have hm := weightedMain_le
    have ha := M2Pilot.auxiliaryBudget_le_small
    have hl := low_zero_budget_small L hL
    have hp := prime_power_budget_small L hL hLA
    have hv := trivial_budget_small L hL
    dsimp [Z]
    linarith
  have hh := middle_prime_of_zero_budget HI L L L Z hL le_rfl le_rfl hZ hb
  simpa only [middleX, L, Real.exp_log hx] using hh

end LegendreK6.M3Lower
