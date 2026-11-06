import LegendreK6.AssemblyWithTail
import LegendreK6.M3LowerResult
import LegendreK6.M3MiddleUpper
import LegendreK6.M3FarUpper

/-!
# The complete downstream sixth-power theorem

Every project-specific analytic and numerical obligation is supplied by a
proof. The seven named mathematical inputs remain visible: QRH(7/8), CS v2,
Rosser's zero count, the classical integrated explicit formula, finite RH
through 3e12, CHJII's short-interval formula, and the corrected CHL rows.
This is not a re-proof of those external literature results.
-/

namespace LegendreK6

theorem middle_short_interval_from_inputs
    (HQ : QRHSevenEighths) (HC : CSv2) (HR : RosserZeroCount)
    (HI : IntegratedExplicitFormula) (HFR : FiniteRH3e12)
    (x : ℝ) (hx : 0 < x) (hlo : 167 ≤ Real.log x) (hhi : Real.log x ≤ 400) :
    ShortInterval6 x := by
  by_cases h : Real.log x ≤ 715/4
  · exact M3Lower.lower_middle_short_interval_from_inputs HQ HC HR HI HFR x hx hlo h
  · exact M3MiddleUpper.middle_upper_short_interval_from_inputs HQ HC HR HI x hx (by linarith) hhi

theorem finite_analytic_segments_from_inputs
    (HQ : QRHSevenEighths) (HC : CSv2) (HR : RosserZeroCount)
    (HI : IntegratedExplicitFormula) (HFR : FiniteRH3e12) :
    FiniteAnalyticSegmentInputs :=
  ⟨middle_short_interval_from_inputs HQ HC HR HI HFR,
    M3FarUpper.far_short_interval_from_inputs HQ HC HR HI⟩

/-- The stronger integral short-interval claim for every positive integer. -/
theorem sixth_power_short_from_named_inputs
    (HQ : QRHSevenEighths) (HC : CSv2) (HR : RosserZeroCount)
    (HI : IntegratedExplicitFormula) (HFR : FiniteRH3e12)
    (HJ : CHJIIShortInterval) (HCHL : CHLRows) (n : ℕ) (hn : 1 ≤ n) :
    NatSixthShort n := by
  apply nat_short_all_of_segment_inputs HCHL
    ⟨middle_short_interval_from_inputs HQ HC HR HI HFR,
      M3FarUpper.far_short_interval_from_inputs HQ HC HR HI,
      tail_short_interval_from_inputs HQ HC HR HJ⟩ n hn

/-- No local analytic-segment conclusion or numerical bound is an input. -/
theorem sixth_powers_from_named_inputs
    (HQ : QRHSevenEighths) (HC : CSv2) (HR : RosserZeroCount)
    (HI : IntegratedExplicitFormula) (HFR : FiniteRH3e12)
    (HJ : CHJIIShortInterval) (HCHL : CHLRows) : SixthPowerConclusion :=
  sixth_powers_of_finite_segment_inputs HQ HC HR HJ HCHL
    (finite_analytic_segments_from_inputs HQ HC HR HI HFR)

end LegendreK6
