import LegendreK6.Assembly
import LegendreK6.TailFromInputs

/-!
# Assembly after the infinite tail has been formalized

The two finite analytic ranges remain explicitly unproved inputs. The tail
is derived from named external inputs, and is no longer a local assumption.
The earlier assembly theorem is retained as a general conditional lemma.
-/

namespace LegendreK6

structure FiniteAnalyticSegmentInputs : Prop where
  middle : ∀ x : ℝ, 0 < x → 167 ≤ Real.log x → Real.log x ≤ 400 → ShortInterval6 x
  far : ∀ x : ℝ, 0 < x → 400 ≤ Real.log x → Real.log x ≤ 700 → ShortInterval4 x

theorem sixth_powers_of_finite_segment_inputs
    (HQ : QRHSevenEighths) (HC : CSv2) (HR : RosserZeroCount)
    (HJ : CHJIIShortInterval) (HCHL : CHLRows) (H : FiniteAnalyticSegmentInputs) :
    SixthPowerConclusion := by
  apply sixth_powers_of_segment_inputs HCHL
  exact ⟨H.middle, H.far, tail_short_interval_from_inputs HQ HC HR HJ⟩

end LegendreK6
