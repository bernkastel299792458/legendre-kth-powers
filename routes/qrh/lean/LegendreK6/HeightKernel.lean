import Mathlib

/-! The common trapezoid height envelope, as a function of the actual height. -/

namespace LegendreK6

noncomputable def trapezoidHeightKernel (q T : ℝ) : ℝ :=
  min 1 (min (((64 : ℝ) / 31) * q / T) (((4096 : ℝ) / 31) * q ^ 2 / T ^ 2))

end LegendreK6
