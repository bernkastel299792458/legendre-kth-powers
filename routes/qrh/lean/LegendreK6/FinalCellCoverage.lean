import LegendreK6.FinalResult
import LegendreK6.Certificates

/-! Every historical cell is covered by an actual prime-interval theorem.
The new far proof uses the trapezoid, not the historical polynomial weight.
Saved rational maxima are not premises of these analytic conclusions. -/

namespace LegendreK6

theorem refined_cells_domain : ∀ c ∈ refinedCells,
    (167 : ℚ) ≤ c.left ∧ c.right ≤ 400 := by
  norm_num [refinedCells]

theorem historical_far_cells_domain : ∀ c ∈ polynomialCells,
    (400 : ℚ) ≤ c.left ∧ c.right ≤ 700 := by
  norm_num [polynomialCells]

theorem all_94_cells_actual_prime_intervals
    (HQ : QRHSevenEighths) (HC : CSv2) (HR : RosserZeroCount)
    (HI : IntegratedExplicitFormula) (HFR : FiniteRH3e12)
    (c : SavedCell) (hc : c ∈ refinedCells) (x : ℝ) (hx : 0 < x)
    (hlo : (c.left : ℝ) ≤ Real.log x) (hhi : Real.log x ≤ (c.right : ℝ)) :
    ShortInterval6 x := by
  obtain ⟨ha,hb⟩ := refined_cells_domain c hc
  have ha' : (167 : ℝ) ≤ (c.left : ℝ) := by exact_mod_cast ha
  have hb' : (c.right : ℝ) ≤ (400 : ℝ) := by exact_mod_cast hb
  exact middle_short_interval_from_inputs HQ HC HR HI HFR x hx (ha'.trans hlo) (hhi.trans hb')

theorem all_60_far_cells_actual_prime_intervals
    (HQ : QRHSevenEighths) (HC : CSv2) (HR : RosserZeroCount)
    (HI : IntegratedExplicitFormula)
    (c : SavedCell) (hc : c ∈ polynomialCells) (x : ℝ) (hx : 0 < x)
    (hlo : (c.left : ℝ) ≤ Real.log x) (hhi : Real.log x ≤ (c.right : ℝ)) :
    ShortInterval4 x := by
  obtain ⟨ha,hb⟩ := historical_far_cells_domain c hc
  have ha' : (400 : ℝ) ≤ (c.left : ℝ) := by exact_mod_cast ha
  have hb' : (c.right : ℝ) ≤ (700 : ℝ) := by exact_mod_cast hb
  exact M3FarUpper.far_short_interval_from_inputs HQ HC HR HI x hx (ha'.trans hlo) (hhi.trans hb')

end LegendreK6
