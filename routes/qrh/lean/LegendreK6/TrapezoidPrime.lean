import LegendreK6.IntegratedExplicitFormula
import LegendreK6.PrimePowerBudget
import LegendreK6.MiddleDomains

/-!
# Prime extraction from actual trapezoid formulas and verified budgets

The lemmas here expose zero, trivial-zero and prime-power estimates as local
premises. They are intermediate criteria, not proofs of a numerical cell.
A completed cell must supply those premises from actual analytic estimates
and kernel-checked numerical bounds.
-/

namespace LegendreK6

open Filter Topology

/-- Pass a uniform finite-height zero bound to the actual weighted formula,
subtract actual nonprime contributions, and obtain a strictly interior prime. -/
theorem prime_of_trapezoid_budgets (H : IntegratedExplicitFormula)
    (x h a b Y Z P V : ℝ) (hx : 1 < x) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (hh : 0 < h) (hY : x + h ≤ Y)
    (hZ : ∀ T : ℝ, ‖truncatedTrapezoidZeroSum x h a b T‖ ≤ h * Z)
    (hV : ‖trapezoidTrivialDifference x h a b‖ ≤ h * V)
    (hP : weightedNonprime (Finset.Ioc 0 ⌊Y⌋₊)
      (fun m => trapezoidWeight x h a b (m : ℝ)) ≤ h * P)
    (hbudget : Z + P + V < 1) : PrimeInOpenInterval x (x + h) := by
  let W : ℝ := weightedMangoldt (Finset.Ioc 0 ⌊Y⌋₊)
    (fun m => trapezoidWeight x h a b (m : ℝ))
  let E : ℂ := trapezoidTrivialDifference x h a b
  have hlim := trapezoid_zero_sum_tendsto H x h a b Y hx ha hb hab hh hY
  have hz : ‖(h : ℂ) - (W : ℂ) - E‖ ≤ h * Z := le_of_tendsto' hlim.norm hZ
  have htri : ‖(h : ℂ) - (W : ℂ)‖ ≤ ‖(h : ℂ) - (W : ℂ) - E‖ + ‖E‖ := by
    simpa only [sub_add_cancel] using norm_add_le ((h : ℂ) - (W : ℂ) - E) E
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at htri
  simp only [Complex.ofReal_sub] at htri
  have hgain : h - h * (Z + V) ≤ W := by
    have hv : ‖E‖ ≤ h * V := hV
    have hle := le_abs_self (h - W)
    nlinarith
  apply prime_of_weighted_excess (Finset.Ioc 0 ⌊Y⌋₊)
    (fun m => trapezoidWeight x h a b (m : ℝ)) x (x + h)
  · intro m _ hm
    exact trapezoidWeight_support x h a b (m : ℝ) ha hb hab hh hm
  · have hstrict := mul_lt_mul_of_pos_left hbudget hh
    change weightedNonprime (Finset.Ioc 0 ⌊Y⌋₊)
      (fun m => trapezoidWeight x h a b (m : ℝ)) < W
    nlinarith

/-- The fixed middle trapezoid uses the proved actual prime-power cell budget.
The zero and trivial-zero bounds remain explicit obligations of the caller. -/
theorem middle_prime_of_trapezoid_budgets (H : IntegratedExplicitFormula)
    (A C L Z V : ℝ) (hA : 167 ≤ A) (hAL : A ≤ L) (hLC : L ≤ C)
    (hZ : ∀ T : ℝ,
      ‖truncatedTrapezoidZeroSum (middleX L) (middleH L) (1 / 32) (31 / 32) T‖ ≤ middleH L * Z)
    (hV : ‖trapezoidTrivialDifference (middleX L) (middleH L) (1 / 32) (31 / 32)‖ ≤ middleH L * V)
    (hbudget : Z + middlePrimePowerBudget A C + V < 1) : ShortInterval6 (middleX L) := by
  have hp := prime_of_trapezoid_budgets H (middleX L) (middleH L) (1 / 32) (31 / 32)
    (middleY L) Z (middlePrimePowerBudget A C) V (middle_X_gt_one L (hA.trans hAL))
    (by norm_num) (by norm_num) (by norm_num) (middleH_pos L) (le_refl _)
    hZ hV (middle_prime_power_le A C L hA hAL hLC) hbudget
  simpa only [ShortInterval6, middleH_eq_rpow] using hp

end LegendreK6
