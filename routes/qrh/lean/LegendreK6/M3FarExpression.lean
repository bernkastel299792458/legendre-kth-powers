import LegendreK6.M3FarBudgetDefinitions
import LegendreK6.M3FarGrid
import LegendreK6.TrapezoidHeightBound

/-! Exact connection of the analytic height budget to the factored pilot sum. -/

namespace LegendreK6.M3Far

open scoped BigOperators

theorem sigmaWeight_eq_grid (j : Fin 384) :
    sigmaWeight j = sigmaGridWeight s left j.val := by
  unfold sigmaWeight sigmaGridWeight
  rw [sigmaLo_eq_s, sigmaHi_eq_s_succ]

theorem sigmaWeight_nonneg (j : Fin 384) : 0 ≤ sigmaWeight j := by
  rw [sigmaWeight_eq_grid]
  exact sigmaGridWeight_nonneg s left j.val s_monotone (by norm_num [left])

theorem sigmaCoefficient_nonneg (j : Fin 384) : 0 ≤ sigmaCoefficient j :=
  mul_nonneg (cs_row_constants_nonneg (row j)).1 (sigmaWeight_nonneg j)

theorem sigmaFactor_nonneg (j : Fin 384) : 0 ≤ sigmaFactor j := by
  rw [sigmaFactor_eq]
  exact mul_nonneg (sigmaCoefficient_nonneg j) (Real.exp_nonneg _)

theorem mainBudget_le_lowRank : mainBudget ≤
    lowRankTaylor20 Finset.univ Finset.univ sigmaFactor sigmaPower heightFactor heightPower := by
  have hh := shifted_exp_sum_le (Finset.univ : Finset (Fin 384))
    (Finset.univ : Finset (Fin 125)) sigmaCoefficient exponent heightCoefficient heightV
    shiftP shiftV (fun j _ => sigmaCoefficient_nonneg j)
    (fun j _ => sub_nonneg.mp (sigmaPower_bounds j).1)
    (fun i _ => heightCoefficient_nonneg i)
    (fun i _ => sub_nonneg.mp (heightPower_bounds i).1)
    (fun j _ i _ => (sigma_height_product_bounds j i).2)
  change mainBudget ≤ lowRankTaylor20 Finset.univ Finset.univ
    (fun j => sigmaFactor j) (fun j => exponent j-shiftP)
    (fun i => heightCoefficient i*Real.exp (shiftP*(heightV i-shiftV)))
    (fun i => heightV i-shiftV)
  simpa only [mainBudget, ← sigmaFactor_eq] using hh

theorem exp_power_height_factor (p u : ℝ) (hu : 0 < u) :
    Real.exp (p*u) * u^(p+2) = u^2 * Real.exp (p*(u+Real.log u)) := by
  rw [Real.rpow_add hu, Real.rpow_two, Real.rpow_def_of_pos hu]
  rw [← mul_assoc, mul_comm _ (u^2), ← Real.exp_add]
  rw [show p*u + Real.log u*p = p*(u+Real.log u) by ring]

theorem gridPhi_eq_pilot (u : ℝ) (hu : 0 < u) :
    densityGridPhi s rowNat 384 left u =
      Real.exp (-left/2+u)*u +
        (∑ j : Fin 384, sigmaCoefficient j * Real.exp (exponent j*(u+Real.log u)))*u^2 +
        densityD*u^2 + densityE*u := by
  have hs : (∑ j ∈ Finset.range 384,
      sigmaGridWeight s left j * csLogHeightBound (rowNat j) (s j) u) =
      ∑ j : Fin 384, sigmaWeight j * csLogHeightBound (row j) (sigmaLo j) u := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    rw [← sigmaWeight_eq_grid, rowNat_fin]
    rfl
  have hterm (j : Fin 384) : sigmaWeight j * csLogHeightBound (row j) (sigmaLo j) u =
      (sigmaCoefficient j * Real.exp (exponent j*(u+Real.log u)))*u^2 +
      (csB2 (row j)*sigmaWeight j)*u^2 + (csB3 (row j)*sigmaWeight j)*u := by
    have he := exp_power_height_factor (exponent j) u hu
    change Real.exp (csExponent (sigmaLo j)*u) * u^(csExponent (sigmaLo j)+2) = _ at he
    unfold csLogHeightBound sigmaCoefficient
    change sigmaWeight j * (csB1 (row j) * Real.exp (csExponent (sigmaLo j)*u) *
      u^(csExponent (sigmaLo j)+2) + csB2 (row j)*u^2 + csB3 (row j)*u) = _
    have hc : Real.exp ((sigmaHi j-1)*left) - Real.exp ((sigmaLo j-1)*left) = sigmaWeight j := rfl
    rw [hc]
    calc
      _ = csB1 (row j)*sigmaWeight j *
          (Real.exp (csExponent (sigmaLo j)*u)*u^(csExponent (sigmaLo j)+2)) +
          (csB2 (row j)*sigmaWeight j)*u^2 + (csB3 (row j)*sigmaWeight j)*u := by ring
      _ = _ := by rw [he]; ring
  unfold densityGridPhi
  rw [hs]
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.sum_mul]
  unfold densityD densityE
  ring

end LegendreK6.M3Far
