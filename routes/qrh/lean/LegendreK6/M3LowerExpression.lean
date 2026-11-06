import LegendreK6.M3LowerBudgetDefinitions
import LegendreK6.M3LowerConstants
import LegendreK6.M2PilotBudgetIdentity

/-! The scaled actual density-grid budget is reduced to the weighted pilot
main term and 64 times the already certified auxiliary term. -/

namespace LegendreK6.M3Lower

open scoped BigOperators
open M2Pilot

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem csLogHeightBound_div_square (j : Fin 1536) (u : ℝ) (hu : 0 < u) :
    csLogHeightBound (row j) (sigmaLo j) u / u^2 =
      csB1 (row j)*Real.exp (exponent j*(u+Real.log u)) +
        csB2 (row j) + csB3 (row j)/u := by
  have he := exp_power_height_factor (exponent j) u hu
  change Real.exp (csExponent (sigmaLo j)*u)*u^(csExponent (sigmaLo j)+2) = _ at he
  unfold csLogHeightBound
  rw [show csB1 (row j)*Real.exp (csExponent (sigmaLo j)*u)*u^(csExponent (sigmaLo j)+2) =
    csB1 (row j)*(Real.exp (csExponent (sigmaLo j)*u)*u^(csExponent (sigmaLo j)+2)) by ring, he]
  field_simp [hu.ne']

theorem gridPhi_div_square_eq (L u : ℝ) (hu : 0 < u) :
    densityGridPhi s rowNat 1536 L u / u^2 = Real.exp (-L/2+u)/u +
      ∑ j : Fin 1536, sigmaGridWeight s L j.val *
        (csB1 (row j)*Real.exp (exponent j*(u+Real.log u)) + csB2 (row j) + csB3 (row j)/u) := by
  unfold densityGridPhi
  rw [add_div, Finset.sum_div, ← Fin.sum_univ_eq_sum_range]
  apply congrArg₂ (·+·)
  · field_simp [hu.ne']
  · apply Finset.sum_congr rfl
    intro j _
    rw [mul_div_assoc, rowNat_fin, ← sigmaLo_eq_s, csLogHeightBound_div_square j u hu]

theorem scaled_gridPhi_div_square_le (L u : ℝ) (hL : 167 ≤ L)
    (hLA : L ≤ left) (hu : 0 < u) :
    scaling L * (densityGridPhi s rowNat 1536 L u/u^2) ≤
      (∑ j : Fin 1536, multiplier j*sigmaCoefficient j*Real.exp (exponent j*(u+Real.log u))) +
        64*(densityD+densityE/u+Real.exp (-left/2+u)/u) := by
  have hb0 := scaled_baseline_le L u hL hLA hu.le
  have hb1 : scaling L*Real.exp (-L/2+u) ≤ 64*Real.exp (-left/2+u) := by
    apply (mul_le_mul_iff_left₀ hu).mp
    simpa only [scaling, mul_assoc] using hb0
  have hb : scaling L*(Real.exp (-L/2+u)/u) ≤ 64*(Real.exp (-left/2+u)/u) := by
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hb1 hu.le
  have hp (j : Fin 1536) :
      scaling L*(sigmaGridWeight s L j.val *
        (csB1 (row j)*Real.exp (exponent j*(u+Real.log u)) + csB2 (row j) + csB3 (row j)/u)) ≤
      multiplier j*sigmaCoefficient j*Real.exp (exponent j*(u+Real.log u)) +
        64*(csB2 (row j)*sigmaWeight j + (csB3 (row j)*sigmaWeight j)/u) := by
    have hw : scaling L*sigmaGridWeight s L j.val ≤ multiplier j*sigmaWeight j :=
      scaled_sigma_weight_le L hL hLA j
    have hw64 : scaling L*sigmaGridWeight s L j.val ≤ 64*sigmaWeight j :=
      hw.trans (mul_le_mul_of_nonneg_right (multiplier_le_64 j) (sigmaWeight_nonneg j))
    obtain ⟨hB1, hB2, hB3⟩ := cs_row_constants_nonneg (row j)
    have hm := mul_le_mul_of_nonneg_right hw
      (mul_nonneg hB1 (Real.exp_nonneg (exponent j*(u+Real.log u))))
    have ha := mul_le_mul_of_nonneg_right hw64
      (add_nonneg hB2 (div_nonneg hB3 hu.le))
    have hc : sigmaCoefficient j = csB1 (row j)*sigmaWeight j := rfl
    rw [hc]
    calc
      _ = (scaling L*sigmaGridWeight s L j.val)*
          (csB1 (row j)*Real.exp (exponent j*(u+Real.log u))) +
          (scaling L*sigmaGridWeight s L j.val)*(csB2 (row j)+csB3 (row j)/u) := by ring
      _ ≤ (multiplier j*sigmaWeight j)*(csB1 (row j)*Real.exp (exponent j*(u+Real.log u))) +
          (64*sigmaWeight j)*(csB2 (row j)+csB3 (row j)/u) := add_le_add hm ha
      _ = _ := by ring
  rw [gridPhi_div_square_eq L u hu, mul_add, Finset.mul_sum]
  apply (add_le_add hb (Finset.sum_le_sum fun j _ => hp j)).trans
  apply le_of_eq
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
  unfold densityD densityE
  ring

theorem height_sum_identity (L : ℝ) :
    (∑ i : Fin 988, heightCoefficient i *
      (densityGridPhi s rowNat 1536 L (height i)/(height i)^2)) =
        2*trapezoidHeightBudget s rowNat 1536 L q node 988 := by
  simp_rw [height_coefficient_mul_div, Finset.sum_add_distrib]
  rw [height_tail_sum]
  unfold trapezoidHeightBudget
  rw [mul_add, Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
  apply congrArg₂ (·+·)
  · apply Finset.sum_congr rfl
    intro i _
    rw [← node_succ_eq_height, heightMass_eq_node, logKernel_eq, logKernel_eq]
    ring
  · rw [height_last, node_end, heightZ_square_eq]
    ring

theorem scaled_heightBudget_le (L : ℝ) (hL : 167 ≤ L) (hLA : L ≤ left) :
    2*scaling L*trapezoidHeightBudget s rowNat 1536 L q node 988 ≤
      weightedMain+64*auxiliaryBudget := by
  have hp (i : Fin 988) :
      scaling L*(heightCoefficient i*(densityGridPhi s rowNat 1536 L (height i)/(height i)^2)) ≤
      heightCoefficient i*((∑ j : Fin 1536,
        multiplier j*sigmaCoefficient j*Real.exp (exponent j*heightV i)) +
          64*(densityD+densityE/height i+Real.exp (-left/2+height i)/height i)) := by
    have hh := mul_le_mul_of_nonneg_left
      (scaled_gridPhi_div_square_le L (height i) hL hLA (height_pos i)) (heightCoefficient_nonneg i)
    simpa only [heightV, mul_left_comm] using hh
  have heq (i : Fin 988) :
      heightCoefficient i*((∑ j : Fin 1536,
        multiplier j*sigmaCoefficient j*Real.exp (exponent j*heightV i)) +
          64*(densityD+densityE/height i+Real.exp (-left/2+height i)/height i)) =
      (∑ j : Fin 1536,
        multiplier j*sigmaCoefficient j*heightCoefficient i*Real.exp (exponent j*heightV i)) +
          64*(heightCoefficient i*(densityD+densityE/height i+Real.exp (-left/2+height i)/height i)) := by
    rw [mul_add, Finset.mul_sum]
    apply congrArg₂ (·+·)
    · apply Finset.sum_congr rfl
      intro j _
      ring
    · ring
  calc
    _ = scaling L*∑ i : Fin 988, heightCoefficient i*
        (densityGridPhi s rowNat 1536 L (height i)/(height i)^2) := by
      rw [height_sum_identity]
      ring
    _ ≤ ∑ i : Fin 988, heightCoefficient i*((∑ j : Fin 1536,
        multiplier j*sigmaCoefficient j*Real.exp (exponent j*heightV i)) +
          64*(densityD+densityE/height i+Real.exp (-left/2+height i)/height i)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => hp i
    _ = _ := by
      simp_rw [heq, Finset.sum_add_distrib, ← Finset.mul_sum]
      unfold weightedMain auxiliaryBudget
      rw [Finset.sum_comm]

end LegendreK6.M3Lower
