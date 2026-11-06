import LegendreK6.M2PilotExpression

/-! The complete pilot numerical expression equals the proved analytic budget. -/

namespace LegendreK6.M2Pilot

open scoped BigOperators

set_option maxRecDepth 10000

theorem height_coefficient_mul_div (i : Fin 988) (F : ℝ) :
    heightCoefficient i * (F/(height i)^2) = 2*heightMass i*F +
      if i.val = 987 then 32*(4096/31 : ℝ)*(heightZ (height i))^2*F else 0 := by
  have hn : height i ≠ 0 := (height_pos i).ne'
  unfold heightCoefficient
  split_ifs <;> field_simp <;> ring

theorem height_tail_sum (F : Fin 988 → ℝ) :
    (∑ i : Fin 988, if i.val = 987 then
      32*(4096/31 : ℝ)*(heightZ (height i))^2*F i else 0) =
      32*(4096/31 : ℝ)*(heightZ U)^2*F 987 := by
  classical
  rw [Finset.sum_eq_single (987 : Fin 988)]
  · rw [show (987 : Fin 988).val = 987 by decide, ite_eq_left (rfl : (987:ℕ)=987), height_last]
  · intro i _ hi
    have hv : i.val ≠ 987 := by
      intro he
      apply hi
      apply Fin.ext
      simpa using he
    rw [ite_eq_right hv]
  · simp

theorem heightZ_square_eq (u : ℝ) : (heightZ u)^2 = q^2*Real.exp (-2*u) := by
  rw [heightZ_eq, div_pow]
  have he : Real.exp (-2*u) = 1/(Real.exp u)^2 := by
    rw [show -2*u = -(u+u) by ring, Real.exp_neg, Real.exp_add]
    ring
  rw [he]
  ring

theorem weightedPhi_eq_twice_heightBudget :
    (∑ i : Fin 988, heightCoefficient i * (densityGridPhi s rowNat 1536 left (height i)/(height i)^2)) =
      2*trapezoidHeightBudget s rowNat 1536 left q node 988 := by
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

theorem gridPhi_div_square (i : Fin 988) :
    densityGridPhi s rowNat 1536 left (height i)/(height i)^2 =
      (∑ j : Fin 1536, sigmaCoefficient j * Real.exp (exponent j*heightV i)) +
      (densityD + densityE/height i + Real.exp (-left/2+height i)/height i) := by
  let M : ℝ := ∑ j : Fin 1536, sigmaCoefficient j * Real.exp (exponent j*heightV i)
  have hp : densityGridPhi s rowNat 1536 left (height i) =
      Real.exp (-left/2+height i)*height i + M*(height i)^2 +
        densityD*(height i)^2 + densityE*height i := gridPhi_eq_pilot _ (height_pos i)
  change densityGridPhi s rowNat 1536 left (height i)/(height i)^2 =
    M + (densityD + densityE/height i + Real.exp (-left/2+height i)/height i)
  rw [hp]
  have hn : height i ≠ 0 := (height_pos i).ne'
  field_simp [hn]
  ring

theorem weightedPhi_eq_main_add_aux :
    (∑ i : Fin 988, heightCoefficient i * (densityGridPhi s rowNat 1536 left (height i)/(height i)^2)) =
      mainBudget + auxiliaryBudget := by
  have hp (i : Fin 988) :
      heightCoefficient i * (densityGridPhi s rowNat 1536 left (height i)/(height i)^2) =
      (∑ j : Fin 1536, sigmaCoefficient j*heightCoefficient i*Real.exp (exponent j*heightV i)) +
        heightCoefficient i*(densityD+densityE/height i+Real.exp (-left/2+height i)/height i) := by
    rw [gridPhi_div_square, mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hp]
  rw [Finset.sum_add_distrib]
  change (∑ i : Fin 988, ∑ j : Fin 1536,
    sigmaCoefficient j*heightCoefficient i*Real.exp (exponent j*heightV i)) + auxiliaryBudget = _
  unfold mainBudget
  rw [Finset.sum_comm]

theorem analytic_budget_eq_completeBudget :
    2*trapezoidHeightBudget s rowNat 1536 left q node 988 +
      middlePrimePowerBudget left right + cellTrivialBudget left = completeBudget := by
  rw [← weightedPhi_eq_twice_heightBudget, weightedPhi_eq_main_add_aux]
  rfl

end LegendreK6.M2Pilot
