import LegendreK6.DensityInput
import LegendreK6.HeightKernel
import LegendreK6.LowRankTaylor

/-! Exact real expressions for the most difficult middle cell.
The new pilot uses a conservative geometric height tail. It does not alter
the frozen Arb certificate or assume its saved numerical upper bounds. -/

namespace LegendreK6.M2Pilot

open scoped BigOperators

noncomputable def left : ℝ := 715 / 4
noncomputable def right : ℝ := 179
noncomputable def shiftP : ℝ := 1 / 3
noncomputable def shiftV : ℝ := 2057 / 64
noncomputable def q : ℝ := 1 + Real.exp (right / 6) / 6
noncomputable def sigmaLo (j : Fin 1536) : ℝ := (2048 + (j.val : ℝ)) / 4096
noncomputable def sigmaHi (j : Fin 1536) : ℝ := (2049 + (j.val : ℝ)) / 4096
def row (j : Fin 1536) : Fin 12 := ⟨j.val / 128, by omega⟩
noncomputable def exponent (j : Fin 1536) : ℝ :=
  3 * (1 - sigmaLo j) / (2 - sigmaLo j)
noncomputable def sigmaCoefficient (j : Fin 1536) : ℝ :=
  csB1 (row j) * (Real.exp ((sigmaHi j - 1) * left) -
    Real.exp ((sigmaLo j - 1) * left))
noncomputable def sigmaFactor (j : Fin 1536) : ℝ :=
  csB1 (row j) * (Real.exp ((sigmaHi j - 1) * left + exponent j * shiftV) -
    Real.exp ((sigmaLo j - 1) * left + exponent j * shiftV))
noncomputable def sigmaPower (j : Fin 1536) : ℝ := exponent j - shiftP

theorem sigmaFactor_eq (j : Fin 1536) :
    sigmaFactor j = sigmaCoefficient j * Real.exp (exponent j * shiftV) := by
  unfold sigmaFactor sigmaCoefficient
  rw [Real.exp_add, Real.exp_add]
  ring

/-- The stable evaluation of `q*exp(-u)`. -/
noncomputable def heightZ (u : ℝ) : ℝ := Real.exp (-u) + Real.exp (right / 6 - u) / 6
noncomputable def zKernel (z : ℝ) : ℝ :=
  min 1 (min (((64 : ℝ) / 31) * z) (((4096 : ℝ) / 31) * z ^ 2))
noncomputable def logKernel (u : ℝ) : ℝ := zKernel (heightZ u)
noncomputable def height (i : Fin 988) : ℝ := (1842 + (i.val : ℝ)) / 64
noncomputable def heightMass (i : Fin 988) : ℝ :=
  logKernel (height i - 1 / 64) - logKernel (height i)
noncomputable def heightV (i : Fin 988) : ℝ := height i + Real.log (height i)
noncomputable def heightPower (i : Fin 988) : ℝ := heightV i - shiftV

/-- The geometric tail contributes once more at the final height. -/
noncomputable def heightCoefficient (i : Fin 988) : ℝ :=
  2 * (height i) ^ 2 * heightMass i +
  if i.val = 987 then 32 * (4096 / 31 : ℝ) * (heightZ (height i)) ^ 2 * (height i) ^ 2
    else 0
noncomputable def heightFactor (i : Fin 988) : ℝ :=
  heightCoefficient i * Real.exp (shiftP * heightPower i)

theorem heightZ_eq (u : ℝ) : heightZ u = q / Real.exp u := by
  unfold heightZ q
  rw [Real.exp_sub, Real.exp_neg]
  field_simp

theorem logKernel_eq (u : ℝ) : logKernel u = trapezoidHeightKernel q (Real.exp u) := by
  unfold logKernel zKernel trapezoidHeightKernel
  rw [heightZ_eq]
  congr 2 <;> ring

theorem heightZ_nonneg (u : ℝ) : 0 ≤ heightZ u := by unfold heightZ; positivity

theorem heightZ_antitone : Antitone heightZ := by
  intro u v huv
  unfold heightZ
  apply add_le_add
  · exact Real.exp_le_exp.mpr (neg_le_neg huv)
  · exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by norm_num)

theorem zKernel_monotone {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : zKernel a ≤ zKernel b := by
  unfold zKernel
  apply min_le_min le_rfl
  apply min_le_min
  · exact mul_le_mul_of_nonneg_left hab (by norm_num)
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab 2) (by norm_num)

theorem logKernel_antitone : Antitone logKernel := by
  intro u v huv
  exact zKernel_monotone (heightZ_nonneg v) (heightZ_antitone huv)

theorem heightMass_nonneg (i : Fin 988) : 0 ≤ heightMass i := by
  unfold heightMass
  exact sub_nonneg.mpr (logKernel_antitone (by linarith))

theorem heightCoefficient_nonneg (i : Fin 988) : 0 ≤ heightCoefficient i := by
  unfold heightCoefficient
  have hm := heightMass_nonneg i
  split_ifs <;> positivity

theorem heightFactor_nonneg (i : Fin 988) : 0 ≤ heightFactor i :=
  mul_nonneg (heightCoefficient_nonneg i) (Real.exp_nonneg _)

end LegendreK6.M2Pilot
