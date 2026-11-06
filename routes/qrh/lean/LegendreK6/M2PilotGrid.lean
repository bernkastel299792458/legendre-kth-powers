import LegendreK6.M2PilotDefinitions
import LegendreK6.M2PilotConstants
import LegendreK6.FiniteDensityGrid
import LegendreK6.MiddleDomains

/-!
# Exact grid geometry and shifted-power domains of the pilot cell

Natural-index grids are used by the generic density and height estimates;
the equalities below connect them to the finite-index numerical definitions.
The row bounds cover the full closed sigma cell, including shared boundaries.
-/

namespace LegendreK6.M2Pilot

noncomputable def s (j : ℕ) : ℝ := (2048 + (j : ℝ)) / 4096
def rowNat (j : ℕ) : Fin 12 := ⟨min (j / 128) 11, by omega⟩
noncomputable def node (i : ℕ) : ℝ := (1841 + (i : ℝ)) / 64
noncomputable def U : ℝ := 2829 / 64

theorem left_ge_167 : (167 : ℝ) ≤ left := by norm_num [left]
theorem left_le_right : left ≤ right := by norm_num [left, right]
theorem q_pos : 0 < q := by unfold q; positivity

theorem middle_q_le_pilot_q (L : ℝ) (hLC : L ≤ right) : middleQ L ≤ q :=
  middle_q_cell_le L right hLC

theorem s_monotone : Monotone s := by
  intro i j hij
  unfold s
  exact div_le_div_of_nonneg_right (add_le_add le_rfl (Nat.cast_le.mpr hij)) (by norm_num)

theorem s_zero : s 0 = (1 / 2 : ℝ) := by norm_num [s]
theorem s_end : s 1536 = (7 / 8 : ℝ) := by norm_num [s]

theorem s_domain (j : ℕ) (hj : j ≤ 1536) : (1 / 2 : ℝ) ≤ s j ∧ s j ≤ (7 / 8 : ℝ) := by
  constructor
  · rw [← s_zero]
    exact s_monotone (Nat.zero_le j)
  · rw [← s_end]
    exact s_monotone hj

theorem rowNat_val (j : ℕ) (hj : j < 1536) : (rowNat j).val = j / 128 := by
  unfold rowNat
  exact min_eq_left (by omega)

theorem rowNat_fin (j : Fin 1536) : rowNat j.val = row j := by
  apply Fin.ext
  exact rowNat_val j.val j.isLt

theorem sigmaLo_eq_s (j : Fin 1536) : sigmaLo j = s j.val := rfl

theorem sigmaHi_eq_s_succ (j : Fin 1536) : sigmaHi j = s (j.val + 1) := by
  unfold sigmaHi s
  push_cast
  ring

/-- Both endpoints of each sigma cell belong to the selected closed CS row. -/
theorem s_row_cell (j : ℕ) (hj : j < 1536) :
    (16 + ((rowNat j).val : ℝ)) / 32 ≤ s j ∧
      s (j + 1) ≤ (17 + ((rowNat j).val : ℝ)) / 32 := by
  have hlo : 128 * (j / 128) ≤ j := by omega
  have hhi : j + 1 ≤ 128 * (j / 128 + 1) := by omega
  have hloR : (128 : ℝ) * ((j / 128 : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hlo
  have hhiR : (j : ℝ) + 1 ≤ (128 : ℝ) * (((j / 128 : ℕ) : ℝ) + 1) := by
    exact_mod_cast hhi
  rw [rowNat_val j hj]
  unfold s
  push_cast
  constructor <;> linarith

theorem s_row (j : ℕ) (hj : j < 1536) :
    (16 + ((rowNat j).val : ℝ)) / 32 ≤ s j ∧
      s j ≤ (17 + ((rowNat j).val : ℝ)) / 32 := by
  obtain ⟨hlo, hhi⟩ := s_row_cell j hj
  exact ⟨hlo, (s_monotone (Nat.le_succ j)).trans hhi⟩

theorem sigma_row_cell (j : Fin 1536) :
    (16 + ((row j).val : ℝ)) / 32 ≤ sigmaLo j ∧
      sigmaHi j ≤ (17 + ((row j).val : ℝ)) / 32 := by
  simpa only [rowNat_fin, ← sigmaLo_eq_s, ← sigmaHi_eq_s_succ] using s_row_cell j.val j.isLt

theorem sigmaLo_bounds (j : Fin 1536) : (1 / 2 : ℝ) ≤ sigmaLo j ∧ sigmaLo j ≤ (7 / 8 : ℝ) :=
  s_domain j.val j.isLt.le

theorem sigmaHi_bounds (j : Fin 1536) : (1 / 2 : ℝ) ≤ sigmaHi j ∧ sigmaHi j ≤ (7 / 8 : ℝ) := by
  rw [sigmaHi_eq_s_succ]
  exact s_domain (j.val + 1) (by omega)

theorem exponent_eq_csExponent (j : Fin 1536) : exponent j = csExponent (s j.val) := rfl

theorem sigmaCoefficient_eq_grid (j : Fin 1536) :
    sigmaCoefficient j = csB1 (rowNat j.val) * sigmaGridWeight s left j.val := by
  rw [rowNat_fin]
  unfold sigmaCoefficient sigmaGridWeight
  rw [sigmaLo_eq_s, sigmaHi_eq_s_succ]

theorem node_monotone : Monotone node := by
  intro i j hij
  unfold node
  exact div_le_div_of_nonneg_right (add_le_add le_rfl (Nat.cast_le.mpr hij)) (by norm_num)

theorem node_start : node 0 = (1841 / 64 : ℝ) := by norm_num [node]
theorem node_end : node 988 = U := by norm_num [node, U]
theorem U_ge_six : (6 : ℝ) ≤ U := by norm_num [U]

theorem node_succ_eq_height (i : Fin 988) : node (i.val + 1) = height i := by
  unfold node height
  push_cast
  ring

theorem node_eq_height_sub (i : Fin 988) : node i.val = height i - (1 / 64 : ℝ) := by
  unfold node height
  ring

theorem heightMass_eq_node (i : Fin 988) :
    heightMass i = logKernel (node i.val) - logKernel (node (i.val + 1)) := by
  rw [node_succ_eq_height, node_eq_height_sub]
  rfl

theorem height_bounds (i : Fin 988) : (1842 / 64 : ℝ) ≤ height i ∧ height i ≤ (2829 / 64 : ℝ) := by
  have hlo : (0 : ℝ) ≤ (i.val : ℝ) := Nat.cast_nonneg _
  have hhi : (i.val : ℝ) ≤ 987 := by exact_mod_cast (show i.val ≤ 987 by omega)
  unfold height
  constructor <;> linarith

theorem height_pos (i : Fin 988) : 0 < height i := lt_of_lt_of_le (by norm_num) (height_bounds i).1
theorem height_zero : height 0 = (1842 / 64 : ℝ) := by norm_num [height]
theorem height_last : height 987 = U := by norm_num [height, U]

theorem sigmaPower_bounds (j : Fin 1536) : 0 ≤ sigmaPower j ∧ sigmaPower j ≤ (2 / 3 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := sigmaLo_bounds j
  have hden : 0 < 2 - sigmaLo j := by linarith
  have hp0 : (1 / 3 : ℝ) ≤ exponent j := by
    unfold exponent
    apply (le_div_iff₀ hden).2
    linarith
  have hp1 : exponent j ≤ 1 := by
    unfold exponent
    apply (div_le_iff₀ hden).2
    linarith
  unfold sigmaPower shiftP
  constructor <;> linarith

theorem height_log_lower (i : Fin 988) : (215 / 64 : ℝ) ≤ Real.log (height i) := by
  have h0 : Real.exp (215 / 64 : ℝ) ≤ (1842 / 64 : ℝ) := by
    convert first_height_exp_lower using 1 <;> norm_num
  exact (Real.le_log_iff_exp_le (height_pos i)).2 (h0.trans (height_bounds i).1)

theorem height_log_upper (i : Fin 988) : Real.log (height i) ≤ (284 / 64 : ℝ) := by
  have h0 : (2829 / 64 : ℝ) ≤ Real.exp (284 / 64 : ℝ) := by
    convert last_height_exp_upper using 1 <;> norm_num
  exact (Real.log_le_iff_le_exp (height_pos i)).2 ((height_bounds i).2.trans h0)

theorem heightPower_bounds (i : Fin 988) : 0 ≤ heightPower i ∧ heightPower i ≤ (33 / 2 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := height_bounds i
  have hloglo := height_log_lower i
  have hloghi := height_log_upper i
  unfold heightPower heightV shiftV
  constructor <;> linarith

theorem sigma_height_product_bounds (j : Fin 1536) (i : Fin 988) :
    0 ≤ sigmaPower j * heightPower i ∧ sigmaPower j * heightPower i ≤ 11 := by
  obtain ⟨hs0, hs1⟩ := sigmaPower_bounds j
  obtain ⟨ht0, ht1⟩ := heightPower_bounds i
  constructor
  · exact mul_nonneg hs0 ht0
  · have h := mul_le_mul hs1 ht1 ht0 (by norm_num : (0 : ℝ) ≤ 2 / 3)
    norm_num at h
    exact h

end LegendreK6.M2Pilot
