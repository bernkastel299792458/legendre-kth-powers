import LegendreK6.M3FarAnalytic
import LegendreK6.M3FarResult
import LegendreK6.FarUniformBudgets
import LegendreK6.TrapezoidBudgetTranslation

/-!
# All far cells from one translated trapezoid pilot

The proof covers the real interval 400 <= log x <= 700 continuously. It is
an alternative proof of the full range previously covered by sixty polynomial
cells. It does not assert that the historical polynomial-kernel proof itself
has been translated line by line into Lean.
-/
namespace LegendreK6.M3FarUpper

open M3Far

theorem sigma_translation_grid (j : ℕ) (hj : j < 384) :
    1/2 ≤ s j ∧ s j ≤ s (j+1) ∧ s (j+1) ≤ 7/8 ∧ s (j+1)-s j ≤ 1/1024 := by
  refine ⟨(s_domain j hj.le).1, s_monotone (Nat.le_succ j),
    (s_domain (j+1) (by omega)).2, ?_⟩
  unfold s
  push_cast
  linarith

/-- The entire original far range, proved through the new translated
trapezoid budget. Only the four named external analytic inputs remain. -/
theorem far_upper_of_pilot_zero_budget
    (HQ : QRHSevenEighths) (HC : CSv2) (HR : RosserZeroCount)
    (HF : IntegratedExplicitFormula)
    (hzero : 2*trapezoidHeightBudget s rowNat 384 left q node 125 ≤ (22501/50000:ℝ))
    (x : ℝ) (hx : 0 < x) (hlo : 400 ≤ Real.log x) (hhi : Real.log x ≤ 700) :
    ShortInterval4 x := by
  let d : ℝ := Real.log x - left
  have hd : 0 ≤ d := by dsimp [d, left]; linarith
  have hd4 : 0 ≤ d/4 := by positivity
  have hA : 400 ≤ left+d := by dsimp [d, left]; linarith
  have hC0 : 0 ≤ right+d := by unfold right; linarith
  have hC : right+d ≤ 701 := by dsimp [d, right, left]; linarith
  have hq : 1+Real.exp ((right+d)/4)/4 ≤ q*Real.exp (d/4) := by
    exact one_add_exp_div_translate_le right d 4 hd (by norm_num)
  have ht := trapezoidHeightBudget_translation_le s rowNat 384 left q node 125 d 4
    (by norm_num [left]) q_pos.le node_monotone (by norm_num [node]) hd
    (by norm_num) sigma_translation_grid
  have hz : 2*trapezoidHeightBudget s rowNat 384 (left+d) (q*Real.exp (d/4))
      (fun j => node j+d/4) 125 ≤ (22501/50000 : ℝ) :=
    (mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ)≤2)).trans hzero
  have hp := farPrimePowerBudget_uniform (left+d) (right+d) hA hC0 hC
  have hv := farTrivialBudget_uniform (left+d) hA
  have hbudget : 2*trapezoidHeightBudget s rowNat 384 (left+d) (q*Real.exp (d/4))
      (fun j => node j+d/4) 125 + farPrimePowerBudget (left+d) (right+d) +
        cellTrivialBudget (left+d) < 1 := by linarith
  have hu : Monotone (fun j => node j+d/4) := by
    intro i j hij
    linarith [node_monotone hij]
  have hfirst : 3000000000000 ≤ Real.exp (node 0) := by
    rw [node_start]
    convert start_height_ge_RH using 1 <;> norm_num
  have huH : 3000000000000 ≤ Real.exp (node 0+d/4) :=
    hfirst.trans (Real.exp_le_exp.mpr (by linarith))
  have hu1 : 1 ≤ node 0+d/4 := by norm_num [node]; linarith
  have hU : 6 ≤ node 125+d/4 := by norm_num [node]; linarith
  have hstart : trapezoidHeightKernel (q*Real.exp (d/4)) (Real.exp (node 0+d/4)) = 1 := by
    rw [trapezoidHeightKernel_exp_translate, ← logKernel_eq, node_start]
    exact start_logKernel_eq_one
  exact far_cell_of_grid_budget_with_q HQ HC HR HF s rowNat 384
    (left+d) (right+d) (q*Real.exp (d/4)) (fun j => node j+d/4) 125 hA hq
    s_monotone s_zero (le_of_eq s_end.symm) s_row hu huH hu1 hU hstart hbudget x hx
    (by dsimp [d]; linarith)
    (by dsimp [d]; have := left_le_right; linarith)

theorem far_short_interval_from_inputs
    (HQ : QRHSevenEighths) (HC : CSv2) (HR : RosserZeroCount)
    (HI : IntegratedExplicitFormula)
    (x : ℝ) (hx : 0 < x) (hlo : 400 ≤ Real.log x) (hhi : Real.log x ≤ 700) :
    ShortInterval4 x :=
  far_upper_of_pilot_zero_budget HQ HC HR HI M3Far.zeroBudget_le x hx hlo hhi

end LegendreK6.M3FarUpper
