import LegendreK6.M2PilotResult
import LegendreK6.TrapezoidBudgetTranslation

/-! The complete sixth-power middle range above the certified pilot.
One checked numerical certificate is transported analytically; no new
cell budget or weighted-zero estimate is assumed. -/

namespace LegendreK6.M3MiddleUpper

open M2Pilot

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def shiftedQ (L : ℝ) : ℝ := q*Real.exp ((L-left)/6)
noncomputable def shiftedNode (L : ℝ) (j : ℕ) : ℝ := node j+(L-left)/6
noncomputable def pilotZeroBudget : ℝ :=
  2*trapezoidHeightBudget s rowNat 1536 left q node 988

theorem pilot_grid_translation_conditions :
    ∀ j < 1536, 1/2 ≤ s j ∧ s j ≤ s (j+1) ∧ s (j+1) ≤ 7/8 ∧
      s (j+1)-s j ≤ 1/1024 := by
  intro j hj
  refine ⟨(s_domain j (by omega)).1, s_monotone (Nat.le_succ j),
    (s_domain (j+1) (by omega)).2, ?_⟩
  unfold s
  push_cast
  linarith

theorem pilot_zero_budget_small : pilotZeroBudget ≤ (93977/100000 : ℝ) := by
  have hm := mainBudget_le_lowRank.trans lowRankTaylor20_le
  have ha := auxiliaryBudget_le_small
  have he : pilotZeroBudget = mainBudget+auxiliaryBudget := by
    unfold pilotZeroBudget
    rw [← weightedPhi_eq_twice_heightBudget, weightedPhi_eq_main_add_aux]
  rw [he]
  linarith

theorem shifted_budget_le_pilot (L : ℝ) (hL : left ≤ L) :
    2*trapezoidHeightBudget s rowNat 1536 L (shiftedQ L) (shiftedNode L) 988 ≤
      pilotZeroBudget := by
  have ht := trapezoidHeightBudget_translation_le s rowNat 1536 left q node 988
    (L-left) 6 left_ge_167 q_pos.le node_monotone (by norm_num [node])
    (by linarith) (by norm_num) pilot_grid_translation_conditions
  have he : left+(L-left) = L := by ring
  rw [he] at ht
  exact mul_le_mul_of_nonneg_left ht (by norm_num)

theorem middleQ_le_shiftedQ (L : ℝ) (hL : left ≤ L) : middleQ L ≤ shiftedQ L := by
  have hd : 0 ≤ (L-left)/6 := by linarith
  have he1 : 1 ≤ Real.exp ((L-left)/6) := Real.one_le_exp_iff.mpr hd
  have hC : L ≤ right+(L-left) := by norm_num [left,right] at *; linarith
  have hh := middle_q_cell_le L (right+(L-left)) hC
  have he : Real.exp ((right+(L-left))/6) =
      Real.exp (right/6)*Real.exp ((L-left)/6) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hh
  unfold shiftedQ q
  nlinarith

theorem shifted_kernel_start (L : ℝ) :
    trapezoidHeightKernel (shiftedQ L) (Real.exp (shiftedNode L 0)) = 1 := by
  rw [shiftedQ, shiftedNode, trapezoidHeightKernel_exp_translate, ← logKernel_eq, node_start]
  exact start_logKernel_eq_one

theorem shifted_zero_bound (HQ : QRHSevenEighths) (HC : CSv2) (HR : RosserZeroCount)
    (L T : ℝ) (hL : left ≤ L) :
    ‖truncatedTrapezoidZeroSum (middleX L) (middleH L) (1/32) (31/32) T‖ ≤
      middleH L*pilotZeroBudget := by
  have hL167 : 167 ≤ L := left_ge_167.trans hL
  have hd : 0 ≤ (L-left)/6 := by linarith
  have hun : Monotone (shiftedNode L) := by
    intro i j hij
    dsimp [shiftedNode]
    linarith [node_monotone hij]
  have hh0 : 3000000000000 ≤ Real.exp (node 0) := by
    rw [node_start]
    convert start_height_ge_RH using 1 <;> norm_num
  have hh : 3000000000000 ≤ Real.exp (shiftedNode L 0) :=
    hh0.trans (Real.exp_le_exp.mpr (by unfold shiftedNode; linarith))
  have hu1 : 1 ≤ shiftedNode L 0 := by unfold shiftedNode; norm_num [node]; linarith
  have hU : 6 ≤ shiftedNode L 988 := by unfold shiftedNode; norm_num [node]; linarith
  have hq : 0 ≤ shiftedQ L := mul_nonneg q_pos.le (Real.exp_nonneg _)
  have hqq : (Real.exp L+middleH L)/middleH L ≤ shiftedQ L := middleQ_le_shiftedQ L hL
  have hb := norm_truncatedTrapezoidZeroSum_le_heightBudget HQ HC HR s rowNat 1536
    L L (middleH L) (shiftedQ L) T (shiftedNode L) 988 (middleH_pos L)
    (by linarith) le_rfl hq hqq s_monotone s_zero (le_of_eq s_end.symm) s_row
    hun hh hu1 hU (shifted_kernel_start L)
  exact hb.trans (mul_le_mul_of_nonneg_left (shifted_budget_le_pilot L hL) (middleH_pos L).le)

private theorem log_two_lower : (1/2:ℝ) ≤ Real.log 2 := by
  apply (Real.le_log_iff_exp_le (by norm_num : (0:ℝ)<2)).2
  have he : Real.exp (((1/2:ℚ):ℝ)) ≤ 2 := by dyadic_interval [prec := 64]
  norm_num at he
  exact he

theorem upper_prime_power_budget_small (A C : ℝ) (hA : left ≤ A)
    (hC0 : 0 ≤ C) (hC : C ≤ 401) :
    middlePrimePowerBudget A C ≤ (1/1000000:ℝ) := by
  let e := middleEpsilon A
  have he0 : 0 ≤ e := (middleEpsilon_pos A).le
  have he1 : e ≤ 1 := by
    have hn : 6*Real.exp (-2) ≤ (1:ℝ) := by dyadic_interval [prec := 64]
    have hm : Real.exp (-A/6) ≤ Real.exp (-2) := by
      apply Real.exp_le_exp.mpr
      norm_num [left] at hA
      linarith
    dsimp [e,middleEpsilon]
    linarith
  have hs0 := Real.sqrt_nonneg (1+e)
  have hs2 : Real.sqrt (1+e) ≤ 2 := by
    have hs := Real.sq_sqrt (show 0 ≤ 1+e by linarith)
    nlinarith
  have hl0 : 0 ≤ Real.log (1+e) := Real.log_nonneg (by linarith)
  have hl1 : Real.log (1+e) ≤ 1 := by
    have hl := Real.log_le_sub_one_of_pos (show 0 < 1+e by linarith)
    linarith
  have hnum : (32/31:ℝ)*Real.sqrt (1+e)*(C+Real.log (1+e))^2 ≤ 1200000 := by
    calc
      _ ≤ 2*2*402^2 :=
        mul_le_mul (mul_le_mul (by norm_num) hs2 hs0 (by norm_num))
          (pow_le_pow_left₀ (by linarith) (by linarith) 2) (sq_nonneg _) (by norm_num)
      _ ≤ _ := by norm_num
  have hd : 6 ≤ 12*Real.log 2 := by linarith [log_two_lower]
  have hd0 : 0 < 12*Real.log 2 := by linarith
  have hquot : (32/31:ℝ)*Real.sqrt (1+e)*(C+Real.log (1+e))^2 /
      (12*Real.log 2) ≤ 200000 := by
    apply (div_le_iff₀ hd0).2
    nlinarith
  have hexp0 : Real.exp (-55) ≤ (0.000000000000000001:ℝ) := by
    dyadic_interval [prec := 64]
  have hexp : Real.exp (-A/3) ≤ (0.000000000000000001:ℝ) := by
    apply le_trans _ hexp0
    apply Real.exp_le_exp.mpr
    norm_num [left] at hA
    linarith
  change (32/31:ℝ)*Real.sqrt (1+e)*(C+Real.log (1+e))^2 /
    (12*Real.log 2)*Real.exp (-A/3) ≤ (1/1000000:ℝ)
  have hp := mul_le_mul_of_nonneg_right hquot (Real.exp_nonneg (-A/3))
  nlinarith

theorem middle_upper_at_log_from_inputs
    (HQ : QRHSevenEighths) (HC : CSv2) (HR : RosserZeroCount)
    (HF : IntegratedExplicitFormula) (L : ℝ) (hlo : (715/4:ℝ) ≤ L) (hhi : L ≤ 400) :
    ShortInterval6 (middleX L) := by
  have hL : left ≤ L := hlo
  have hp := upper_prime_power_budget_small L (L+1/4) hL (by linarith) (by linarith)
  have hv := (cellTrivialBudget_antitone (by norm_num [left]) hL).trans trivial_budget_small
  exact middle_prime_of_zero_budget HF L (L+1/4) L pilotZeroBudget
    (left_ge_167.trans hL) le_rfl (by linarith)
    (fun T => shifted_zero_bound HQ HC HR L T hL)
    (by linarith [pilot_zero_budget_small])

theorem middle_upper_short_interval_from_inputs
    (HQ : QRHSevenEighths) (HC : CSv2) (HR : RosserZeroCount)
    (HF : IntegratedExplicitFormula) (x : ℝ) (hx : 0 < x)
    (hlo : (715/4:ℝ) ≤ Real.log x) (hhi : Real.log x ≤ 400) : ShortInterval6 x := by
  have hh := middle_upper_at_log_from_inputs HQ HC HR HF (Real.log x) hlo hhi
  simpa only [middleX,Real.exp_log hx] using hh

end LegendreK6.M3MiddleUpper
