import LegendreK6.DensityGridTranslation
import LegendreK6.TrapezoidHeightBound

/-! Exact height-kernel scaling and monotonicity of the complete finite
height budget, including the geometric residual. -/

namespace LegendreK6

open scoped BigOperators

theorem one_add_exp_div_translate_le (C d k : ℝ) (hd : 0 ≤ d) (hk : 0 < k) :
    1+Real.exp ((C+d)/k)/k ≤ (1+Real.exp (C/k)/k)*Real.exp (d/k) := by
  have he : 1 ≤ Real.exp (d/k) := Real.one_le_exp_iff.mpr (div_nonneg hd hk.le)
  rw [show (C+d)/k = C/k+d/k by ring, Real.exp_add]
  calc
    _ ≤ Real.exp (d/k)+Real.exp (C/k)*Real.exp (d/k)/k := by linarith
    _ = _ := by ring

theorem trapezoidHeightKernel_exp_translate (q u v : ℝ) :
    trapezoidHeightKernel (q*Real.exp v) (Real.exp (u+v)) =
      trapezoidHeightKernel q (Real.exp u) := by
  unfold trapezoidHeightKernel
  rw [Real.exp_add]
  congr 2 <;> field_simp <;> ring

theorem trapezoid_tail_coefficient_translate (q U v : ℝ) :
    16*(((4096:ℝ)/31)*(q*Real.exp v)^2)*Real.exp (-2*(U+v)) =
      16*(((4096:ℝ)/31)*q^2)*Real.exp (-2*U) := by
  have hp : (Real.exp v)^2 = Real.exp (2*v) := by
    simpa using (Real.exp_nat_mul v 2).symm
  rw [mul_pow, hp, show -2*(U+v) = -2*U+(-2*v) by ring, Real.exp_add]
  calc
    _ = (16*(((4096:ℝ)/31)*q^2)*Real.exp (-2*U)) *
        (Real.exp (2*v)*Real.exp (-2*v)) := by ring
    _ = _ := by rw [← Real.exp_add]; simp

theorem trapezoidHeightBudget_translation_le (s : ℕ → ℝ) (row : ℕ → Fin 12)
    (nSigma : ℕ) (A q : ℝ) (u : ℕ → ℝ) (nHeight : ℕ) (d k : ℝ)
    (hA : 167 ≤ A) (hq : 0 ≤ q) (hu : Monotone u) (hu0 : 28 ≤ u 0)
    (hd : 0 ≤ d) (hk : 4 ≤ k)
    (hgrid : ∀ j < nSigma, 1/2 ≤ s j ∧ s j ≤ s (j+1) ∧ s (j+1) ≤ 7/8 ∧
      s (j+1)-s j ≤ 1/1024) :
    trapezoidHeightBudget s row nSigma (A+d) (q*Real.exp (d/k))
      (fun j => u j+d/k) nHeight ≤ trapezoidHeightBudget s row nSigma A q u nHeight := by
  unfold trapezoidHeightBudget
  simp only [trapezoidHeightKernel_exp_translate]
  rw [trapezoid_tail_coefficient_translate]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro j _
    have hmass : 0 ≤ trapezoidHeightKernel q (Real.exp (u j)) -
        trapezoidHeightKernel q (Real.exp (u (j+1))) := by
      apply sub_nonneg.mpr
      exact trapezoidHeightKernel_antitone hq (Real.exp_pos _) (Real.exp_pos _)
        (Real.exp_le_exp.mpr (hu (Nat.le_succ j)))
    exact mul_le_mul_of_nonneg_left
      (densityGridPhi_translation_le s row nSigma A (u (j+1)) d k hA
        (hu0.trans (hu (Nat.zero_le _))) hd hk hgrid) hmass
  · exact mul_le_mul_of_nonneg_left
      (densityGridPhi_translation_le s row nSigma A (u nHeight) d k hA
        (hu0.trans (hu (Nat.zero_le _))) hd hk hgrid) (by positivity)

end LegendreK6
