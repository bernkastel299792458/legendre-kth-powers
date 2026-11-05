/-
Copyright (c) 2026 AI4Math legendre_k67 project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI4Math legendre_k67 project (drafted with Claude)
-/
import Mathlib

/-!
# 命题 H / S 中的初等积分估计

∫_a^b e^{−(1−σ)λ} dσ ≤ e^{−(1−b)λ}/λ（λ > 0，a ≤ b）。
命题 H、S 在 KLN 段和 Bellotti 段的积分都用到这一步（再乘以常数 L·C 等）。
-/

namespace LegendreK67

open Real intervalIntegral

theorem integral_exp_bound (a b l : ℝ) (hab : a ≤ b) (hl : 0 < l) :
    ∫ σ in a..b, Real.exp (-(1 - σ) * l) ≤ Real.exp (-(1 - b) * l) / l := by
  have hfun : (fun σ : ℝ => Real.exp (-(1 - σ) * l)) = fun σ => Real.exp (l * σ + (-l)) := by
    funext σ; ring_nf
  rw [hfun, intervalIntegral.integral_comp_mul_add (fun t => Real.exp t) hl.ne' (-l),
    integral_exp]
  have h1 : Real.exp (l * b + -l) = Real.exp (-(1 - b) * l) := by ring_nf
  have h2 : 0 < Real.exp (l * a + -l) := Real.exp_pos _
  rw [h1, smul_eq_mul]
  rw [div_eq_inv_mul]
  have hinv : 0 < l⁻¹ := inv_pos.mpr hl
  nlinarith [mul_pos hinv h2]

end LegendreK67
