/-
Copyright (c) 2026 AI4Math legendre_k67 project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI4Math legendre_k67 project (drafted with Claude)
-/
import Mathlib

/-!
# 命题 H 与命题 S 的最后组合步骤（抽象形式）

这两个引理只检验"把各项误差加起来、小于 1 就得到正性"这一步的记账是否正确。
它们把解析输入当作抽象的实数不等式。
-/

namespace LegendreK67

/-- 命题 H 的组合：若 |ψ(x+h) − ψ(x) − h| ≤ (δ_zeros + δ_tr)·h，
(ψ−θ)(x+h) − (ψ−θ)(x) ≤ δ_pp·h，且 δ_zeros + δ_tr + δ_pp < 1，
则 θ(x+h) − θ(x) > 0。 -/
theorem propH_combination {dψ dθ h δz δt δp : ℝ} (hh : 0 < h)
    (hψ : |dψ - h| ≤ (δz + δt) * h) (hpp : dψ - dθ ≤ δp * h)
    (hδ : δz + δt + δp < 1) : 0 < dθ := by
  have h1 : h - (δz + δt) * h ≤ dψ := by linarith [neg_abs_le (dψ - h)]
  nlinarith

/-- 命题 S 的组合：显式公式 A = I − Z − E，A = P + Q（P：素数部分，Q：高次素数幂部分），
|Z| ≤ z·I，|E| ≤ e·I，0 ≤ Q ≤ q·I，I > 0，z + e + q < 1 ⇒ P > 0。 -/
theorem propS_combination {A P Q I Z E z e q : ℝ} (hI : 0 < I) (hEF : A = I - Z - E)
    (hAPQ : A = P + Q) (hZ : |Z| ≤ z * I) (hE : |E| ≤ e * I) (hQ : Q ≤ q * I)
    (hδ : z + e + q < 1) : 0 < P := by
  have hZ' : Z ≤ z * I := le_trans (le_abs_self Z) hZ
  have hE' : E ≤ e * I := le_trans (le_abs_self E) hE
  nlinarith

/-- 若一个有限加权和（权非负、只在素数上取值、支撑在 (x, x+h) 内）为正，则其中至少有一项为正。
这对应"Σ_{x<p<x+h} log p · φ((p−x)/h) > 0 ⇒ 存在素数 p ∈ (x, x+h)"。 -/
theorem exists_pos_term {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h : 0 < ∑ i ∈ s, f i) :
    ∃ i ∈ s, 0 < f i := by
  by_contra hne
  push Not at hne
  have : ∑ i ∈ s, f i ≤ 0 := Finset.sum_nonpos hne
  linarith

end LegendreK67
