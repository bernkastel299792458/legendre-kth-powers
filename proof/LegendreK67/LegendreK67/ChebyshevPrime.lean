/-
Copyright (c) 2026 AI4Math legendre_k67 project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI4Math legendre_k67 project (drafted with Claude)
-/
import Mathlib

/-!
# θ 的增量为正 ⇒ 区间中有素数

用 Mathlib 的 `Chebyshev.theta`：θ(x) = Σ_{p ≤ x, p 素数} log p。
-/

namespace LegendreK67

open Real Finset

/-- 若 `θ y - θ x > 0`，则存在素数 `p` 满足 `x < p ≤ y`。 -/
theorem exists_prime_of_theta_sub_pos {x y : ℝ}
    (h : 0 < Chebyshev.theta y - Chebyshev.theta x) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ y := by
  by_contra hne
  push Not at hne
  have hsub : (Ioc 0 ⌊y⌋₊).filter Nat.Prime ⊆ (Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
    obtain ⟨⟨h0, hpy⟩, hpr⟩ := hp
    refine ⟨⟨h0, ?_⟩, hpr⟩
    have hy1 : 1 ≤ ⌊y⌋₊ := le_trans h0 hpy
    have hy0 : 0 ≤ y := by
      have := Nat.one_le_floor_iff y |>.mp hy1
      linarith
    have hpy' : (p : ℝ) ≤ y := le_trans (by exact_mod_cast hpy) (Nat.floor_le hy0)
    by_contra hpx
    push Not at hpx
    have hxp : x < p := Nat.lt_of_floor_lt hpx
    exact absurd (hne p hpr hxp) (not_lt.mpr hpy')
  have hle : Chebyshev.theta y ≤ Chebyshev.theta x := by
    unfold Chebyshev.theta
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp _
    simp only [Finset.mem_filter] at hp
    exact Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)
  linarith

end LegendreK67
