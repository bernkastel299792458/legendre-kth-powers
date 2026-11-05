/-
Copyright (c) 2026 AI4Math legendre_k67 project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI4Math legendre_k67 project (drafted with Claude)
-/
import LegendreK67.Reduction
import LegendreK67.ChebyshevPrime

/-!
# 下段：从 Cully-Hugill–Lee 的区间估计推出 (3.2)_{k₀}

Cully-Hugill–Lee（Math. Comp. 2022，arXiv:2103.05986v3 Thm 1）：对表中每一对 (Δ, x₀)，
所有 y ≥ x₀ 都使 (y(1 − 1/Δ), y] 中有素数。

取 y = x + h，h = k₀ x^{1−1/k₀}。若 k₀ x^{−1/k₀}(Δ − 1) ≥ 1，则 y(1−1/Δ) ≥ x，
于是 (x, x+h] 中有素数，从而 θ(x+h) − θ(x) > 0。
-/

namespace LegendreK67

open Real Finset

/-- 不等式 (3.2)_{k₀}：θ(x + k₀ x^{1-1/k₀}) − θ(x) > 0。 -/
def Ineq32 (k₀ : ℕ) (x : ℝ) : Prop :=
  0 < Chebyshev.theta (x + k₀ * x ^ ((1 : ℝ) - 1 / k₀)) - Chebyshev.theta x

/-- CHL 型区间估计：对所有 y ≥ x₀，(y(1−1/Δ), y] 中有素数。 -/
def CHLInterval (Δ x₀ : ℝ) : Prop :=
  ∀ y : ℝ, x₀ ≤ y → ∃ p : ℕ, p.Prime ∧ y * (1 - 1 / Δ) < p ∧ (p : ℝ) ≤ y

/-- 若 (x, y] 中有素数，则 θ(y) − θ(x) > 0。 -/
theorem theta_sub_pos_of_prime {x y : ℝ} {p : ℕ} (hp : p.Prime) (hxp : x < p) (hpy : (p : ℝ) ≤ y) :
    0 < Chebyshev.theta y - Chebyshev.theta x := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hy0 : 0 ≤ y := by linarith
  set Sx := (Ioc 0 ⌊x⌋₊).filter Nat.Prime
  set Sy := (Ioc 0 ⌊y⌋₊).filter Nat.Prime
  have hpSy : p ∈ Sy := by
    simp only [Sy, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hp.pos, Nat.le_floor hpy⟩, hp⟩
  have hpSx : p ∉ Sx := by
    intro hmem
    simp only [Sx, Finset.mem_filter, Finset.mem_Ioc] at hmem
    have hle : p ≤ ⌊x⌋₊ := hmem.1.2
    have hx0 : 0 ≤ x ∨ x < 0 := le_or_gt 0 x
    rcases hx0 with hx0 | hx0
    · have : (p : ℝ) ≤ x := le_trans (by exact_mod_cast hle) (Nat.floor_le hx0)
      linarith
    · have : ⌊x⌋₊ = 0 := Nat.floor_of_nonpos hx0.le
      have := hp.pos
      omega
  have hsub : insert p Sx ⊆ Sy := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hpSy
    · simp only [Sx, Sy, Finset.mem_filter, Finset.mem_Ioc] at hq ⊢
      refine ⟨⟨hq.1.1, ?_⟩, hq.2⟩
      exact le_trans hq.1.2 (Nat.floor_le_floor (by linarith))
  have h1 : Chebyshev.theta y ≥ ∑ q ∈ insert p Sx, Real.log q := by
    unfold Chebyshev.theta
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro q hq _
    simp only [Sy, Finset.mem_filter] at hq
    exact Real.log_nonneg (by exact_mod_cast hq.2.one_lt.le)
  rw [Finset.sum_insert hpSx] at h1
  have h2 : Chebyshev.theta x = ∑ q ∈ Sx, Real.log q := rfl
  have h3 : 0 < Real.log p := Real.log_pos hp1
  linarith

/-- 下段的核心推导。 -/
theorem ineq32_of_CHL {k₀ : ℕ} {Δ x₀ x : ℝ} (hk₀ : 1 ≤ k₀) (hΔ : 1 < Δ) (hCHL : CHLInterval Δ x₀)
    (hx : x₀ ≤ x) (hxpos : 0 < x) (hcond : 1 ≤ k₀ * x ^ (-(1 : ℝ) / k₀) * (Δ - 1)) :
    Ineq32 k₀ x := by
  unfold Ineq32
  have hk₀r : (0 : ℝ) < k₀ := by exact_mod_cast hk₀
  set h : ℝ := k₀ * x ^ ((1 : ℝ) - 1 / k₀) with hh
  -- h = x · k₀ x^{−1/k₀}
  have hsplit : x ^ ((1 : ℝ) - 1 / k₀) = x * x ^ (-(1 : ℝ) / k₀) := by
    rw [show (1 : ℝ) - 1 / k₀ = 1 + (-(1 : ℝ) / k₀) by ring, Real.rpow_add hxpos, Real.rpow_one]
  have hh' : h = x * (k₀ * x ^ (-(1 : ℝ) / k₀)) := by rw [hh, hsplit]; ring
  have hΔpos : 0 < Δ := by linarith
  have key : x ≤ (x + h) * (1 - 1 / Δ) := by
    have e : (x + h) * (1 - 1 / Δ) = ((x + h) * (Δ - 1)) / Δ := by field_simp
    rw [e, le_div_iff₀ hΔpos]
    have : x ≤ h * (Δ - 1) := by
      rw [hh']
      have := mul_le_mul_of_nonneg_left hcond hxpos.le
      nlinarith [this]
    nlinarith
  have hhpos : 0 < h := by
    rw [hh']; exact mul_pos hxpos (mul_pos hk₀r (Real.rpow_pos_of_pos hxpos _))
  obtain ⟨p, hp, hlow, hup⟩ := hCHL (x + h) (by linarith)
  exact theta_sub_pos_of_prime hp (lt_of_le_of_lt key hlow) hup

/-- 若 log x ≤ a，则 x^{−1/k₀} ≥ exp(−a/k₀)。 -/
theorem rpow_neg_ge_of_log_le {k₀ : ℕ} {x a : ℝ} (hk₀ : 1 ≤ k₀) (hx : 0 < x)
    (h : Real.log x ≤ a) : Real.exp (-a / k₀) ≤ x ^ (-(1 : ℝ) / k₀) := by
  have hk₀r : (0 : ℝ) < k₀ := by exact_mod_cast hk₀
  rw [Real.rpow_def_of_pos hx]
  apply Real.exp_le_exp.mpr
  have : Real.log x * (-(1 : ℝ) / k₀) = -(Real.log x) / k₀ := by ring
  rw [this]
  exact div_le_div_of_nonneg_right (by linarith) hk₀r.le

/-- 区间版：若 exp(a/k₀) ≤ k₀(Δ−1)，则对所有 x₀ ≤ x、log x ≤ a，(3.2)_{k₀} 成立。 -/
theorem ineq32_of_CHL_range {k₀ : ℕ} {Δ x₀ a x : ℝ} (hk₀ : 1 ≤ k₀) (hΔ : 1 < Δ)
    (hCHL : CHLInterval Δ x₀) (hnum : Real.exp (a / k₀) ≤ k₀ * (Δ - 1)) (hx : x₀ ≤ x)
    (hxpos : 0 < x) (hla : Real.log x ≤ a) : Ineq32 k₀ x := by
  apply ineq32_of_CHL hk₀ hΔ hCHL hx hxpos
  have h1 := rpow_neg_ge_of_log_le hk₀ hxpos hla
  have h2 : Real.exp (-a / k₀) * Real.exp (a / k₀) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hΔ1 : 0 < Δ - 1 := by linarith
  have hk₀r : (0 : ℝ) < k₀ := by exact_mod_cast hk₀
  have h3 : 1 ≤ Real.exp (-a / k₀) * (k₀ * (Δ - 1)) := by
    calc (1 : ℝ) = Real.exp (-a / k₀) * Real.exp (a / k₀) := h2.symm
      _ ≤ Real.exp (-a / k₀) * (k₀ * (Δ - 1)) :=
          mul_le_mul_of_nonneg_left hnum (Real.exp_pos _).le
  calc (1 : ℝ) ≤ Real.exp (-a / k₀) * (k₀ * (Δ - 1)) := h3
    _ ≤ x ^ (-(1 : ℝ) / k₀) * (k₀ * (Δ - 1)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = k₀ * x ^ (-(1 : ℝ) / k₀) * (Δ - 1) := by ring

end LegendreK67
