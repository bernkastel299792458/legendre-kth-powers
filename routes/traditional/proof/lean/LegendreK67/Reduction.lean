/-
Copyright (c) 2026 AI4Math legendre_k67 project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI4Math legendre_k67 project (drafted with Claude)
-/
import Mathlib

/-!
# 归约：从 (3.2)_{k₀} 到"相邻 k 次方之间有素数"（k ≥ k₀）

本文件完整形式化以下初等事实（无 `sorry`、无新公理）：

* `key_ineq`：当 1 ≤ k₀ ≤ k、n ≥ 1 时，k₀·(n^k)^(1−1/k₀) ≤ k·n^(k−1)。
* `binom_lower`：当 k ≥ 2 时，n^k + k·n^(k−1) + 1 ≤ (n+1)^k。
* `main_of_gap`：设 k₀ ≥ 62。若对所有实数 x ≥ 4·10^18，区间 (x, x + k₀·x^(1−1/k₀)] 中都有素数，
  则对所有 k ≥ k₀ 和 n ≥ 1，(n^k, (n+1)^k) 中都有素数。
-/

namespace LegendreK67

open Real

/-- 区间 `(x, x + k₀ x^{1-1/k₀}]` 中有素数（x 为实数）。 -/
def PrimeInShortInterval (k₀ : ℕ) (x : ℝ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + k₀ * x ^ ((1 : ℝ) - 1 / k₀)

/-- 对所有 `x ≥ X`，`PrimeInShortInterval k₀ x` 成立。 -/
def GapProperty (k₀ : ℕ) (X : ℝ) : Prop :=
  ∀ x : ℝ, X ≤ x → PrimeInShortInterval k₀ x

/-- 关键不等式：`k₀ * (n^k)^(1 - 1/k₀) ≤ k * n^(k-1)`，其中 `1 ≤ k₀ ≤ k`、`n ≥ 1`。 -/
theorem key_ineq (k₀ k n : ℕ) (hk₀ : 1 ≤ k₀) (hk : k₀ ≤ k) (hn : 1 ≤ n) :
    (k₀ : ℝ) * ((n : ℝ) ^ k) ^ ((1 : ℝ) - 1 / k₀) ≤ (k : ℝ) * (n : ℝ) ^ (k - 1) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hk1 : 1 ≤ k := le_trans hk₀ hk
  have hk₀r : (0 : ℝ) < k₀ := by exact_mod_cast hk₀
  have hkk : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : ((n : ℝ) ^ k) ^ ((1 : ℝ) - 1 / k₀) = (n : ℝ) ^ ((k : ℝ) * ((1 : ℝ) - 1 / k₀)) := by
    rw [Real.rpow_mul hn0, Real.rpow_natCast]
  -- k(1 − 1/k₀) ≤ k − 1，因为 k/k₀ ≥ 1
  have hexp : (k : ℝ) * ((1 : ℝ) - 1 / k₀) ≤ ((k - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hk1]
    have hdiv : (1 : ℝ) ≤ (k : ℝ) / k₀ := by rw [le_div_iff₀ hk₀r]; linarith
    have e : (k : ℝ) * ((1 : ℝ) - 1 / k₀) = k - (k : ℝ) / k₀ := by field_simp
    rw [e]; push_cast; linarith
  have h2 : (n : ℝ) ^ ((k : ℝ) * ((1 : ℝ) - 1 / k₀)) ≤ (n : ℝ) ^ (k - 1) := by
    calc (n : ℝ) ^ ((k : ℝ) * ((1 : ℝ) - 1 / k₀))
        ≤ (n : ℝ) ^ (((k - 1 : ℕ) : ℝ)) := Real.rpow_le_rpow_of_exponent_le hn1 hexp
      _ = (n : ℝ) ^ (k - 1) := Real.rpow_natCast _ _
  have hpos : (0 : ℝ) ≤ (n : ℝ) ^ (k - 1) := pow_nonneg hn0 _
  rw [h1]
  calc (k₀ : ℝ) * (n : ℝ) ^ ((k : ℝ) * ((1 : ℝ) - 1 / k₀))
      ≤ (k₀ : ℝ) * (n : ℝ) ^ (k - 1) := by gcongr
    _ ≤ (k : ℝ) * (n : ℝ) ^ (k - 1) := by gcongr

/-- 二项式下界：`n^(m+2) + (m+2) n^(m+1) + 1 ≤ (n+1)^(m+2)`。 -/
theorem binom_lower_aux (n m : ℕ) :
    n ^ (m + 2) + (m + 2) * n ^ (m + 1) + 1 ≤ (n + 1) ^ (m + 2) := by
  induction m with
  | zero => ring_nf; omega
  | succ m ih =>
    have e1 : (n + 1) ^ (m + 1 + 2) = (n + 1) ^ (m + 2) * (n + 1) := by ring
    have e2 : n ^ (m + 1 + 2) = n ^ (m + 2) * n := by ring
    have e3 : n ^ (m + 1 + 1) = n ^ (m + 2) := by ring
    rw [e1, e2, e3]
    have h := Nat.mul_le_mul_right (n + 1) ih
    have hge : n ^ (m + 2) * n + (↑(m + 1) + 2) * n ^ (m + 2) + 1
        ≤ (n ^ (m + 2) + (m + 2) * n ^ (m + 1) + 1) * (n + 1) := by
      have : n ^ (m + 2) = n ^ (m + 1) * n := by ring
      nlinarith [Nat.zero_le (n ^ (m + 1)), Nat.zero_le n, Nat.zero_le ((m + 2) * n ^ (m + 1))]
    exact le_trans hge h

theorem binom_lower (n k : ℕ) (hk : 2 ≤ k) :
    n ^ k + k * n ^ (k - 1) + 1 ≤ (n + 1) ^ k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have := binom_lower_aux n m
  simpa [Nat.add_sub_cancel, show m + 2 - 1 = m + 1 by omega] using this

/-- 归约定理：(3.2)_{k₀} 型的短区间素数结论 ⇒ 对所有 k ≥ k₀，相邻 k 次方之间有素数。 -/
theorem main_of_gap (k₀ : ℕ) (hk₀ : 62 ≤ k₀) (h : GapProperty k₀ (4 * 10 ^ 18)) (k n : ℕ)
    (hk : k₀ ≤ k) (hn : 1 ≤ n) : ∃ p : ℕ, p.Prime ∧ n ^ k < p ∧ p < (n + 1) ^ k := by
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · -- n = 1：取 p = 2
    have hn1 : n = 1 := by omega
    subst hn1
    refine ⟨2, Nat.prime_two, by simp, ?_⟩
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at this ⊢
    omega
  · -- n ≥ 2：取 x = n^k
    set x : ℝ := (n : ℝ) ^ k with hx
    have hx_big : (4 * 10 ^ 18 : ℝ) ≤ x := by
      have h2 : (2 : ℝ) ^ 62 ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
      have h3 : (2 : ℝ) ^ k ≤ (n : ℝ) ^ k :=
        pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hn2) k
      have h4 : (4 * 10 ^ 18 : ℝ) ≤ (2 : ℝ) ^ 62 := by norm_num
      linarith
    obtain ⟨p, hp, hxp, hpx⟩ := h x hx_big
    refine ⟨p, hp, ?_, ?_⟩
    · have : ((n ^ k : ℕ) : ℝ) < p := by rw [Nat.cast_pow]; exact hxp
      exact_mod_cast this
    · have hkey := key_ineq k₀ k n (by omega) hk hn
      have hb := binom_lower n k (by omega)
      have hb' : ((n : ℝ) ^ k + (k : ℝ) * (n : ℝ) ^ (k - 1) + 1) ≤ ((n + 1 : ℕ) : ℝ) ^ k := by
        exact_mod_cast hb
      have hlt : (p : ℝ) < ((n + 1) ^ k : ℕ) := by
        push_cast at hb' ⊢
        linarith
      exact_mod_cast hlt

end LegendreK67
