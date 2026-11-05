/-
Copyright (c) 2026 AI4Math legendre_k67 project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI4Math legendre_k67 project (drafted with Claude)
-/
import LegendreK67.Reduction
import LegendreK67.ChebyshevPrime
import LegendreK67.CHL

/-!
# 拼装：四段区间 ⇒ 主定理（参数 k₀ 及 L₁ < L₂ < L₃）

不等式 (3.2)_{k₀} 写成 `Ineq32 k₀ x`。证明的四段（见 `proof/manuscript.md` §10）以**显式命名的假设**进入：

* `CHL1`、`CHL2`：Cully-Hugill–Lee（arXiv:2103.05986v3 Thm 1）的两对 (Δ, x₀) =
  (3.90970·10^7, 4·10^18) 与 (2.51949·10^11, e^600)。
* `num1`、`num2`：两个数值事实，由 arb 验证（`code/numeric_facts.py`）。
  由 CHL1、CHL2、num1、num2 在 Lean 中推出 log x ≤ L₁ 时的 (3.2)（`CHL.lean`）。
* `Hsmooth`：命题 S 加证书，L₁ ≤ log x ≤ L₂。
* `Hhyb`：命题 H 加证书，L₂ ≤ log x ≤ L₃。
* `Htail`：尾部引理 Lemma T（`code/tail.py`），log x ≥ L₃。

阶段性成果的两个实例（v4）：
* `main_k70`：k₀ = 70，L₁ = 2186309/1024，L₂ = 9521，L₃ = 10^8（常数组 4.896 / 21.233 / 54.004）；
* `main_k74`：k₀ = 74，L₁ = 578863/256，L₂ = 7343，L₃ = 10^8（全部已发表的常数 5.558691 / 21.233 / 54.004）。

**Lean 只检验这些假设能逻辑地推出主定理。** 假设本身（解析输入、命题 S/H、Lemma T、arb 证书）
没有在 Lean 中证明；"无 sorry"只针对这里的记账部分，不代表核心解析论证已被机器验证。
-/

namespace LegendreK67

open Real

/-- 四段假设（参数：k₀ 与分界点 L₁, L₂, L₃，均为 log x 的值）。 -/
structure Hypotheses (k₀ : ℕ) (L₁ L₂ L₃ : ℝ) : Prop where
  CHL1 : CHLInterval 39097000 (4 * 10 ^ 18)
  CHL2 : CHLInterval 251949000000 (Real.exp 600)
  num1 : Real.exp (600 / k₀) ≤ k₀ * ((39097000 : ℝ) - 1)
  num2 : Real.exp (L₁ / k₀) ≤ k₀ * ((251949000000 : ℝ) - 1)
  Hsmooth : ∀ x : ℝ, 0 < x → L₁ ≤ Real.log x → Real.log x ≤ L₂ → Ineq32 k₀ x
  Hhyb : ∀ x : ℝ, 0 < x → L₂ ≤ Real.log x → Real.log x ≤ L₃ → Ineq32 k₀ x
  Htail : ∀ x : ℝ, 0 < x → L₃ ≤ Real.log x → Ineq32 k₀ x

/-- 四段覆盖 x ≥ 4·10^18。 -/
theorem ineq32_all {k₀ : ℕ} {L₁ L₂ L₃ : ℝ} (hk₀ : 1 ≤ k₀) (H : Hypotheses k₀ L₁ L₂ L₃) (x : ℝ)
    (hx : 4 * 10 ^ 18 ≤ x) : Ineq32 k₀ x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  by_cases h0 : Real.log x ≤ 600
  · exact ineq32_of_CHL_range hk₀ (by norm_num) H.CHL1 H.num1 hx hx0 h0
  push Not at h0
  by_cases h1 : Real.log x ≤ L₁
  · have hx600 : Real.exp 600 ≤ x := by
      calc Real.exp 600 ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr h0.le
        _ = x := Real.exp_log hx0
    exact ineq32_of_CHL_range hk₀ (by norm_num) H.CHL2 H.num2 hx600 hx0 h1
  push Not at h1
  by_cases h2 : Real.log x ≤ L₂
  · exact H.Hsmooth x hx0 h1.le h2
  push Not at h2
  by_cases h3 : Real.log x ≤ L₃
  · exact H.Hhyb x hx0 h2.le h3
  push Not at h3
  exact H.Htail x hx0 h3.le

/-- (3.2)_{k₀} ⇒ 短区间中有素数。 -/
theorem gap_of_hypotheses {k₀ : ℕ} {L₁ L₂ L₃ : ℝ} (hk₀ : 1 ≤ k₀) (H : Hypotheses k₀ L₁ L₂ L₃) :
    GapProperty k₀ (4 * 10 ^ 18) := by
  intro x hx
  exact exists_prime_of_theta_sub_pos (ineq32_all hk₀ H x hx)

/-- **主定理（一般形式）**：在四段假设下，对所有 k ≥ k₀ ≥ 62、n ≥ 1，存在素数 p 满足 n^k < p < (n+1)^k。 -/
theorem primes_between_consecutive_powers {k₀ : ℕ} {L₁ L₂ L₃ : ℝ} (hk₀ : 62 ≤ k₀)
    (H : Hypotheses k₀ L₁ L₂ L₃) (k n : ℕ) (hk : k₀ ≤ k) (hn : 1 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ n ^ k < p ∧ p < (n + 1) ^ k :=
  main_of_gap k₀ hk₀ (gap_of_hypotheses (by omega) H) k n hk hn

/-- **阶段性成果，高置信版**：k₀ = 70（常数组 4.896 / 21.233 / 54.004）。 -/
theorem main_k70 (H : Hypotheses 70 (2186309 / 1024) 9521 (10 ^ 8)) (k n : ℕ) (hk : 70 ≤ k)
    (hn : 1 ≤ n) : ∃ p : ℕ, p.Prime ∧ n ^ k < p ∧ p < (n + 1) ^ k :=
  primes_between_consecutive_powers (by norm_num) H k n hk hn

/-- **阶段性成果，保守版**：k₀ = 74（全部已发表的常数 5.558691 / 21.233 / 54.004）。 -/
theorem main_k74 (H : Hypotheses 74 (578863 / 256) 7343 (10 ^ 8)) (k n : ℕ) (hk : 74 ≤ k)
    (hn : 1 ≤ n) : ∃ p : ℕ, p.Prime ∧ n ^ k < p ∧ p < (n + 1) ^ k :=
  primes_between_consecutive_powers (by norm_num) H k n hk hn

end LegendreK67
