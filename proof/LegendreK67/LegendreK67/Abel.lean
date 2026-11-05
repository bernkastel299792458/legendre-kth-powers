/-
Copyright (c) 2026 AI4Math legendre_k67 project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI4Math legendre_k67 project (drafted with Claude)
-/
import Mathlib

/-!
# 数值积分中使用的 Abel 求和不等式

在命题 S 的严格求积里，把 v 轴切成格子，S_i 是 Φ 在第 i 格上的上界，g_i = g̃(v_i)（单调不增、非负）。
我们用
  Σ_{i<N} S_i (g_i − g_{i+1}) ≤ Σ_{i<N} (M_i − M_{i−1}) ĝ_i,
其中 M_i = max_{l ≤ i} S_l（M_{−1} := 0），ĝ_i ≥ g_i。右边所有系数都非负，
所以可以逐项代入 g_i 的上界，从而避免球与球相减产生的依赖误差。本文件完整证明这个不等式。
-/

namespace LegendreK67

open Finset

/-- 累计最大值 `M i = max_{l ≤ i} S l`。 -/
noncomputable def runMax (S : ℕ → ℝ) : ℕ → ℝ
  | 0 => S 0
  | i + 1 => max (runMax S i) (S (i + 1))

/-- `prevMax S i = M (i-1)`，约定 `prevMax S 0 = 0`。 -/
noncomputable def prevMax (S : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | i + 1 => runMax S i

theorem le_runMax (S : ℕ → ℝ) (i : ℕ) : S i ≤ runMax S i := by
  cases i with
  | zero => simp [runMax]
  | succ i => simp [runMax]

theorem runMax_nonneg (S : ℕ → ℝ) (hS : ∀ i, 0 ≤ S i) (i : ℕ) : 0 ≤ runMax S i :=
  le_trans (hS i) (le_runMax S i)

theorem prevMax_le_runMax (S : ℕ → ℝ) (hS : ∀ i, 0 ≤ S i) (i : ℕ) :
    prevMax S i ≤ runMax S i := by
  cases i with
  | zero => simpa [prevMax] using runMax_nonneg S hS 0
  | succ i => simp [prevMax, runMax]

theorem prevMax_nonneg (S : ℕ → ℝ) (hS : ∀ i, 0 ≤ S i) (i : ℕ) : 0 ≤ prevMax S i := by
  cases i with
  | zero => simp [prevMax]
  | succ i => exact runMax_nonneg S hS i

/-- 分部求和恒等式。 -/
theorem abel_identity (S g : ℕ → ℝ) (N : ℕ) :
    ∑ i ∈ range N, runMax S i * (g i - g (i + 1)) + prevMax S N * g N
      = ∑ i ∈ range N, (runMax S i - prevMax S i) * g i := by
  induction N with
  | zero => simp [prevMax]
  | succ N ih =>
    rw [sum_range_succ, sum_range_succ, ← ih]
    simp only [prevMax]
    ring

/-- **Abel 求和不等式**（命题 S 的严格求积所用）。 -/
theorem abel_bound (S g gU : ℕ → ℝ) (N : ℕ) (hS : ∀ i, 0 ≤ S i)
    (hg : ∀ i, i < N → g (i + 1) ≤ g i) (hgN : 0 ≤ g N) (hgU : ∀ i, i < N → g i ≤ gU i) :
    ∑ i ∈ range N, S i * (g i - g (i + 1))
      ≤ ∑ i ∈ range N, (runMax S i - prevMax S i) * gU i := by
  have step1 : ∑ i ∈ range N, S i * (g i - g (i + 1))
      ≤ ∑ i ∈ range N, runMax S i * (g i - g (i + 1)) := by
    apply sum_le_sum
    intro i hi
    have hi' := mem_range.mp hi
    exact mul_le_mul_of_nonneg_right (le_runMax S i) (by linarith [hg i hi'])
  have step2 : ∑ i ∈ range N, runMax S i * (g i - g (i + 1))
      ≤ ∑ i ∈ range N, (runMax S i - prevMax S i) * g i := by
    have h := abel_identity S g N
    have : 0 ≤ prevMax S N * g N := mul_nonneg (prevMax_nonneg S hS N) hgN
    linarith
  have step3 : ∑ i ∈ range N, (runMax S i - prevMax S i) * g i
      ≤ ∑ i ∈ range N, (runMax S i - prevMax S i) * gU i := by
    apply sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hgU i (mem_range.mp hi))
      (by linarith [prevMax_le_runMax S hS i])
  linarith

end LegendreK67
