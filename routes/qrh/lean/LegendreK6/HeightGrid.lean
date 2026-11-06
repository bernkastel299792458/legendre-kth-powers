import LegendreK6.FiniteDensityGrid
import LegendreK6.HeightKernel

/-! Finite height summation with its residual explicitly retained. -/

namespace LegendreK6

open scoped BigOperators

theorem trapezoidHeightKernel_nonneg {q T : ℝ} (hq : 0 ≤ q) (hT : 0 < T) :
    0 ≤ trapezoidHeightKernel q T := by
  unfold trapezoidHeightKernel
  positivity

theorem trapezoidHeightKernel_le_one (q T : ℝ) : trapezoidHeightKernel q T ≤ 1 :=
  min_le_left _ _

theorem trapezoidHeightKernel_le_quadratic (q T : ℝ) :
    trapezoidHeightKernel q T ≤ (4096/31 : ℝ)*q^2/T^2 :=
  (min_le_right _ _).trans (min_le_right _ _)

theorem trapezoidHeightKernel_antitone {q : ℝ} (hq : 0 ≤ q) :
    AntitoneOn (trapezoidHeightKernel q) (Set.Ioi 0) := by
  intro T hT U hU hTU
  unfold trapezoidHeightKernel
  apply min_le_min le_rfl
  apply min_le_min
  · exact div_le_div_of_nonneg_left (by positivity) hT hTU
  · exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hT)
      (sq_le_sq₀ hT.le hU.le |>.mpr hTU)

/-- A purely finite Stieltjes upper sum. The last term is retained even for
heights below the final node, so no endpoint residual is discarded. -/
theorem kernel_le_height_grid (g : ℝ → ℝ) (u : ℕ → ℝ) (n : ℕ) (t : ℝ)
    (hg : AntitoneOn g (Set.Ioi 0)) (hg1 : ∀ t, 0 < t → g t ≤ 1)
    (hu : Monotone u) (hu0 : 0 < u 0) (hstart : g (u 0) = 1) (ht : 0 < t) :
    g t ≤ (∑ j ∈ Finset.range n, if t ≤ u (j+1) then g (u j) - g (u (j+1)) else 0) +
      g (max t (u n)) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_add]
    by_cases htu : t ≤ u 0
    · rw [max_eq_right htu, hstart]
      exact hg1 t ht
    · rw [max_eq_left (le_of_not_ge htu)]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hun : 0 < u n := hu0.trans_le (hu (Nat.zero_le n))
    have hun1 : 0 < u (n+1) := hu0.trans_le (hu (Nat.zero_le (n+1)))
    have huu : u n ≤ u (n+1) := hu (Nat.le_succ n)
    by_cases htn : t ≤ u n
    · rw [max_eq_right htn] at ih
      rw [ite_eq_left (htn.trans huu), max_eq_right (htn.trans huu)]
      linarith
    · have hnt : u n ≤ t := le_of_not_ge htn
      rw [max_eq_left hnt] at ih
      by_cases htn1 : t ≤ u (n+1)
      · rw [ite_eq_left htn1, max_eq_right htn1]
        have hgnt := hg hun ht hnt
        linarith
      · rw [ite_eq_right htn1, max_eq_left (le_of_not_ge htn1), add_zero]
        exact ih

theorem finite_sum_kernel_le_height_grid {ι : Type*} (S : Finset ι)
    (height weight : ι → ℝ) (g : ℝ → ℝ) (u : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i ∈ S, 0 ≤ weight i) (ht : ∀ i ∈ S, 0 < height i)
    (hg : AntitoneOn g (Set.Ioi 0)) (hg1 : ∀ t, 0 < t → g t ≤ 1)
    (hu : Monotone u) (hu0 : 0 < u 0) (hstart : g (u 0) = 1) :
    (∑ i ∈ S, weight i * g (height i)) ≤
      (∑ j ∈ Finset.range n, (g (u j) - g (u (j+1))) *
        ∑ i ∈ S, if height i ≤ u (j+1) then weight i else 0) +
      ∑ i ∈ S, weight i * g (max (height i) (u n)) := by
  classical
  calc
    _ ≤ ∑ i ∈ S, weight i * ((∑ j ∈ Finset.range n,
        if height i ≤ u (j+1) then g (u j) - g (u (j+1)) else 0) +
        g (max (height i) (u n))) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (kernel_le_height_grid g u n (height i) hg hg1 hu hu0 hstart (ht i hi)) (hw i hi)
    _ = _ := by
      simp_rw [mul_add, Finset.mul_sum]
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> ring

end LegendreK6
