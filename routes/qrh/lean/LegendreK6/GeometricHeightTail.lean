import LegendreK6.FiniteDensityGrid

/-!
# A conservative geometric height tail

Finite prefix sums suffice for every actual finite zero truncation. Heights
grow by four, the count envelope by eight, and the quadratic kernel decays
by sixteen. This retains all residual mass below the starting height.
-/

namespace LegendreK6

open scoped BigOperators

theorem decay_le_geometric_prefix (θ : ℕ → ℝ) (f t c : ℝ) (N : ℕ)
    (hc : 0 ≤ c) (hbase : f ≤ c)
    (hdecay : ∀ k, θ k < t → f ≤ c * (1/16 : ℝ)^k)
    (hcover : t ≤ θ (N+1)) :
    f ≤ c * ∑ k ∈ Finset.range (N+1),
      if t ≤ θ (k+1) then (1/16 : ℝ)^k else 0 := by
  induction N with
  | zero => simpa [hcover] using hbase
  | succ N ih =>
    rw [Finset.sum_range_succ]
    by_cases ht : t ≤ θ (N+1)
    · have hh := ih ht
      have hp : 0 ≤ (if t ≤ θ (N+1+1) then (1/16 : ℝ)^(N+1) else 0) := by
        split_ifs <;> positivity
      nlinarith
    · have hd := hdecay (N+1) (lt_of_not_ge ht)
      rw [ite_eq_left hcover]
      have hs : 0 ≤ ∑ k ∈ Finset.range (N+1),
          if t ≤ θ (k+1) then (1/16 : ℝ)^k else 0 := by
        apply Finset.sum_nonneg
        intro k _
        split_ifs <;> positivity
      nlinarith

theorem half_geometric_sum_le_two (N : ℕ) :
    (∑ k ∈ Finset.range N, (1/2 : ℝ)^k) ≤ 2 := by
  have h : (∑ k ∈ Finset.range N, (1/2 : ℝ)^k) = 2 * (1 - (1/2 : ℝ)^N) := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [h]
  have hp : 0 ≤ (1/2 : ℝ)^N := by positivity
  linarith

/-- A finite, weighted prefix-count bound; `16*c*B` bounds the whole
quadratic residual, including weights of heights below the first node. -/
theorem finite_geometric_prefix_bound {ι : Type*} (S : Finset ι)
    (height weight f : ι → ℝ) (θ : ℕ → ℝ) (c B : ℝ) (N : ℕ)
    (hc : 0 ≤ c) (hB : 0 ≤ B) (hw : ∀ i ∈ S, 0 ≤ weight i)
    (hbase : ∀ i ∈ S, f i ≤ c)
    (hdecay : ∀ i ∈ S, ∀ k, θ k < height i → f i ≤ c*(1/16 : ℝ)^k)
    (hcover : ∀ i ∈ S, height i ≤ θ (N+1))
    (hcount : ∀ k, (∑ i ∈ S, if height i ≤ θ (k+1) then weight i else 0) ≤
      B * (8 : ℝ)^(k+1)) :
    (∑ i ∈ S, weight i * f i) ≤ 16*c*B := by
  classical
  calc
    _ ≤ ∑ i ∈ S, weight i * (c * ∑ k ∈ Finset.range (N+1),
        if height i ≤ θ (k+1) then (1/16 : ℝ)^k else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (decay_le_geometric_prefix θ (f i) (height i) c N hc (hbase i hi)
          (hdecay i hi) (hcover i hi)) (hw i hi)
    _ = c * ∑ k ∈ Finset.range (N+1), (1/16 : ℝ)^k *
        ∑ i ∈ S, if height i ≤ θ (k+1) then weight i else 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> ring
    _ ≤ c * ∑ k ∈ Finset.range (N+1), (1/16 : ℝ)^k * (B * (8 : ℝ)^(k+1)) := by
      apply mul_le_mul_of_nonneg_left _ hc
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left (hcount k) (by positivity)
    _ = (8*c*B) * ∑ k ∈ Finset.range (N+1), (1/2 : ℝ)^k := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      have hp : (1/16 : ℝ)^k * (8 : ℝ)^k = (1/2 : ℝ)^k := by
        rw [← mul_pow]
        norm_num
      rw [pow_succ]
      rw [← hp]
      ring
    _ ≤ (8*c*B)*2 := mul_le_mul_of_nonneg_left
      (half_geometric_sum_le_two (N+1)) (by positivity)
    _ = _ := by ring

theorem finite_quadratic_residual_bound {ι : Type*} (S : Finset ι)
    (height weight : ι → ℝ) (R C B T : ℝ)
    (hR : 0 < R) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hw : ∀ i ∈ S, 0 ≤ weight i) (hT : ∀ i ∈ S, height i ≤ T)
    (hcount : ∀ k, (∑ i ∈ S, if height i ≤ R*(4 : ℝ)^(k+1) then weight i else 0) ≤
      B*(8 : ℝ)^(k+1)) :
    (∑ i ∈ S, weight i * (C / (max (height i) R)^2)) ≤ 16*(C/R^2)*B := by
  obtain ⟨N,hN⟩ := pow_unbounded_of_one_lt (T/R) (by norm_num : (1:ℝ)<4)
  have hTR : T ≤ R*(4 : ℝ)^(N+1) := by
    have hN' : T < R*(4 : ℝ)^N := by
      have hh := (div_lt_iff₀ hR).mp hN
      nlinarith
    have hp : (4 : ℝ)^N ≤ (4 : ℝ)^(N+1) :=
      pow_le_pow_right₀ (by norm_num) (Nat.le_succ N)
    nlinarith
  apply finite_geometric_prefix_bound S height weight
    (fun i => C/(max (height i) R)^2) (fun k => R*(4 : ℝ)^k)
    (C/R^2) B N (by positivity) hB hw
  · intro i _
    exact div_le_div_of_nonneg_left hC (sq_pos_of_pos hR)
      ((sq_le_sq₀ hR.le (hR.le.trans (le_max_right _ _))).mpr (le_max_right _ _))
  · intro i _ k hk
    have hRk : 0 < R*(4 : ℝ)^k := by positivity
    have hbig : R*(4 : ℝ)^k ≤ max (height i) R := hk.le.trans (le_max_left _ _)
    calc
      _ ≤ C/(R*(4 : ℝ)^k)^2 := div_le_div_of_nonneg_left hC
        (sq_pos_of_pos hRk)
        ((sq_le_sq₀ hRk.le (hRk.le.trans hbig)).mpr hbig)
      _ = (C/R^2)*(1/16 : ℝ)^k := by
        have hp : ((4 : ℝ)^k)^2 = (16 : ℝ)^k := by
          rw [← pow_mul, Nat.mul_comm, pow_mul]
          norm_num
        rw [mul_pow, hp, div_pow]
        simp only [one_pow]
        ring
  · intro i hi
    exact (hT i hi).trans hTR
  · exact hcount

end LegendreK6
