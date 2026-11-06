import LegendreK6.PrimeExtraction

/-!
# Actual prime-power budgets

These bounds concern Mathlib's von Mangoldt function and Chebyshev functions,
not a freely supplied error variable. No zero-density or QRH input is needed.
-/

namespace LegendreK6

open scoped BigOperators

/-- A bounded weight on a finite integer interval is controlled by the actual
nonprime part of the Chebyshev sum. Only an upper bound on the weight is needed. -/
theorem weightedNonprime_le_psi_sub_theta (S : Finset ℕ) (w : ℕ → ℝ)
    (Y W : ℝ) (hW : 0 ≤ W)
    (hS : S ⊆ Finset.Ioc 0 ⌊Y⌋₊)
    (hw : ∀ m ∈ S, w m ≤ W) :
    weightedNonprime S w ≤ W * (Chebyshev.psi Y - Chebyshev.theta Y) := by
  classical
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.mul_sum]
  unfold weightedNonprime
  calc
    _ ≤ ∑ m ∈ S.filter (fun m => ¬Nat.Prime m),
        W * ArithmeticFunction.vonMangoldt m := by
      apply Finset.sum_le_sum
      intro m hm
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hw m (Finset.mem_filter.mp hm).1)
        ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset_filter _ hS
      · intro m _ _
        exact mul_nonneg hW ArithmeticFunction.vonMangoldt_nonneg

/-- The unconditional Chebyshev bound gives a concrete weighted prime-power
budget for every real upper endpoint at least one. -/
theorem weightedNonprime_le_sqrt_log (S : Finset ℕ) (w : ℕ → ℝ)
    (Y W : ℝ) (hY : 1 ≤ Y) (hW : 0 ≤ W)
    (hS : S ⊆ Finset.Ioc 0 ⌊Y⌋₊)
    (hw : ∀ m ∈ S, w m ≤ W) :
    weightedNonprime S w ≤ 2 * W * Real.sqrt Y * Real.log Y := by
  calc
    _ ≤ W * (Chebyshev.psi Y - Chebyshev.theta Y) :=
      weightedNonprime_le_psi_sub_theta S w Y W hW hS hw
    _ ≤ W * (2 * Real.sqrt Y * Real.log Y) := by
      apply mul_le_mul_of_nonneg_left _ hW
      exact (le_abs_self _).trans (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hY)
    _ = _ := by ring

/-- In the parameter range used by the manuscript, the preceding bound is
stronger than the manuscript's square-log prime-power budget. -/
theorem weightedNonprime_le_manuscript_budget (S : Finset ℕ) (w : ℕ → ℝ)
    (Y W : ℝ) (hY : 1 ≤ Y) (hW : 0 ≤ W)
    (hlog : 4 * Real.log 2 ≤ Real.log Y)
    (hS : S ⊆ Finset.Ioc 0 ⌊Y⌋₊)
    (hw : ∀ m ∈ S, w m ≤ W) :
    weightedNonprime S w ≤ W * Real.sqrt Y * (Real.log Y) ^ 2 / (2 * Real.log 2) := by
  apply (weightedNonprime_le_sqrt_log S w Y W hY hW hS hw).trans
  apply (le_div_iff₀ (show 0 < 2 * Real.log 2 by positivity)).2
  have hn := mul_nonneg
    (mul_nonneg (mul_nonneg hW (Real.sqrt_nonneg Y)) (Real.log_nonneg hY))
    (sub_nonneg.mpr hlog)
  nlinarith

/-- If an open interval contains no prime, its Chebyshev increment can consist
only of the right endpoint, whose possible contribution is `log y`. -/
theorem theta_sub_le_log_of_no_prime (x y : ℝ) (hx : 0 ≤ x)
    (hxy : x ≤ y) (hy : 1 ≤ y) (hno : ¬PrimeInOpenInterval x y) :
    Chebyshev.theta y - Chebyshev.theta x ≤ Real.log y := by
  classical
  let A := (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime
  let B := (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime
  have hBA : B ⊆ A :=
    Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right (Nat.floor_mono hxy))
  have hsum : Chebyshev.theta y - Chebyshev.theta x =
      ∑ p ∈ A \ B, Real.log (p : ℝ) := by
    have hs := Finset.sum_sdiff hBA (f := fun p : ℕ => Real.log (p : ℝ))
    change (∑ p ∈ A, Real.log (p : ℝ)) - (∑ p ∈ B, Real.log (p : ℝ)) = _
    linarith
  have hend : ∀ p ∈ A \ B, (p : ℝ) = y := by
    intro p hp
    obtain ⟨hpA, hpB⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hpI, hpprime⟩ := Finset.mem_filter.mp hpA
    obtain ⟨hp0, hpy⟩ := Finset.mem_Ioc.mp hpI
    have hpy' : (p : ℝ) ≤ y := (Nat.le_floor_iff (by linarith)).mp hpy
    have hpx : x < (p : ℝ) := by
      apply (Nat.floor_lt hx).mp
      by_contra! hn
      exact hpB (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp0, hn⟩, hpprime⟩)
    apply le_antisymm hpy'
    by_contra! hn
    exact hno ⟨p, hpprime, hpx, hn⟩
  rw [hsum]
  by_cases hne : (A \ B).Nonempty
  · obtain ⟨p, hp⟩ := hne
    have hsingle : A \ B = {p} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hp, ?_⟩
      intro q hq
      exact_mod_cast (hend q hq).trans (hend p hp).symm
    rw [hsingle, Finset.sum_singleton, hend p hp]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
    exact Real.log_nonneg hy

/-- A theta increment strictly larger than the possible right-endpoint
contribution forces a prime strictly between the two endpoints. -/
theorem prime_of_theta_sub_gt_log (x y : ℝ) (hx : 0 ≤ x)
    (hxy : x ≤ y) (hy : 1 ≤ y)
    (hgain : Real.log y < Chebyshev.theta y - Chebyshev.theta x) :
    PrimeInOpenInterval x y := by
  by_contra hno
  exact (not_lt_of_ge (theta_sub_le_log_of_no_prime x y hx hxy hy hno)) hgain

/-- The manuscript's unweighted prime-power budget, for its actual large-Y
domain, follows from an already formalized unconditional Chebyshev estimate. -/
theorem psi_sub_theta_le_manuscript_budget (Y : ℝ) (hY : 1 ≤ Y)
    (hlog : 4 * Real.log 2 ≤ Real.log Y) :
    Chebyshev.psi Y - Chebyshev.theta Y ≤
      Real.sqrt Y * (Real.log Y) ^ 2 / (2 * Real.log 2) := by
  have h := weightedNonprime_le_manuscript_budget
    (Finset.Ioc 0 ⌊Y⌋₊) (fun _ => 1) Y 1 hY (by norm_num) hlog
    (fun _ h => h) (by simp)
  simpa [weightedNonprime, Chebyshev.psi_sub_theta_eq_sum_not_prime] using h

/-- This form is directly usable with a lower bound obtained from a truncated
explicit formula for the actual Chebyshev psi function. -/
theorem prime_of_psi_sub_gt_manuscript_budget (x y : ℝ) (hx : 0 ≤ x)
    (hxy : x ≤ y) (hy : 1 ≤ y) (hlog : 4 * Real.log 2 ≤ Real.log y)
    (hgain : Real.sqrt y * (Real.log y) ^ 2 / (2 * Real.log 2) + Real.log y <
      Chebyshev.psi y - Chebyshev.psi x) :
    PrimeInOpenInterval x y := by
  apply prime_of_theta_sub_gt_log x y hx hxy hy
  have hpow := psi_sub_theta_le_manuscript_budget y hy hlog
  have hleft := Chebyshev.theta_le_psi x
  linarith

end LegendreK6
