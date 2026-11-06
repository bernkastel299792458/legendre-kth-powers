import LegendreK6.Definitions

/-!
# Extracting a prime from a weighted von Mangoldt inequality

The sums here use Mathlib's actual von Mangoldt function, and the conclusion uses
`Nat.Prime`. The finite support and strict endpoint condition are explicit.
The analytic estimate supplying the weighted lower bound is not assumed proved
by this lemma; it is the separate zero-density/explicit-formula bridge.
-/

namespace LegendreK6

open scoped BigOperators

noncomputable def weightedMangoldt (S : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ m ∈ S, ArithmeticFunction.vonMangoldt m * w m

noncomputable def weightedNonprime (S : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ m ∈ S.filter (fun m => ¬Nat.Prime m), ArithmeticFunction.vonMangoldt m * w m

/-- A positive excess over all nonprime contributions forces a prime in support. -/
theorem prime_of_weighted_excess (S : Finset ℕ) (w : ℕ → ℝ) (x y : ℝ)
    (hsupport : ∀ m ∈ S, w m ≠ 0 → x < (m : ℝ) ∧ (m : ℝ) < y)
    (hexcess : weightedNonprime S w < weightedMangoldt S w) :
    PrimeInOpenInterval x y := by
  classical
  by_contra hno
  have hzero : ∀ m ∈ S, Nat.Prime m → w m = 0 := by
    intro m hm hprime
    by_contra hwm
    obtain ⟨hlo, hhi⟩ := hsupport m hm hwm
    exact hno ⟨m, hprime, hlo, hhi⟩
  have hprimeSum :
      (∑ m ∈ S.filter Nat.Prime, ArithmeticFunction.vonMangoldt m * w m) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    obtain ⟨hmS, hp⟩ := Finset.mem_filter.mp hm
    rw [hzero m hmS hp, mul_zero]
  have hsplit := Finset.sum_filter_add_sum_filter_not S Nat.Prime
    (fun m => ArithmeticFunction.vonMangoldt m * w m)
  rw [hprimeSum, zero_add] at hsplit
  unfold weightedNonprime weightedMangoldt at hexcess
  linarith

/-- The usual main-term-minus-errors criterion with the prime-power budget separate. -/
theorem prime_of_weighted_budget (S : Finset ℕ) (w : ℕ → ℝ) (x y M E P : ℝ)
    (hsupport : ∀ m ∈ S, w m ≠ 0 → x < (m : ℝ) ∧ (m : ℝ) < y)
    (hmain : M - E ≤ weightedMangoldt S w)
    (hnonprime : weightedNonprime S w ≤ P)
    (hbudget : E + P < M) : PrimeInOpenInterval x y := by
  apply prime_of_weighted_excess S w x y hsupport
  linarith

/-- A rigorous `delta < 1` criterion, retaining the actual weighted prime sum. -/
theorem prime_of_normalized_weighted_budget (S : Finset ℕ) (w : ℕ → ℝ)
    (x y M δ : ℝ)
    (hsupport : ∀ m ∈ S, w m ≠ 0 → x < (m : ℝ) ∧ (m : ℝ) < y)
    (hM : 0 < M) (hδ : δ < 1)
    (hmain : M * (1 - δ) ≤ weightedMangoldt S w - weightedNonprime S w) :
    PrimeInOpenInterval x y := by
  apply prime_of_weighted_excess S w x y hsupport
  have hpos : 0 < M * (1 - δ) := mul_pos hM (by linarith)
  linarith

end LegendreK6
