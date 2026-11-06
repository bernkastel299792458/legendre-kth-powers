import LegendreK6.LowRankTaylor

/-! Exact integer moment evaluation for dyadic coefficient certificates.
The arithmetic evaluator is connected to the real finite-sum definitions;
its ground inequalities are intended to be checked with ordinary `decide`.
-/

namespace LegendreK6

open scoped BigOperators

def integerMoment (rows : List (ℕ × ℕ)) (n : ℕ) : ℕ :=
  (rows.map (fun r => r.1 * r.2 ^ n)).sum

def rationalMoment (bits : ℕ) (rows : List (ℕ × ℕ)) (n : ℕ) : ℚ :=
  (integerMoment rows n : ℚ) / (2 : ℚ) ^ (bits * (n + 1))

def rationalLowRank20 (bits : ℕ) (sigmaRows heightRows : List (ℕ × ℕ)) : ℚ :=
  (∑ n ∈ Finset.range 21,
    rationalMoment bits sigmaRows n * rationalMoment bits heightRows n / (n.factorial : ℚ)) +
  2 * rationalMoment bits sigmaRows 21 * rationalMoment bits heightRows 21 /
    (Nat.factorial 21 : ℚ)

noncomputable def dyadicCoefficient (bits : ℕ) (rows : List (ℕ × ℕ))
    (i : Fin rows.length) : ℝ := (rows.get i).1 / (2 : ℝ) ^ bits

noncomputable def dyadicPower (bits : ℕ) (rows : List (ℕ × ℕ))
    (i : Fin rows.length) : ℝ := (rows.get i).2 / (2 : ℝ) ^ bits

theorem integerMoment_eq_sum (rows : List (ℕ × ℕ)) (n : ℕ) :
    integerMoment rows n = ∑ i : Fin rows.length, (rows.get i).1 * (rows.get i).2 ^ n := by
  have heq : rows.map (fun r => r.1 * r.2 ^ n) =
      List.ofFn (fun i : Fin rows.length => (rows.get i).1 * (rows.get i).2 ^ n) := by
    simpa only [List.get_eq_getElem] using
      (List.ofFn_getElem_eq_map rows (fun r => r.1 * r.2 ^ n)).symm
  unfold integerMoment
  rw [heq, List.sum_ofFn]

theorem dyadicMoment_eq_rationalMoment (bits : ℕ) (rows : List (ℕ × ℕ)) (n : ℕ) :
    positiveMoment Finset.univ (dyadicCoefficient bits rows) (dyadicPower bits rows) n =
      (rationalMoment bits rows n : ℝ) := by
  have hterm (i : Fin rows.length) :
      dyadicCoefficient bits rows i * dyadicPower bits rows i ^ n =
      (((rows.get i).1 * (rows.get i).2 ^ n : ℕ) : ℝ) /
        (2 : ℝ) ^ (bits * (n + 1)) := by
    unfold dyadicCoefficient dyadicPower
    push_cast
    rw [pow_mul, pow_succ, div_pow]
    ring
  unfold positiveMoment rationalMoment
  simp_rw [hterm]
  rw [← Finset.sum_div, integerMoment_eq_sum]
  push_cast
  rfl

theorem lowRankTaylor20_eq_rational (bits : ℕ) (sigmaRows heightRows : List (ℕ × ℕ)) :
    lowRankTaylor20 Finset.univ Finset.univ
      (dyadicCoefficient bits sigmaRows) (dyadicPower bits sigmaRows)
      (dyadicCoefficient bits heightRows) (dyadicPower bits heightRows) =
      (rationalLowRank20 bits sigmaRows heightRows : ℝ) := by
  unfold lowRankTaylor20 rationalLowRank20
  simp_rw [dyadicMoment_eq_rationalMoment]
  push_cast
  rfl

end LegendreK6
