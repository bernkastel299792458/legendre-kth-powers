import Mathlib

/-!
# Positive low-rank Taylor bounds for a finite exponential sum

These semantic lemmas reduce a double exponential sum to finitely many
positive moments. The scalar remainder is the existing Mathlib theorem
`Complex.exp_bound'`, specialized to degree twenty and `0 ≤ z ≤ 11`.
No numerical output of an external program is assumed correct.
-/

namespace LegendreK6

open scoped BigOperators

/-- A polynomial majorant that is valid on the entire closed interval `[0,11]`. -/
theorem exp_le_taylor20 {z : ℝ} (hz : 0 ≤ z) (hz11 : z ≤ 11) :
    Real.exp z ≤ (∑ d ∈ Finset.range 21, z ^ d / (d.factorial : ℝ)) +
      2 * z ^ 21 / (Nat.factorial 21 : ℝ) := by
  have hsize : ‖(z : ℂ)‖ / (21 + 1 : ℕ) ≤ (1 / 2 : ℝ) := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz]
    norm_num
    linarith
  have hc := Complex.exp_bound' (x := (z : ℂ)) (n := 21) hsize
  have hs : ((Real.exp z - ∑ d ∈ Finset.range 21,
      z ^ d / (d.factorial : ℝ) : ℝ) : ℂ) =
      Complex.exp (z : ℂ) - ∑ d ∈ Finset.range 21, (z : ℂ) ^ d / (d.factorial : ℂ) := by
    push_cast
    rfl
  rw [← hs, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz] at hc
  have h := (le_abs_self (Real.exp z -
    ∑ d ∈ Finset.range 21, z ^ d / (d.factorial : ℝ))).trans hc
  linarith

/-- A moment of a positive coefficient family. -/
noncomputable def positiveMoment {ι : Type*} (s : Finset ι) (c a : ι → ℝ)
    (d : ℕ) : ℝ := ∑ i ∈ s, c i * a i ^ d

/-- The low-rank degree-twenty majorant, with its certified twenty-first term. -/
noncomputable def lowRankTaylor20 {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (c a : ι → ℝ) (d b : κ → ℝ) : ℝ :=
  (∑ n ∈ Finset.range 21,
    positiveMoment s c a n * positiveMoment t d b n / (n.factorial : ℝ)) +
  2 * positiveMoment s c a 21 * positiveMoment t d b 21 / (Nat.factorial 21 : ℝ)

/-- The finite product moment factors exactly; this is not a numerical approximation. -/
theorem sum_product_moment {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (c a : ι → ℝ) (d b : κ → ℝ) (n : ℕ) :
    (∑ i ∈ s, ∑ j ∈ t, c i * d j * (a i * b j) ^ n) =
      positiveMoment s c a n * positiveMoment t d b n := by
  unfold positiveMoment
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_pow]
  ring

/-- A double finite exponential sum is bounded by its two moment families. -/
theorem low_rank_exp_sum_le {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (c a : ι → ℝ) (d b : κ → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hd : ∀ j ∈ t, 0 ≤ d j) (hb : ∀ j ∈ t, 0 ≤ b j)
    (hab : ∀ i ∈ s, ∀ j ∈ t, a i * b j ≤ 11) :
    (∑ i ∈ s, ∑ j ∈ t, c i * d j * Real.exp (a i * b j)) ≤
      lowRankTaylor20 s t c a d b := by
  have hpoint : ∀ i ∈ s, ∀ j ∈ t,
      c i * d j * Real.exp (a i * b j) ≤
      c i * d j * ((∑ n ∈ Finset.range 21,
        (a i * b j) ^ n / (n.factorial : ℝ)) +
        2 * (a i * b j) ^ 21 / (Nat.factorial 21 : ℝ)) := by
    intro i hi j hj
    exact mul_le_mul_of_nonneg_left
      (exp_le_taylor20 (mul_nonneg (ha i hi) (hb j hj)) (hab i hi j hj))
      (mul_nonneg (hc i hi) (hd j hj))
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ t, c i * d j *
        ((∑ n ∈ Finset.range 21, (a i * b j) ^ n / (n.factorial : ℝ)) +
        2 * (a i * b j) ^ 21 / (Nat.factorial 21 : ℝ)) := by
      exact Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hpoint i hi j hj))
    _ = _ := by
      unfold lowRankTaylor20
      simp_rw [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
      congr 1
      · simp_rw [Finset.sum_comm (s := t) (t := Finset.range 21)]
        rw [Finset.sum_comm (s := s) (t := Finset.range 21)]
        apply Finset.sum_congr rfl
        intro n _
        simp_rw [← mul_div_assoc, ← Finset.sum_div]
        rw [sum_product_moment]
      · have hr (i : ι) (j : κ) :
            c i * d j * (2 * (a i * b j) ^ 21 / (Nat.factorial 21 : ℝ)) =
            2 * (c i * d j * (a i * b j) ^ 21) / (Nat.factorial 21 : ℝ) := by ring
        simp_rw [hr, ← Finset.sum_div, ← Finset.mul_sum]
        rw [sum_product_moment]
        ring

/-- Exact separation of the reference real part and height. -/
theorem shifted_exp_factorization (p v p0 v0 : ℝ) :
    Real.exp (p * v) = Real.exp (p * v0) * Real.exp (p0 * (v - v0)) *
      Real.exp ((p - p0) * (v - v0)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The original exponent matrix is reduced to positive low-rank moments. -/
theorem shifted_exp_sum_le {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (c p : ι → ℝ) (d v : κ → ℝ) (p0 v0 : ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hp : ∀ i ∈ s, p0 ≤ p i)
    (hd : ∀ j ∈ t, 0 ≤ d j) (hv : ∀ j ∈ t, v0 ≤ v j)
    (hpv : ∀ i ∈ s, ∀ j ∈ t, (p i - p0) * (v j - v0) ≤ 11) :
    (∑ i ∈ s, ∑ j ∈ t, c i * d j * Real.exp (p i * v j)) ≤
      lowRankTaylor20 s t
        (fun i => c i * Real.exp (p i * v0)) (fun i => p i - p0)
        (fun j => d j * Real.exp (p0 * (v j - v0))) (fun j => v j - v0) := by
  have hh := low_rank_exp_sum_le s t
    (fun i => c i * Real.exp (p i * v0)) (fun i => p i - p0)
    (fun j => d j * Real.exp (p0 * (v j - v0))) (fun j => v j - v0)
    (fun i hi => mul_nonneg (hc i hi) (Real.exp_nonneg _))
    (fun i hi => sub_nonneg.mpr (hp i hi))
    (fun j hj => mul_nonneg (hd j hj) (Real.exp_nonneg _))
    (fun j hj => sub_nonneg.mpr (hv j hj)) hpv
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [shifted_exp_factorization (p i) (v j) p0 v0]
  ring

/-- Positive moments can be enclosed by separate pointwise rational bounds. -/
theorem positiveMoment_mono {ι : Type*} (s : Finset ι) (c a C A : ι → ℝ) (n : ℕ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hcC : ∀ i ∈ s, c i ≤ C i) (haA : ∀ i ∈ s, a i ≤ A i) :
    positiveMoment s c a n ≤ positiveMoment s C A n := by
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul (hcC i hi) (pow_le_pow_left₀ (ha i hi) (haA i hi) n)
    (pow_nonneg (ha i hi) n) ((hc i hi).trans (hcC i hi))

theorem positiveMoment_nonneg {ι : Type*} (s : Finset ι) (c a : ι → ℝ) (n : ℕ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (ha : ∀ i ∈ s, 0 ≤ a i) :
    0 ≤ positiveMoment s c a n :=
  Finset.sum_nonneg (fun i hi => mul_nonneg (hc i hi) (pow_nonneg (ha i hi) n))

/-- Monotonicity of the complete factored polynomial and its remainder. -/
theorem lowRankTaylor20_mono {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (c a C A : ι → ℝ) (d b D B : κ → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hd : ∀ j ∈ t, 0 ≤ d j) (hb : ∀ j ∈ t, 0 ≤ b j)
    (hcC : ∀ i ∈ s, c i ≤ C i) (haA : ∀ i ∈ s, a i ≤ A i)
    (hdD : ∀ j ∈ t, d j ≤ D j) (hbB : ∀ j ∈ t, b j ≤ B j) :
    lowRankTaylor20 s t c a d b ≤ lowRankTaylor20 s t C A D B := by
  have hm (n : ℕ) : positiveMoment s c a n * positiveMoment t d b n ≤
      positiveMoment s C A n * positiveMoment t D B n :=
    mul_le_mul (positiveMoment_mono s c a C A n hc ha hcC haA)
      (positiveMoment_mono t d b D B n hd hb hdD hbB)
      (positiveMoment_nonneg t d b n hd hb)
      (positiveMoment_nonneg s C A n
        (fun i hi => (hc i hi).trans (hcC i hi))
        (fun i hi => (ha i hi).trans (haA i hi)))
  unfold lowRankTaylor20
  apply add_le_add
  · exact Finset.sum_le_sum (fun n _ => div_le_div_of_nonneg_right (hm n) (by positivity))
  · have h21 := mul_le_mul_of_nonneg_left (hm 21) (show (0 : ℝ) ≤ 2 by norm_num)
    exact div_le_div_of_nonneg_right (by simpa only [mul_assoc] using h21) (by positivity)

end LegendreK6
