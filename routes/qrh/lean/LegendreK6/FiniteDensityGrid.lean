import LegendreK6.DensityInput
import LegendreK6.LiteratureInputs
import LegendreK6.FiniteZeroLayer

/-!
# Exact finite real-part grids for actual zero counts

The staircase estimate is proved directly by finite telescoping. Thus every
closed grid cell contributes its exact exponential difference, including
zeros on its boundary; no numerical integration or supplied soundness flag
is used here.
-/

namespace LegendreK6

open scoped BigOperators

theorem exp_le_grid_staircase (s : ℕ → ℝ) (n : ℕ) (L β : ℝ)
    (hL : 0 ≤ L) (hs : Monotone s) (hβ : β ≤ s n) :
    Real.exp ((β - 1) * L) ≤ Real.exp ((s 0 - 1) * L) +
      ∑ j ∈ Finset.range n, if s j ≤ β then
        Real.exp ((s (j + 1) - 1) * L) - Real.exp ((s j - 1) * L) else 0 := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hL)
  | succ n ih =>
    rw [Finset.sum_range_succ]
    by_cases hbn : β ≤ s n
    · have hi := ih hbn
      have hd : 0 ≤ (if s n ≤ β then
          Real.exp ((s (n + 1) - 1) * L) - Real.exp ((s n - 1) * L) else 0) := by
        split_ifs
        · exact sub_nonneg.mpr (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_right (sub_le_sub_right (hs (Nat.le_succ n)) 1) hL))
        · exact le_rfl
      linarith
    · have hnβ : s n ≤ β := le_of_lt (lt_of_not_ge hbn)
      rw [ite_eq_left hnβ]
      have hsum : (∑ j ∈ Finset.range n, if s j ≤ β then
          Real.exp ((s (j + 1) - 1) * L) - Real.exp ((s j - 1) * L) else 0) =
          Real.exp ((s n - 1) * L) - Real.exp ((s 0 - 1) * L) := by
        calc
          _ = ∑ j ∈ Finset.range n,
              (Real.exp ((s (j + 1) - 1) * L) - Real.exp ((s j - 1) * L)) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [ite_eq_left ((hs (Nat.le_of_lt (Finset.mem_range.mp hj))).trans hnβ)]
          _ = _ := Finset.sum_range_sub (fun j => Real.exp ((s j - 1) * L)) n
      rw [hsum]
      have he := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (sub_le_sub_right hβ 1) hL)
      linarith

theorem finite_exp_grid_bound {ι : Type*} (S : Finset ι) (β : ι → ℝ)
    (m : ι → ℕ) (s : ℕ → ℝ) (n : ℕ) (L : ℝ)
    (hL : 0 ≤ L) (hs : Monotone s) (hβ : ∀ i ∈ S, β i ≤ s n) :
    (∑ i ∈ S, (m i : ℝ) * Real.exp ((β i - 1) * L)) ≤
      (∑ i ∈ S, (m i : ℝ)) * Real.exp ((s 0 - 1) * L) +
      ∑ j ∈ Finset.range n,
        (Real.exp ((s (j+1) - 1) * L) - Real.exp ((s j - 1) * L)) *
          finiteLayerCount S β m (s j) := by
  classical
  calc
    _ ≤ ∑ i ∈ S, (m i : ℝ) * (Real.exp ((s 0 - 1) * L) +
        ∑ j ∈ Finset.range n, if s j ≤ β i then
          Real.exp ((s (j+1) - 1) * L) - Real.exp ((s j - 1) * L) else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (exp_le_grid_staircase s n L (β i) hL hs (hβ i hi)) (Nat.cast_nonneg _)
    _ = _ := by
      simp_rw [mul_add, Finset.mul_sum]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [finiteLayerCount, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> ring

/-- Actual multiplicity-weighted positive-height zero count. -/
noncomputable def positiveZeroWeight (L T : ℝ) : ℝ :=
  ∑ ρ ∈ positiveZetaZeros T, (zetaMultiplicity ρ : ℝ) * Real.exp ((ρ.re - 1) * L)

theorem positiveZeroWeight_nonneg (L T : ℝ) : 0 ≤ positiveZeroWeight L T := by
  exact Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _))

theorem positiveZeroWeight_mono (L : ℝ) : Monotone (positiveZeroWeight L) := by
  intro T U hTU
  apply Finset.sum_le_sum_of_subset_of_nonneg (positiveZetaZeros_mono hTU)
  intro ρ _ _
  exact mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)

noncomputable def sigmaGridWeight (s : ℕ → ℝ) (L : ℝ) (j : ℕ) : ℝ :=
  Real.exp ((s (j+1) - 1) * L) - Real.exp ((s j - 1) * L)

theorem sigmaGridWeight_nonneg (s : ℕ → ℝ) (L : ℝ) (j : ℕ)
    (hs : Monotone s) (hL : 0 ≤ L) : 0 ≤ sigmaGridWeight s L j := by
  exact sub_nonneg.mpr (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (sub_le_sub_right (hs (Nat.le_succ j)) 1) hL))

theorem positiveZeroWeight_le_density_grid (HQ : QRHSevenEighths)
    (s : ℕ → ℝ) (n : ℕ) (L T : ℝ) (hL : 0 ≤ L) (hs : Monotone s)
    (hs0 : s 0 = 1/2) (hsn : 7/8 ≤ s n) :
    positiveZeroWeight L T ≤ Real.exp (-L/2) * (totalZeroCount T : ℝ) +
      ∑ j ∈ Finset.range n, sigmaGridWeight s L j * (densityZeroCount (s j) T : ℝ) := by
  have hb : ∀ ρ ∈ positiveZetaZeros T, ρ.re ≤ s n := by
    intro ρ hρ
    obtain ⟨hz, hre0, hre1, _⟩ := mem_positiveZetaZeros.mp hρ
    exact (HQ ⟨ρ, hz, hre0, hre1⟩).trans hsn
  have hg := finite_exp_grid_bound (positiveZetaZeros T) Complex.re
    zetaMultiplicity s n L hL hs hb
  have hcount (σ : ℝ) :
      finiteLayerCount (positiveZetaZeros T) Complex.re zetaMultiplicity σ =
        (densityZeroCount σ T : ℝ) := by
    classical
    simp [finiteLayerCount, densityZeroCount, Finset.sum_filter]
  simp_rw [hcount] at hg
  rw [← totalZeroCount_cast, hs0] at hg
  have he : (1/2 - 1) * L = -L/2 := by ring
  rw [he, mul_comm] at hg
  exact hg

/-- Original CS row expression after writing the height as exp u. -/
noncomputable def csLogHeightBound (i : Fin 12) (σ u : ℝ) : ℝ :=
  csB1 i * Real.exp (csExponent σ * u) * u ^ (csExponent σ + 2) +
    csB2 i * u^2 + csB3 i * u

theorem densityZeroCount_exp_le (HC : CSv2) (i : Fin 12) (σ u : ℝ)
    (hlo : (16 + (i.val : ℝ)) / 32 ≤ σ)
    (hhi : σ ≤ (17 + (i.val : ℝ)) / 32)
    (hT : 3000000000000 ≤ Real.exp u) :
    (densityZeroCount σ (Real.exp u) : ℝ) ≤ csLogHeightBound i σ u := by
  have hσ : σ < 2 := by
    have hi : i.val < 12 := i.isLt
    have hi' : (i.val : ℝ) < 12 := by exact_mod_cast hi
    linarith
  have hc := HC i σ (Real.exp u) hlo hhi hT
  rw [Real.log_exp, cs_log_exponent_eq hσ, ← Real.exp_mul] at hc
  simpa only [csLogHeightBound, mul_comm u (csExponent σ)] using hc

noncomputable def densityGridPhi (s : ℕ → ℝ) (row : ℕ → Fin 12)
    (n : ℕ) (L u : ℝ) : ℝ :=
  Real.exp (-L/2 + u) * u +
    ∑ j ∈ Finset.range n, sigmaGridWeight s L j * csLogHeightBound (row j) (s j) u

/-- The grid envelope bounds an actual zeta-zero sum. Only QRH, the original
CS rows and Rosser are external inputs. Grid and domain conditions are
ordinary finite numerical obligations for each certificate. -/
theorem positiveZeroWeight_le_gridPhi (HQ : QRHSevenEighths) (HC : CSv2)
    (HR : RosserZeroCount) (s : ℕ → ℝ) (row : ℕ → Fin 12)
    (n : ℕ) (L u : ℝ) (hL : 0 ≤ L) (hs : Monotone s)
    (hs0 : s 0 = 1/2) (hsn : 7/8 ≤ s n)
    (hrows : ∀ j < n, (16 + ((row j).val : ℝ))/32 ≤ s j ∧
      s j ≤ (17 + ((row j).val : ℝ))/32)
    (hT : 3000000000000 ≤ Real.exp u) (hu : 1 ≤ u) :
    positiveZeroWeight L (Real.exp u) ≤ densityGridPhi s row n L u := by
  apply (positiveZeroWeight_le_density_grid HQ s n L (Real.exp u) hL hs hs0 hsn).trans
  unfold densityGridPhi
  apply add_le_add
  · have hn := totalZeroCount_le_mul_log HR hT (by simpa using hu)
    have hm := mul_le_mul_of_nonneg_left hn (Real.exp_nonneg (-L/2))
    simpa only [Real.log_exp, Real.exp_add, mul_assoc] using hm
  · apply Finset.sum_le_sum
    intro j hj
    obtain ⟨hlo, hhi⟩ := hrows j (Finset.mem_range.mp hj)
    exact mul_le_mul_of_nonneg_left (densityZeroCount_exp_le HC (row j) (s j) u hlo hhi hT)
      (sigmaGridWeight_nonneg s L j hs hL)

end LegendreK6
