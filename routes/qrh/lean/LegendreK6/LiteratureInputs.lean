import LegendreK6.ZetaZeros

/-!
# Precisely stated classical inputs for the nonsmoothed tail

These propositions are named external literature inputs, not proved results
of this project. They do not assume a prime interval or a bound for the
project's weighted-zero expression. All sums use the actual zeta function
and its analytic multiplicities.

CHJII: arXiv:2402.04272v3, Theorem 1.3 and Table 1, row
log(x_M)=40, alpha=1/2, omega=0, M=2.894.
Rosser: the classical counting bound quoted in the manuscript, with its
full constants, rather than the weaker bound N(T) <= T log T used later.
-/

namespace LegendreK6

open scoped BigOperators

noncomputable def truncatedZeroIncrement (x y T : ℝ) : ℂ :=
  ∑ ρ ∈ allZetaZeros T, (zetaMultiplicity ρ : ℂ) *
    (((y : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ)

/-- A single shared truncation for the two endpoints. The norm formulation
is exactly the O-star error in the cited short-interval theorem. -/
def CHJIIShortInterval : Prop :=
  ∀ (x h T : ℝ), 0 < x → 40 ≤ Real.log x → 0 ≤ h →
    max 51 ((Real.log x) ^ 2) < T → T < (Real.sqrt x - 2) / 4 →
    ∃ Tstar : ℝ, T ≤ Tstar ∧ Tstar ≤ 2 * T ∧
      ‖((Chebyshev.psi (x + h) - Chebyshev.psi x - h : ℝ) : ℂ) +
        truncatedZeroIncrement x (x + h) Tstar‖ ≤
        (1447 / 500 : ℝ) / T * ((x + h) * Real.log (x + h) + x * Real.log x)

/-- The source's closed rectangle, retaining real-axis and strip-boundary
zeros until separately excluded. This avoids strengthening the quoted input
by silently changing the set being counted. -/
def rosserZeroSet (T : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ 0 ≤ ρ.re ∧ ρ.re ≤ 1 ∧ 0 ≤ ρ.im ∧ ρ.im ≤ T}

theorem rosserZeroSet_finite (T : ℝ) : (rosserZeroSet T).Finite := by
  apply ((isCompact_closedBall (0 : ℂ) (|T| + 1)).inter_riemannZetaZeros_finite).subset
  intro ρ hρ
  rcases hρ with ⟨hz, hre0, hre1, him0, himT⟩
  constructor
  · simp only [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
      _ ≤ |T| + 1 := by
        rw [abs_of_nonneg hre0, abs_of_nonneg him0]
        linarith [le_abs_self T]
  · exact hz

noncomputable def rosserZeros (T : ℝ) : Finset ℂ :=
  (rosserZeroSet_finite T).toFinset

noncomputable def rosserCount (T : ℝ) : ℕ :=
  ∑ ρ ∈ rosserZeros T, zetaMultiplicity ρ

theorem totalZeroCount_le_rosserCount (T : ℝ) : totalZeroCount T ≤ rosserCount T := by
  apply Finset.sum_le_sum_of_subset
  intro ρ hρ
  obtain ⟨hz, hr0, hr1, hi0, hiT⟩ := mem_positiveZetaZeros.mp hρ
  simpa [rosserZeros, rosserZeroSet] using ⟨hz, hr0.le, hr1.le, hi0.le, hiT⟩

/-- The explicit Rosser bound in the source's closed-rectangle convention.
Source: Dusart's HDR, printed p. 82, Theorem 86, and p. 34, (2.2)-(2.3).
The counting set is retained literally; only an upper bound is transferred
to the project's strictly positive-height count. -/
def RosserZeroCount : Prop :=
  ∀ T : ℝ, 2 ≤ T →
    |(rosserCount T : ℝ) -
      (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) -
        T / (2 * Real.pi) + 7 / 8)| ≤
      (137 / 1000 : ℝ) * Real.log T +
      (443 / 1000 : ℝ) * Real.log (Real.log T) + 397 / 250

/-- The manuscript's deliberately coarse count is derived from the full
literature formula. It is not a second assumed estimate. -/
theorem totalZeroCount_le_mul_log (H : RosserZeroCount) {T : ℝ}
    (hT : 3000000000000 ≤ T) (hlog : 1 ≤ Real.log T) :
    (totalZeroCount T : ℝ) ≤ T * Real.log T := by
  have hT0 : 0 < T := by linarith
  have hp : 1 ≤ Real.pi := le_trans (by norm_num) Real.two_le_pi
  have hp0 : 0 < 2 * Real.pi := by positivity
  have hratio0 : 0 < T / (2 * Real.pi) := div_pos hT0 hp0
  have hratio : T / (2 * Real.pi) ≤ T / 2 := by
    apply (div_le_iff₀ hp0).2
    nlinarith [mul_nonneg hT0.le (sub_nonneg.mpr hp)]
  have hratioT : T / (2 * Real.pi) ≤ T := by linarith
  have hlogratio := Real.log_le_log hratio0 hratioT
  have hmain : T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) ≤
      T / 2 * Real.log T := by
    calc
      _ ≤ T / (2 * Real.pi) * Real.log T :=
        mul_le_mul_of_nonneg_left hlogratio hratio0.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hratio (by linarith)
  have hll : Real.log (Real.log T) ≤ Real.log T :=
    le_trans (Real.log_le_sub_one_of_pos (by linarith)) (by linarith)
  have hR := (abs_le.mp (H T (by linarith))).2
  have hsubset : (totalZeroCount T : ℝ) ≤ (rosserCount T : ℝ) :=
    Nat.cast_le.mpr (totalZeroCount_le_rosserCount T)
  have hbudget := mul_nonneg (show 0 ≤ T / 2 - 3 by linarith)
    (show 0 ≤ Real.log T - 1 by linarith)
  nlinarith

end LegendreK6
