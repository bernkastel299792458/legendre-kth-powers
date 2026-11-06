import LegendreK6.TrapezoidZeroBound

/-!
# The finite-height RH input, stated for the actual Riemann zeta function

Platt and Trudgian, arXiv:2004.09765v1 (2020), abstract and Theorem 1:
https://arxiv.org/pdf/2004.09765v1 . The abstract explicitly includes
`0 < gamma <= 3 * 10^12`; Theorem 1 reaches the still higher height
3,000,175,332,800. Our closed cutoff is therefore a restriction of that result.

The computational theorem is an explicit literature premise, not reproved
here. Multiplicities remain the existing analytic orders of the actual zeta
function; no simplicity or alternative zero enumeration is assumed.
-/

namespace LegendreK6

open scoped BigOperators

def FiniteRH3e12 : Prop :=
  ∀ ρ : NontrivialZero, 0 < ρ.val.im → ρ.val.im ≤ 3000000000000 →
    ρ.val.re = 1/2

theorem positiveZeroWeight_eq_finiteRH (HF : FiniteRH3e12) (A T : ℝ)
    (hT : T ≤ 3000000000000) :
    positiveZeroWeight A T = Real.exp (-A/2) * (totalZeroCount T : ℝ) := by
  unfold positiveZeroWeight
  rw [totalZeroCount_cast, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  obtain ⟨hz, hre0, hre1, him0, himT⟩ := mem_positiveZetaZeros.mp hρ
  have hre := HF ⟨ρ, hz, hre0, hre1⟩ him0 (himT.trans hT)
  change ρ.re = 1/2 at hre
  rw [hre]
  rw [show ((1/2 : ℝ)-1)*A = -A/2 by ring]
  ring

theorem one_le_log_finiteRHHeight : 1 ≤ Real.log (3000000000000 : ℝ) := by
  apply (Real.le_log_iff_exp_le (by norm_num)).2
  have he := Real.exp_one_lt_d9
  linarith

theorem positiveZeroWeight_finiteRH_le (HF : FiniteRH3e12) (HR : RosserZeroCount)
    (A : ℝ) :
    positiveZeroWeight A 3000000000000 ≤
      Real.exp (-A/2) * 3000000000000 * Real.log 3000000000000 := by
  rw [positiveZeroWeight_eq_finiteRH HF A _ le_rfl]
  have hn := totalZeroCount_le_mul_log HR (T := 3000000000000) le_rfl
    one_le_log_finiteRHHeight
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hn (Real.exp_nonneg (-A/2))

/-- The low-height prefix of every actual finite cutoff has the same coarse bound. -/
theorem positiveZeroWeight_prefix_finiteRH_le
    (HF : FiniteRH3e12) (HR : RosserZeroCount) (A T : ℝ) :
    (∑ ρ ∈ positiveZetaZeros T, if ρ.im ≤ 3000000000000 then
      (zetaMultiplicity ρ : ℝ) * Real.exp ((ρ.re-1)*A) else 0) ≤
        Real.exp (-A/2) * 3000000000000 * Real.log 3000000000000 :=
  (positiveZeroWeight_prefix_le A T _).trans (positiveZeroWeight_finiteRH_le HF HR A)

end LegendreK6
