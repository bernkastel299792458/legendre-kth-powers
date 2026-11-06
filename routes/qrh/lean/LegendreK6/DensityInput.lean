import LegendreK6.ZetaZeros
import LegendreK6.AnalyticBounds

/-!
# Exact QRH and CS v2 hypotheses, and the derived tail density bound

`QRHSevenEighths` refers to the actual Riemann zeta function. `CSv2` is the
first twelve rows of Corollary 1 and Table 1 of arXiv:2507.15184v2, with
closed sigma intervals and multiplicity-aware positive-height counts.
The project's open-strip count is a restriction of the source count;
restricting a nonnegative counting sum only weakens its upper bound.
These are explicit theorem parameters, not global axioms. The estimate
used by the tail must be derived from these inputs below.
-/

namespace LegendreK6

def QRHSevenEighths : Prop :=
  ∀ ρ : NontrivialZero, ρ.val.re ≤ (7 / 8 : ℝ)

def csB1 (i : Fin 12) : ℝ :=
  ![5.069, 6.046, 7.077, 8.185, 9.387, 10.70,
    12.11, 13.66, 15.35, 17.21, 19.31, 21.77] i

def csB2 (i : Fin 12) : ℝ :=
  ![9.461, 9.168, 8.875, 8.582, 8.290, 7.997,
    7.704, 7.411, 7.118, 6.826, 6.533, 6.240] i

def csB3 (i : Fin 12) : ℝ :=
  ![167.8, 162.6, 157.4, 152.2, 147.0, 141.9,
    136.7, 131.5, 126.3, 121.1, 115.9, 110.7] i

noncomputable def csExponent (σ : ℝ) : ℝ := 3 * (1 - σ) / (2 - σ)
noncomputable def csLogExponent (σ : ℝ) : ℝ := (7 - 5 * σ) / (2 - σ)

/-- Exact accepted density input: no weighted-zero or prime conclusion is assumed. -/
def CSv2 : Prop :=
  ∀ (i : Fin 12) (σ T : ℝ),
    (16 + (i.val : ℝ)) / 32 ≤ σ → σ ≤ (17 + (i.val : ℝ)) / 32 →
    3000000000000 ≤ T →
    (densityZeroCount σ T : ℝ) ≤
      csB1 i * T ^ csExponent σ * (Real.log T) ^ csLogExponent σ +
      csB2 i * (Real.log T) ^ 2 + csB3 i * Real.log T

theorem cs_log_exponent_eq {σ : ℝ} (hσ : σ < 2) :
    csLogExponent σ = csExponent σ + 2 := by
  unfold csLogExponent csExponent
  field_simp
  ring

theorem cs_tail_row_exists {σ : ℝ} (hlo : (5 / 8 : ℝ) ≤ σ)
    (hhi : σ ≤ (7 / 8 : ℝ)) :
    ∃ i : Fin 12, 4 ≤ i.val ∧
      (16 + (i.val : ℝ)) / 32 ≤ σ ∧ σ ≤ (17 + (i.val : ℝ)) / 32 := by
  by_cases h4 : σ ≤ 21 / 32
  · exact ⟨4, by norm_num, by norm_num; linarith, by norm_num; exact h4⟩
  by_cases h5 : σ ≤ 22 / 32
  · exact ⟨5, by norm_num, by norm_num; linarith, by norm_num; linarith⟩
  by_cases h6 : σ ≤ 23 / 32
  · exact ⟨6, by norm_num, by norm_num; linarith, by norm_num; exact h6⟩
  by_cases h7 : σ ≤ 24 / 32
  · exact ⟨7, by norm_num, by norm_num; linarith, by norm_num; linarith⟩
  by_cases h8 : σ ≤ 25 / 32
  · exact ⟨8, by norm_num, by norm_num; linarith, by norm_num; exact h8⟩
  by_cases h9 : σ ≤ 26 / 32
  · exact ⟨9, by norm_num, by norm_num; linarith, by norm_num; linarith⟩
  by_cases h10 : σ ≤ 27 / 32
  · exact ⟨10, by norm_num, by norm_num; linarith, by norm_num; exact h10⟩
  exact ⟨11, by norm_num, by norm_num; linarith, by norm_num; exact hhi⟩

theorem cs_tail_constants (i : Fin 12) (hi : 4 ≤ i.val) :
    0 ≤ csB1 i ∧ csB1 i ≤ (561 / 25 : ℝ) ∧
    csB2 i ≤ (829 / 100 : ℝ) ∧ csB3 i ≤ (147 : ℝ) := by
  fin_cases i <;> norm_num [csB1, csB2, csB3] at *

/-- Equation (36) is a consequence of the actual CS table input, rather
than a replacement assumption for it. -/
theorem cs_tail_density (H : CSv2) {σ U : ℝ}
    (hlo : (5 / 8 : ℝ) ≤ σ) (hhi : σ ≤ (7 / 8 : ℝ))
    (hU : 3000000000000 ≤ U) (hu : 1 ≤ Real.log U) :
    (densityZeroCount σ U : ℝ) ≤
      (561 / 25 : ℝ) * U ^ ((8 / 3 : ℝ) * (1 - σ)) * (Real.log U) ^ 3 +
      (829 / 100 : ℝ) * (Real.log U) ^ 2 + 147 * Real.log U := by
  obtain ⟨i, hi, hrowlo, hrowhi⟩ := cs_tail_row_exists hlo hhi
  obtain ⟨hb0, hb1, hb2, hb3⟩ := cs_tail_constants i hi
  have he : csExponent σ ≤ (8 / 3 : ℝ) * (1 - σ) := by
    have ha := cs_density_exponent_bound hhi
    have := mul_le_mul_of_nonneg_right ha (show 0 ≤ 1 - σ by linarith)
    convert this using 1 <;> dsimp [csExponent] <;> ring
  have heLog : csLogExponent σ ≤ 3 := by
    rw [cs_log_exponent_eq (by linarith)]
    exact cs_log_exponent_bound (by linarith) hhi
  have hpow := Real.rpow_le_rpow_of_exponent_le (show 1 ≤ U by linarith) he
  have hlogpow := Real.rpow_le_rpow_of_exponent_le hu heLog
  have hnonneg : 0 ≤ U ^ csExponent σ := Real.rpow_nonneg (by linarith) _
  have hlognonneg : 0 ≤ (Real.log U) ^ csLogExponent σ :=
    Real.rpow_nonneg (by linarith) _
  have hmain : csB1 i * U ^ csExponent σ * (Real.log U) ^ csLogExponent σ ≤
      (561 / 25 : ℝ) * U ^ ((8 / 3 : ℝ) * (1 - σ)) * (Real.log U) ^ 3 := by
    calc
      _ ≤ (561 / 25 : ℝ) * U ^ ((8 / 3 : ℝ) * (1 - σ)) *
          (Real.log U) ^ (3 : ℝ) :=
        mul_le_mul (mul_le_mul hb1 hpow hnonneg (by norm_num)) hlogpow
          hlognonneg (by positivity)
      _ = _ := by norm_cast
  have hsecond := mul_le_mul_of_nonneg_right hb2 (sq_nonneg (Real.log U))
  have hthird := mul_le_mul_of_nonneg_right hb3 (show 0 ≤ Real.log U by linarith)
  have horig := H i σ U hrowlo hrowhi hU
  linarith

end LegendreK6
