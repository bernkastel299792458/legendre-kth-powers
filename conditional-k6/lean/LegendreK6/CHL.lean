import LegendreK6.Reduction

/-!
# Exact use of a CHL row

`CHLInterval` is an explicitly named external-literature input, not an axiom.
The conversion, including removal of the source theorem's closed right endpoint,
is proved here. Numeric verification of the twelve transcendental source
thresholds is separate from this generic theorem.
-/

namespace LegendreK6

theorem nat_sixth_short_of_CHL {n : ℕ} {Δ X : ℝ}
    (hn : 2 ≤ n) (hΔ : 1 < Δ) (hCHL : CHLInterval Δ X)
    (hX : X ≤ (n : ℝ) ^ 6) (hlimit : (n : ℝ) ≤ 6 * (Δ - 1)) :
    NatSixthShort n := by
  have hΔpos : 0 < Δ := by linarith
  have hΔne : Δ ≠ 0 := ne_of_gt hΔpos
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  let y : ℝ := (n : ℝ) ^ 6 + 6 * (n : ℝ) ^ 5
  have hyX : X ≤ y := by
    dsimp [y]
    nlinarith [pow_nonneg hn0 5]
  have hkey : (n : ℝ) ^ 6 ≤ y * (1 - 1 / Δ) := by
    have hfrac : 1 - 1 / Δ = (Δ - 1) / Δ := by field_simp
    rw [hfrac, ← mul_div_assoc, le_div_iff₀ hΔpos]
    dsimp [y]
    nlinarith [mul_le_mul_of_nonneg_left hlimit (pow_nonneg hn0 5)]
  obtain ⟨p, hp, hlo, hhi⟩ := hCHL y hyX
  have hloNat : n ^ 6 < p := by
    have hreal : (n : ℝ) ^ 6 < p := lt_of_le_of_lt hkey hlo
    exact_mod_cast hreal
  have hhiNat : p ≤ n ^ 6 + 6 * n ^ 5 := by
    dsimp [y] at hhi
    exact_mod_cast hhi
  have hne : p ≠ n ^ 6 + 6 * n ^ 5 := by
    intro heq
    apply sixth_right_endpoint_not_prime hn
    simpa [heq] using hp
  exact ⟨p, hp, hloNat, lt_of_le_of_ne hhiNat hne⟩

end LegendreK6
