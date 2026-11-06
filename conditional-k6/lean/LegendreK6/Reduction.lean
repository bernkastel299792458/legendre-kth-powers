import LegendreK6.Definitions

/-!
# Exact sixth-power reductions and open endpoints

The results below are proved in Lean from Mathlib. They do not require QRH,
zero-density estimates, an interval-arithmetic oracle, or a prime-gap assumption.
-/

namespace LegendreK6

theorem sixth_binomial_gap (n : ℕ) :
    n ^ 6 + 6 * n ^ 5 < (n + 1) ^ 6 := by
  nlinarith [Nat.zero_le (n ^ 4), Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2),
    Nat.zero_le n]

theorem conclusion_at_of_nat_short {n : ℕ} (h : NatSixthShort n) :
    ∃ p : ℕ, p.Prime ∧ n ^ 6 < p ∧ p < (n + 1) ^ 6 := by
  obtain ⟨p, hp, hlo, hhi⟩ := h
  exact ⟨p, hp, hlo, lt_trans hhi (sixth_binomial_gap n)⟩

theorem sixth_rpow_five_sixths (n : ℕ) :
    ((n : ℝ) ^ 6) ^ ((5 : ℝ) / 6) = (n : ℝ) ^ 5 := by
  rw [← Real.rpow_natCast_mul (Nat.cast_nonneg n)]
  norm_num

theorem nat_short_of_real_short (n : ℕ) (h : ShortInterval6 ((n : ℝ) ^ 6)) :
    NatSixthShort n := by
  obtain ⟨p, hp, hlo, hhi⟩ := h
  rw [sixth_rpow_five_sixths] at hhi
  refine ⟨p, hp, ?_, ?_⟩
  · exact_mod_cast hlo
  · exact_mod_cast hhi

theorem four_length_le_six_length {x : ℝ} (hx : 1 ≤ x) :
    4 * x ^ ((3 : ℝ) / 4) ≤ 6 * x ^ ((5 : ℝ) / 6) := by
  have he : x ^ ((3 : ℝ) / 4) ≤ x ^ ((5 : ℝ) / 6) :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hn : 0 ≤ x ^ ((5 : ℝ) / 6) :=
    Real.rpow_nonneg (by linarith) _
  nlinarith

theorem short_six_of_short_four {x : ℝ} (hx : 1 ≤ x) (h : ShortInterval4 x) :
    ShortInterval6 x := by
  obtain ⟨p, hp, hlo, hhi⟩ := h
  refine ⟨p, hp, hlo, lt_of_lt_of_le hhi ?_⟩
  exact add_le_add_right (four_length_le_six_length hx) x

theorem sixth_right_endpoint_not_prime {n : ℕ} (hn : 2 ≤ n) :
    ¬Nat.Prime (n ^ 6 + 6 * n ^ 5) := by
  have hf : n ^ 6 + 6 * n ^ 5 = n ^ 5 * (n + 6) := by ring
  rw [hf]
  apply Nat.not_prime_mul
  · have hpow : 2 ^ 5 ≤ n ^ 5 := Nat.pow_le_pow_left hn 5
    norm_num at hpow
    omega
  · omega

theorem nat_short_one : NatSixthShort 1 := by
  exact ⟨2, Nat.prime_two, by norm_num, by norm_num⟩

end LegendreK6
