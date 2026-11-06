import Mathlib

/-!
# Statements used by the six-power project

These definitions do not assert any unproved mathematical result.  In particular,
no zero-density estimate, analytic bridge, or numerical certificate is an axiom.
The assembly theorem in this project lists its still-unformalized module inputs
as explicit arguments; it is not an end-to-end formalization from QRH and CS v2.
-/

namespace LegendreK6

/-- A prime strictly inside a real interval. -/
def PrimeInOpenInterval (x y : ℝ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) < y

/-- The real-variable sixth-power length used in the new middle segment. -/
def ShortInterval6 (x : ℝ) : Prop :=
  PrimeInOpenInterval x (x + 6 * x ^ ((5 : ℝ) / 6))

/-- The shorter real interval inherited from the fourth-power calculation. -/
def ShortInterval4 (x : ℝ) : Prop :=
  PrimeInOpenInterval x (x + 4 * x ^ ((3 : ℝ) / 4))

/-- The stronger, entirely integral short-interval claim at a sixth power. -/
def NatSixthShort (n : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ n ^ 6 < p ∧ p < n ^ 6 + 6 * n ^ 5

/-- The generalized Legendre assertion for the fixed exponent six. -/
def SixthPowerConclusion : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ n ^ 6 < p ∧ p < (n + 1) ^ 6

/-- The exact orientation of the externally cited CHL short-interval theorem. -/
def CHLInterval (Δ X : ℝ) : Prop :=
  ∀ y : ℝ, X ≤ y →
    ∃ p : ℕ, p.Prime ∧ y * (1 - 1 / Δ) < (p : ℝ) ∧ (p : ℝ) ≤ y

end LegendreK6
