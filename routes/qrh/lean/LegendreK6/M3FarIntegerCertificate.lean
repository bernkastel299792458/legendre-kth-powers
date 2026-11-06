import LegendreK6.M3FarIntegerData

/-! Exact integer/rational evaluation of the proposed dyadic pilot factors.
The finite arithmetic assertion is checked by kernel reduction (`decide`). -/

namespace LegendreK6.M3Far

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem rationalLowRank20_le :
    rationalLowRank20 48 sigmaRows heightRows ≤ (9 / 20 : ℚ) := by
  decide +kernel

theorem dyadicLowRank20_le :
    lowRankTaylor20 Finset.univ Finset.univ
      sigmaDyadicFactor sigmaDyadicPower heightDyadicFactor heightDyadicPower ≤
      (9 / 20 : ℝ) := by
  have heq : lowRankTaylor20 Finset.univ Finset.univ
      sigmaDyadicFactor sigmaDyadicPower heightDyadicFactor heightDyadicPower =
      (rationalLowRank20 48 sigmaRows heightRows : ℝ) := by
    exact lowRankTaylor20_eq_rational 48 sigmaRows heightRows
  rw [heq]
  have h := (Rat.cast_le (K := ℝ)).mpr rationalLowRank20_le
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

end LegendreK6.M3Far
