import LegendreK6.M3FarFactorBounds
import LegendreK6.M3FarIntegerCertificate
import LegendreK6.M3FarExpression

/-! Kernel-checked numerical conclusion for the actual low-rank expression. -/
namespace LegendreK6.M3Far

theorem lowRankTaylor20_le :
    lowRankTaylor20 Finset.univ Finset.univ sigmaFactor sigmaPower heightFactor heightPower ≤
      (9 / 20 : ℝ) := by
  apply (lowRankTaylor20_mono Finset.univ Finset.univ
    sigmaFactor sigmaPower sigmaDyadicFactor sigmaDyadicPower
    heightFactor heightPower heightDyadicFactor heightDyadicPower
    (fun j _ => sigmaFactor_nonneg j) (fun j _ => (sigmaPower_bounds j).1)
    (fun i _ => heightFactor_nonneg i) (fun i _ => (heightPower_bounds i).1)
    (fun j _ => sigmaFactor_upper j) (fun j _ => sigmaPower_upper j)
    (fun i _ => heightFactor_upper i) (fun i _ => heightPower_upper i)).trans
  exact dyadicLowRank20_le

end LegendreK6.M3Far
