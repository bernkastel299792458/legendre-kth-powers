import LegendreK6.M3Far.FactorBounds.Sigma000
import LegendreK6.M3Far.FactorBounds.Sigma001
import LegendreK6.M3Far.FactorBounds.Sigma002
import LegendreK6.M3Far.FactorBounds.Sigma003
import LegendreK6.M3Far.FactorBounds.Sigma004
import LegendreK6.M3Far.FactorBounds.Sigma005
import LegendreK6.M3Far.FactorBounds.Sigma006
import LegendreK6.M3Far.FactorBounds.Sigma007
import LegendreK6.M3Far.FactorBounds.Sigma008
import LegendreK6.M3Far.FactorBounds.Sigma009
import LegendreK6.M3Far.FactorBounds.Sigma010
import LegendreK6.M3Far.FactorBounds.Sigma011
import LegendreK6.M3Far.FactorBounds.Height000
import LegendreK6.M3Far.FactorBounds.Height001
import LegendreK6.M3Far.FactorBounds.Height002
import LegendreK6.M3Far.FactorBounds.Height003

/-! All checked pointwise enclosures for the complete conservative pilot. -/
namespace LegendreK6.M3Far
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sigmaDyadicBounds (i : Fin 384) :
    sigmaFactor i ≤ sigmaDyadicFactor i ∧ sigmaPower i ≤ sigmaDyadicPower i := by
  have hi := i.isLt
  have hk : i.val / 32 < 12 := by omega
  interval_cases h : i.val / 32
  · exact FactorBounds.Sigma000.bounds i (by omega) (by omega)
  · exact FactorBounds.Sigma001.bounds i (by omega) (by omega)
  · exact FactorBounds.Sigma002.bounds i (by omega) (by omega)
  · exact FactorBounds.Sigma003.bounds i (by omega) (by omega)
  · exact FactorBounds.Sigma004.bounds i (by omega) (by omega)
  · exact FactorBounds.Sigma005.bounds i (by omega) (by omega)
  · exact FactorBounds.Sigma006.bounds i (by omega) (by omega)
  · exact FactorBounds.Sigma007.bounds i (by omega) (by omega)
  · exact FactorBounds.Sigma008.bounds i (by omega) (by omega)
  · exact FactorBounds.Sigma009.bounds i (by omega) (by omega)
  · exact FactorBounds.Sigma010.bounds i (by omega) (by omega)
  · exact FactorBounds.Sigma011.bounds i (by omega) (by omega)

theorem sigmaFactor_upper (i : Fin 384) :
    sigmaFactor i ≤ sigmaDyadicFactor i := (sigmaDyadicBounds i).1

theorem sigmaPower_upper (i : Fin 384) :
    sigmaPower i ≤ sigmaDyadicPower i := (sigmaDyadicBounds i).2

theorem heightDyadicBounds (i : Fin 125) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  have hi := i.isLt
  have hk : i.val / 32 < 4 := by omega
  interval_cases h : i.val / 32
  · exact FactorBounds.Height000.bounds i (by omega) (by omega)
  · exact FactorBounds.Height001.bounds i (by omega) (by omega)
  · exact FactorBounds.Height002.bounds i (by omega) (by omega)
  · exact FactorBounds.Height003.bounds i (by omega) (by omega)

theorem heightFactor_upper (i : Fin 125) :
    heightFactor i ≤ heightDyadicFactor i := (heightDyadicBounds i).1

theorem heightPower_upper (i : Fin 125) :
    heightPower i ≤ heightDyadicPower i := (heightDyadicBounds i).2

end LegendreK6.M3Far
