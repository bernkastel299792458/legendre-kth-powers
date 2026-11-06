import LegendreK6.M2Pilot.FactorBounds.Sigma000
import LegendreK6.M2Pilot.FactorBounds.Sigma001
import LegendreK6.M2Pilot.FactorBounds.Sigma002
import LegendreK6.M2Pilot.FactorBounds.Sigma003
import LegendreK6.M2Pilot.FactorBounds.Sigma004
import LegendreK6.M2Pilot.FactorBounds.Sigma005
import LegendreK6.M2Pilot.FactorBounds.Sigma006
import LegendreK6.M2Pilot.FactorBounds.Sigma007
import LegendreK6.M2Pilot.FactorBounds.Sigma008
import LegendreK6.M2Pilot.FactorBounds.Sigma009
import LegendreK6.M2Pilot.FactorBounds.Sigma010
import LegendreK6.M2Pilot.FactorBounds.Sigma011
import LegendreK6.M2Pilot.FactorBounds.Height000
import LegendreK6.M2Pilot.FactorBounds.Height001
import LegendreK6.M2Pilot.FactorBounds.Height002
import LegendreK6.M2Pilot.FactorBounds.Height003
import LegendreK6.M2Pilot.FactorBounds.Height004
import LegendreK6.M2Pilot.FactorBounds.Height005
import LegendreK6.M2Pilot.FactorBounds.Height006
import LegendreK6.M2Pilot.FactorBounds.Height007
import LegendreK6.M2Pilot.FactorBounds.Height008
import LegendreK6.M2Pilot.FactorBounds.Height009
import LegendreK6.M2Pilot.FactorBounds.Height010
import LegendreK6.M2Pilot.FactorBounds.Height011
import LegendreK6.M2Pilot.FactorBounds.Height012
import LegendreK6.M2Pilot.FactorBounds.Height013
import LegendreK6.M2Pilot.FactorBounds.Height014
import LegendreK6.M2Pilot.FactorBounds.Height015
import LegendreK6.M2Pilot.FactorBounds.Height016
import LegendreK6.M2Pilot.FactorBounds.Height017
import LegendreK6.M2Pilot.FactorBounds.Height018
import LegendreK6.M2Pilot.FactorBounds.Height019
import LegendreK6.M2Pilot.FactorBounds.Height020
import LegendreK6.M2Pilot.FactorBounds.Height021
import LegendreK6.M2Pilot.FactorBounds.Height022
import LegendreK6.M2Pilot.FactorBounds.Height023
import LegendreK6.M2Pilot.FactorBounds.Height024
import LegendreK6.M2Pilot.FactorBounds.Height025
import LegendreK6.M2Pilot.FactorBounds.Height026
import LegendreK6.M2Pilot.FactorBounds.Height027
import LegendreK6.M2Pilot.FactorBounds.Height028
import LegendreK6.M2Pilot.FactorBounds.Height029
import LegendreK6.M2Pilot.FactorBounds.Height030

/-! All checked pointwise enclosures for the complete conservative pilot. -/
namespace LegendreK6.M2Pilot
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sigmaDyadicBounds (i : Fin 1536) :
    sigmaFactor i ≤ sigmaDyadicFactor i ∧ sigmaPower i ≤ sigmaDyadicPower i := by
  have hi := i.isLt
  have hk : i.val / 128 < 12 := by omega
  interval_cases h : i.val / 128
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

theorem sigmaFactor_upper (i : Fin 1536) :
    sigmaFactor i ≤ sigmaDyadicFactor i := (sigmaDyadicBounds i).1

theorem sigmaPower_upper (i : Fin 1536) :
    sigmaPower i ≤ sigmaDyadicPower i := (sigmaDyadicBounds i).2

theorem heightDyadicBounds (i : Fin 988) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  have hi := i.isLt
  have hk : i.val / 32 < 31 := by omega
  interval_cases h : i.val / 32
  · exact FactorBounds.Height000.bounds i (by omega) (by omega)
  · exact FactorBounds.Height001.bounds i (by omega) (by omega)
  · exact FactorBounds.Height002.bounds i (by omega) (by omega)
  · exact FactorBounds.Height003.bounds i (by omega) (by omega)
  · exact FactorBounds.Height004.bounds i (by omega) (by omega)
  · exact FactorBounds.Height005.bounds i (by omega) (by omega)
  · exact FactorBounds.Height006.bounds i (by omega) (by omega)
  · exact FactorBounds.Height007.bounds i (by omega) (by omega)
  · exact FactorBounds.Height008.bounds i (by omega) (by omega)
  · exact FactorBounds.Height009.bounds i (by omega) (by omega)
  · exact FactorBounds.Height010.bounds i (by omega) (by omega)
  · exact FactorBounds.Height011.bounds i (by omega) (by omega)
  · exact FactorBounds.Height012.bounds i (by omega) (by omega)
  · exact FactorBounds.Height013.bounds i (by omega) (by omega)
  · exact FactorBounds.Height014.bounds i (by omega) (by omega)
  · exact FactorBounds.Height015.bounds i (by omega) (by omega)
  · exact FactorBounds.Height016.bounds i (by omega) (by omega)
  · exact FactorBounds.Height017.bounds i (by omega) (by omega)
  · exact FactorBounds.Height018.bounds i (by omega) (by omega)
  · exact FactorBounds.Height019.bounds i (by omega) (by omega)
  · exact FactorBounds.Height020.bounds i (by omega) (by omega)
  · exact FactorBounds.Height021.bounds i (by omega) (by omega)
  · exact FactorBounds.Height022.bounds i (by omega) (by omega)
  · exact FactorBounds.Height023.bounds i (by omega) (by omega)
  · exact FactorBounds.Height024.bounds i (by omega) (by omega)
  · exact FactorBounds.Height025.bounds i (by omega) (by omega)
  · exact FactorBounds.Height026.bounds i (by omega) (by omega)
  · exact FactorBounds.Height027.bounds i (by omega) (by omega)
  · exact FactorBounds.Height028.bounds i (by omega) (by omega)
  · exact FactorBounds.Height029.bounds i (by omega) (by omega)
  · exact FactorBounds.Height030.bounds i (by omega) (by omega)

theorem heightFactor_upper (i : Fin 988) :
    heightFactor i ≤ heightDyadicFactor i := (heightDyadicBounds i).1

theorem heightPower_upper (i : Fin 988) :
    heightPower i ≤ heightDyadicPower i := (heightDyadicBounds i).2

end LegendreK6.M2Pilot
