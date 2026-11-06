import LegendreK6.M3LowerComparison
import LegendreK6.M2PilotIntegerData

namespace LegendreK6.M3Lower
open M2Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def doubleSigmaRows : List (ℕ × ℕ) :=
  sigmaRows.mapIdx (fun j v => (multiplierNat j*v.1, v.2))

theorem doubleSigmaRows_length : doubleSigmaRows.length = 1536 := by
  simp only [doubleSigmaRows, List.length_mapIdx, sigmaRows_length]

def doubleRowIndex (j : Fin 1536) : Fin doubleSigmaRows.length :=
  ⟨j.val, by simpa only [doubleSigmaRows_length] using j.isLt⟩

theorem double_factor (j : Fin 1536) :
    dyadicCoefficient 48 doubleSigmaRows (doubleRowIndex j) =
      (multiplierNat j.val : ℝ)*sigmaDyadicFactor j := by
  unfold dyadicCoefficient doubleRowIndex doubleSigmaRows sigmaDyadicFactor
    dyadicCoefficient sigmaRowIndex
  simp only [List.get_eq_getElem, List.getElem_mapIdx, Nat.cast_mul]
  ring

theorem double_power (j : Fin 1536) :
    dyadicPower 48 doubleSigmaRows (doubleRowIndex j) = sigmaDyadicPower j := by
  unfold dyadicPower doubleRowIndex doubleSigmaRows sigmaDyadicPower
    dyadicPower sigmaRowIndex
  simp only [List.get_eq_getElem, List.getElem_mapIdx]

theorem rational_double_budget :
    rationalLowRank20 48 doubleSigmaRows heightRows ≤ (193/100 : ℚ) := by
  decide +kernel

end LegendreK6.M3Lower
