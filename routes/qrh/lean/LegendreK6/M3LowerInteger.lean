import LegendreK6.M3LowerIntegerCertificate
import LegendreK6.M2PilotFactorBounds

/-! The lower-middle certificate reuses every M2 factor enclosure.
Only exact rational multipliers and integer-moment evaluation are new. -/

namespace LegendreK6
open scoped BigOperators

theorem positiveMoment_smul_left {ι : Type*} (s : Finset ι) (f a : ι → ℝ)
    (c : ℝ) (n : ℕ) :
    positiveMoment s (fun i => c*f i) a n = c*positiveMoment s f a n := by
  unfold positiveMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem lowRankTaylor20_smul_left {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (f a : ι → ℝ) (g b : κ → ℝ) (c : ℝ) :
    lowRankTaylor20 s t (fun i => c*f i) a g b = c*lowRankTaylor20 s t f a g b := by
  unfold lowRankTaylor20
  simp_rw [positiveMoment_smul_left]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro n _
    ring
  · ring

namespace M3Lower
open M2Pilot

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem dyadic_double_budget :
    lowRankTaylor20 Finset.univ Finset.univ
      (fun j : Fin 1536 => (multiplierNat j.val : ℝ)*sigmaDyadicFactor j)
      sigmaDyadicPower heightDyadicFactor heightDyadicPower ≤ (193/100 : ℝ) := by
  have h := (Rat.cast_le (K := ℝ)).mpr rational_double_budget
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  rw [← lowRankTaylor20_eq_rational 48 doubleSigmaRows heightRows] at h
  have hc : (fun j : Fin 1536 => (multiplierNat j.val : ℝ)*sigmaDyadicFactor j) =
      (fun j => dyadicCoefficient 48 doubleSigmaRows (doubleRowIndex j)) := by
    funext j
    exact (double_factor j).symm
  have hp : sigmaDyadicPower =
      (fun j : Fin 1536 => dyadicPower 48 doubleSigmaRows (doubleRowIndex j)) := by
    funext j
    exact (double_power j).symm
  rw [hc, hp]
  exact h

theorem weighted_lowRank_le :
    lowRankTaylor20 Finset.univ Finset.univ
      (fun j : Fin 1536 => multiplier j*sigmaFactor j) sigmaPower
      heightFactor heightPower ≤ (193/200 : ℝ) := by
  have hm := lowRankTaylor20_mono (Finset.univ : Finset (Fin 1536))
    (Finset.univ : Finset (Fin 988))
    (fun j => multiplier j*sigmaFactor j) sigmaPower
    (fun j => multiplier j*sigmaDyadicFactor j) sigmaDyadicPower
    heightFactor heightPower heightDyadicFactor heightDyadicPower
    (fun j _ => mul_nonneg (multiplier_nonneg j) (sigmaFactor_nonneg j))
    (fun j _ => (sigmaPower_bounds j).1)
    (fun i _ => heightFactor_nonneg i) (fun i _ => (heightPower_bounds i).1)
    (fun j _ => mul_le_mul_of_nonneg_left (sigmaFactor_upper j) (multiplier_nonneg j))
    (fun j _ => sigmaPower_upper j) (fun i _ => heightFactor_upper i)
    (fun i _ => heightPower_upper i)
  have he : (fun j : Fin 1536 => multiplier j*sigmaDyadicFactor j) =
      (fun j : Fin 1536 => (1/2 : ℝ)*((multiplierNat j.val : ℝ)*sigmaDyadicFactor j)) := by
    funext j
    unfold multiplier
    ring
  rw [he, lowRankTaylor20_smul_left] at hm
  have hb := dyadic_double_budget
  linarith

end M3Lower
end LegendreK6
