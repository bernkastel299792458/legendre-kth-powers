import LegendreK6.M2Pilot.Enclosures.Sigma006
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Sigma006
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 1536) (hlo : 768 ≤ i.val) (hhi : i.val < 896) :
    sigmaFactor i ≤ sigmaDyadicFactor i ∧ sigmaPower i ≤ sigmaDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (768 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_768.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_768.trans
      change ((107228562556441 / 281474976710656 : ℚ) : ℝ) ≤ ((107228562556441 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (769 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_769.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_769.trans
      change ((53554432778189 / 140737488355328 : ℚ) : ℝ) ≤ ((107108865556378 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (770 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_770.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_770.trans
      change ((13373640501201 / 35184372088832 : ℚ) : ℝ) ≤ ((106989124009608 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (771 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_771.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_771.trans
      change ((26717334472815 / 70368744177664 : ℚ) : ℝ) ≤ ((106869337891260 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (772 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_772.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_772.trans
      change ((53374753588221 / 140737488355328 : ℚ) : ℝ) ≤ ((106749507176442 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (773 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_773.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_773.trans
      change ((26657407960061 / 70368744177664 : ℚ) : ℝ) ≤ ((106629631840244 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (774 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_774.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_774.trans
      change ((53254855928869 / 140737488355328 : ℚ) : ℝ) ≤ ((106509711857738 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (775 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_775.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_775.trans
      change ((106389747203979 / 281474976710656 : ℚ) : ℝ) ≤ ((106389747203979 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (776 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_776.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_776.trans
      change ((106269737853999 / 281474976710656 : ℚ) : ℝ) ≤ ((106269737853999 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (777 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_777.trans
      change ((1 / 140737488355328 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_777.trans
      change ((106149683782815 / 281474976710656 : ℚ) : ℝ) ≤ ((106149683782815 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (778 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_778.trans
      change ((1 / 140737488355328 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_778.trans
      change ((53014792482713 / 140737488355328 : ℚ) : ℝ) ≤ ((106029584965426 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (779 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_779.trans
      change ((1 / 140737488355328 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_779.trans
      change ((105909441376809 / 281474976710656 : ℚ) : ℝ) ≤ ((105909441376809 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (780 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_780.trans
      change ((1 / 140737488355328 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_780.trans
      change ((105789252991925 / 281474976710656 : ℚ) : ℝ) ≤ ((105789252991925 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (781 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_781.trans
      change ((1 / 140737488355328 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_781.trans
      change ((105669019785715 / 281474976710656 : ℚ) : ℝ) ≤ ((105669019785715 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (782 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_782.trans
      change ((1 / 140737488355328 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_782.trans
      change ((52774370866551 / 140737488355328 : ℚ) : ℝ) ≤ ((105548741733102 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (783 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_783.trans
      change ((1 / 140737488355328 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_783.trans
      change ((105428418808991 / 281474976710656 : ℚ) : ℝ) ≤ ((105428418808991 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (784 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_784.trans
      change ((1 / 140737488355328 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_784.trans
      change ((52654025494133 / 140737488355328 : ℚ) : ℝ) ≤ ((105308050988266 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (785 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_785.trans
      change ((1 / 140737488355328 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_785.trans
      change ((52593819122897 / 140737488355328 : ℚ) : ℝ) ≤ ((105187638245794 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (786 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_786.trans
      change ((1 / 140737488355328 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_786.trans
      change ((105067180556423 / 281474976710656 : ℚ) : ℝ) ≤ ((105067180556423 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (787 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_787.trans
      change ((1 / 140737488355328 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_787.trans
      change ((52473338947491 / 140737488355328 : ℚ) : ℝ) ≤ ((104946677894982 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (788 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_788.trans
      change ((1 / 140737488355328 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_788.trans
      change ((52413065118141 / 140737488355328 : ℚ) : ℝ) ≤ ((104826130236282 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (789 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_789.trans
      change ((1 / 140737488355328 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_789.trans
      change ((104705537555113 / 281474976710656 : ℚ) : ℝ) ≤ ((104705537555113 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (790 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_790.trans
      change ((1 / 140737488355328 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_790.trans
      change ((13073112478281 / 35184372088832 : ℚ) : ℝ) ≤ ((104584899826248 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (791 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_791.trans
      change ((1 / 140737488355328 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_791.trans
      change ((52232108512221 / 140737488355328 : ℚ) : ℝ) ≤ ((104464217024442 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (792 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_792.trans
      change ((1 / 140737488355328 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_792.trans
      change ((104343489124429 / 281474976710656 : ℚ) : ℝ) ≤ ((104343489124429 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (793 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_793.trans
      change ((1 / 140737488355328 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_793.trans
      change ((104222716100925 / 281474976710656 : ℚ) : ℝ) ≤ ((104222716100925 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (794 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_794.trans
      change ((1 / 140737488355328 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_794.trans
      change ((104101897928627 / 281474976710656 : ℚ) : ℝ) ≤ ((104101897928627 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (795 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_795.trans
      change ((1 / 140737488355328 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_795.trans
      change ((103981034582213 / 281474976710656 : ℚ) : ℝ) ≤ ((103981034582213 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (796 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_796.trans
      change ((1 / 140737488355328 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_796.trans
      change ((103860126036343 / 281474976710656 : ℚ) : ℝ) ≤ ((103860126036343 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (797 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_797.trans
      change ((1 / 140737488355328 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_797.trans
      change ((103739172265657 / 281474976710656 : ℚ) : ℝ) ≤ ((103739172265657 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (798 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_798.trans
      change ((1 / 140737488355328 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_798.trans
      change ((12952271655597 / 35184372088832 : ℚ) : ℝ) ≤ ((103618173244776 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (799 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_799.trans
      change ((1 / 140737488355328 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_799.trans
      change ((103497128948303 / 281474976710656 : ℚ) : ℝ) ≤ ((103497128948303 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (800 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_800.trans
      change ((3 / 281474976710656 : ℚ) : ℝ) ≤ ((3 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_800.trans
      change ((25844009837705 / 70368744177664 : ℚ) : ℝ) ≤ ((103376039350820 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (801 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_801.trans
      change ((3 / 281474976710656 : ℚ) : ℝ) ≤ ((3 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_801.trans
      change ((103254904426893 / 281474976710656 : ℚ) : ℝ) ≤ ((103254904426893 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (802 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_802.trans
      change ((3 / 281474976710656 : ℚ) : ℝ) ≤ ((3 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_802.trans
      change ((51566862075533 / 140737488355328 : ℚ) : ℝ) ≤ ((103133724151066 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (803 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_803.trans
      change ((3 / 281474976710656 : ℚ) : ℝ) ≤ ((3 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_803.trans
      change ((103012498497865 / 281474976710656 : ℚ) : ℝ) ≤ ((103012498497865 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (804 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_804.trans
      change ((3 / 281474976710656 : ℚ) : ℝ) ≤ ((3 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_804.trans
      change ((51445613720899 / 140737488355328 : ℚ) : ℝ) ≤ ((102891227441798 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (805 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_805.trans
      change ((3 / 281474976710656 : ℚ) : ℝ) ≤ ((3 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_805.trans
      change ((102769910957353 / 281474976710656 : ℚ) : ℝ) ≤ ((102769910957353 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (806 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_806.trans
      change ((3 / 281474976710656 : ℚ) : ℝ) ≤ ((3 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_806.trans
      change ((51324274509499 / 140737488355328 : ℚ) : ℝ) ≤ ((102648549018998 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (807 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_807.trans
      change ((3 / 281474976710656 : ℚ) : ℝ) ≤ ((3 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_807.trans
      change ((3203973175037 / 8796093022208 : ℚ) : ℝ) ≤ ((102527141601184 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (808 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_808.trans
      change ((3 / 281474976710656 : ℚ) : ℝ) ≤ ((3 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_808.trans
      change ((25601422169585 / 70368744177664 : ℚ) : ℝ) ≤ ((102405688678340 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (809 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_809.trans
      change ((3 / 281474976710656 : ℚ) : ℝ) ≤ ((3 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_809.trans
      change ((102284190224879 / 281474976710656 : ℚ) : ℝ) ≤ ((102284190224879 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (810 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_810.trans
      change ((3 / 281474976710656 : ℚ) : ℝ) ≤ ((3 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_810.trans
      change ((12770330776899 / 35184372088832 : ℚ) : ℝ) ≤ ((102162646215192 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (811 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_811.trans
      change ((3 / 281474976710656 : ℚ) : ℝ) ≤ ((3 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_811.trans
      change ((25510264155913 / 70368744177664 : ℚ) : ℝ) ≤ ((102041056623652 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (812 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_812.trans
      change ((3 / 281474976710656 : ℚ) : ℝ) ≤ ((3 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_812.trans
      change ((50959710712307 / 140737488355328 : ℚ) : ℝ) ≤ ((101919421424614 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (813 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_813.trans
      change ((3 / 281474976710656 : ℚ) : ℝ) ≤ ((3 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_813.trans
      change ((25449435148103 / 70368744177664 : ℚ) : ℝ) ≤ ((101797740592412 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (814 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_814.trans
      change ((1 / 70368744177664 : ℚ) : ℝ) ≤ ((4 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_814.trans
      change ((101676014101361 / 281474976710656 : ℚ) : ℝ) ≤ ((101676014101361 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (815 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_815.trans
      change ((1 / 70368744177664 : ℚ) : ℝ) ≤ ((4 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_815.trans
      change ((101554241925757 / 281474976710656 : ℚ) : ℝ) ≤ ((101554241925757 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (816 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_816.trans
      change ((1 / 70368744177664 : ℚ) : ℝ) ≤ ((4 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_816.trans
      change ((101432424039877 / 281474976710656 : ℚ) : ℝ) ≤ ((101432424039877 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (817 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_817.trans
      change ((1 / 70368744177664 : ℚ) : ℝ) ≤ ((4 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_817.trans
      change ((50655280208989 / 140737488355328 : ℚ) : ℝ) ≤ ((101310560417978 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (818 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_818.trans
      change ((1 / 70368744177664 : ℚ) : ℝ) ≤ ((4 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_818.trans
      change ((50594325517149 / 140737488355328 : ℚ) : ℝ) ≤ ((101188651034298 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (819 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_819.trans
      change ((1 / 70368744177664 : ℚ) : ℝ) ≤ ((4 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_819.trans
      change ((101066695863057 / 281474976710656 : ℚ) : ℝ) ≤ ((101066695863057 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (820 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_820.trans
      change ((1 / 70368744177664 : ℚ) : ℝ) ≤ ((4 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_820.trans
      change ((100944694878453 / 281474976710656 : ℚ) : ℝ) ≤ ((100944694878453 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (821 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_821.trans
      change ((1 / 70368744177664 : ℚ) : ℝ) ≤ ((4 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_821.trans
      change ((50411324027333 / 140737488355328 : ℚ) : ℝ) ≤ ((100822648054666 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (822 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_822.trans
      change ((1 / 70368744177664 : ℚ) : ℝ) ≤ ((4 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_822.trans
      change ((100700555365857 / 281474976710656 : ℚ) : ℝ) ≤ ((100700555365857 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (823 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_823.trans
      change ((5 / 281474976710656 : ℚ) : ℝ) ≤ ((5 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_823.trans
      change ((100578416786167 / 281474976710656 : ℚ) : ℝ) ≤ ((100578416786167 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (824 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_824.trans
      change ((5 / 281474976710656 : ℚ) : ℝ) ≤ ((5 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_824.trans
      change ((50228116144859 / 140737488355328 : ℚ) : ℝ) ≤ ((100456232289718 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (825 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_825.trans
      change ((5 / 281474976710656 : ℚ) : ℝ) ≤ ((5 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_825.trans
      change ((25083500462653 / 70368744177664 : ℚ) : ℝ) ≤ ((100334001850612 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (826 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_826.trans
      change ((5 / 281474976710656 : ℚ) : ℝ) ≤ ((5 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_826.trans
      change ((25052931360733 / 70368744177664 : ℚ) : ℝ) ≤ ((100211725442932 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (827 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_827.trans
      change ((5 / 281474976710656 : ℚ) : ℝ) ≤ ((5 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_827.trans
      change ((25022350760185 / 70368744177664 : ℚ) : ℝ) ≤ ((100089403040740 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (828 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_828.trans
      change ((5 / 281474976710656 : ℚ) : ℝ) ≤ ((5 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_828.trans
      change ((99967034618081 / 281474976710656 : ℚ) : ℝ) ≤ ((99967034618081 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (829 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_829.trans
      change ((5 / 281474976710656 : ℚ) : ℝ) ≤ ((5 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_829.trans
      change ((24961155037245 / 70368744177664 : ℚ) : ℝ) ≤ ((99844620148980 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (830 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_830.trans
      change ((5 / 281474976710656 : ℚ) : ℝ) ≤ ((5 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_830.trans
      change ((99722159607439 / 281474976710656 : ℚ) : ℝ) ≤ ((99722159607439 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (831 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_831.trans
      change ((3 / 140737488355328 : ℚ) : ℝ) ≤ ((6 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_831.trans
      change ((99599652967445 / 281474976710656 : ℚ) : ℝ) ≤ ((99599652967445 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (832 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_832.trans
      change ((3 / 140737488355328 : ℚ) : ℝ) ≤ ((6 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_832.trans
      change ((99477100202963 / 281474976710656 : ℚ) : ℝ) ≤ ((99477100202963 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (833 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_833.trans
      change ((3 / 140737488355328 : ℚ) : ℝ) ≤ ((6 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_833.trans
      change ((99354501287939 / 281474976710656 : ℚ) : ℝ) ≤ ((99354501287939 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (834 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_834.trans
      change ((3 / 140737488355328 : ℚ) : ℝ) ≤ ((6 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_834.trans
      change ((24807964049075 / 70368744177664 : ℚ) : ℝ) ≤ ((99231856196300 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (835 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_835.trans
      change ((3 / 140737488355328 : ℚ) : ℝ) ≤ ((6 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_835.trans
      change ((99109164901951 / 281474976710656 : ℚ) : ℝ) ≤ ((99109164901951 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (836 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_836.trans
      change ((3 / 140737488355328 : ℚ) : ℝ) ≤ ((6 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_836.trans
      change ((98986427378779 / 281474976710656 : ℚ) : ℝ) ≤ ((98986427378779 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (837 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_837.trans
      change ((7 / 281474976710656 : ℚ) : ℝ) ≤ ((7 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_837.trans
      change ((98863643600653 / 281474976710656 : ℚ) : ℝ) ≤ ((98863643600653 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (838 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_838.trans
      change ((7 / 281474976710656 : ℚ) : ℝ) ≤ ((7 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_838.trans
      change ((98740813541419 / 281474976710656 : ℚ) : ℝ) ≤ ((98740813541419 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (839 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_839.trans
      change ((7 / 281474976710656 : ℚ) : ℝ) ≤ ((7 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_839.trans
      change ((49308968587453 / 140737488355328 : ℚ) : ℝ) ≤ ((98617937174906 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (840 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_840.trans
      change ((7 / 281474976710656 : ℚ) : ℝ) ≤ ((7 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_840.trans
      change ((98495014474921 / 281474976710656 : ℚ) : ℝ) ≤ ((98495014474921 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (841 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_841.trans
      change ((7 / 281474976710656 : ℚ) : ℝ) ≤ ((7 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_841.trans
      change ((98372045415253 / 281474976710656 : ℚ) : ℝ) ≤ ((98372045415253 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (842 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_842.trans
      change ((1 / 35184372088832 : ℚ) : ℝ) ≤ ((8 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_842.trans
      change ((49124514984835 / 140737488355328 : ℚ) : ℝ) ≤ ((98249029969670 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (843 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_843.trans
      change ((1 / 35184372088832 : ℚ) : ℝ) ≤ ((8 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_843.trans
      change ((98125968111921 / 281474976710656 : ℚ) : ℝ) ≤ ((98125968111921 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (844 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_844.trans
      change ((1 / 35184372088832 : ℚ) : ℝ) ≤ ((8 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_844.trans
      change ((12250357476967 / 35184372088832 : ℚ) : ℝ) ≤ ((98002859815736 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (845 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_845.trans
      change ((1 / 35184372088832 : ℚ) : ℝ) ≤ ((8 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_845.trans
      change ((97879705054823 / 281474976710656 : ℚ) : ℝ) ≤ ((97879705054823 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (846 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_846.trans
      change ((1 / 35184372088832 : ℚ) : ℝ) ≤ ((8 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_846.trans
      change ((97756503802871 / 281474976710656 : ℚ) : ℝ) ≤ ((97756503802871 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (847 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_847.trans
      change ((9 / 281474976710656 : ℚ) : ℝ) ≤ ((9 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_847.trans
      change ((48816628016775 / 140737488355328 : ℚ) : ℝ) ≤ ((97633256033550 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (848 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_848.trans
      change ((9 / 281474976710656 : ℚ) : ℝ) ≤ ((9 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_848.trans
      change ((48754980860255 / 140737488355328 : ℚ) : ℝ) ≤ ((97509961720510 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (849 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_849.trans
      change ((9 / 281474976710656 : ℚ) : ℝ) ≤ ((9 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_849.trans
      change ((97386620837379 / 281474976710656 : ℚ) : ℝ) ≤ ((97386620837379 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (850 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_850.trans
      change ((9 / 281474976710656 : ℚ) : ℝ) ≤ ((9 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_850.trans
      change ((97263233357769 / 281474976710656 : ℚ) : ℝ) ≤ ((97263233357769 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (851 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_851.trans
      change ((5 / 140737488355328 : ℚ) : ℝ) ≤ ((10 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_851.trans
      change ((24284949813817 / 70368744177664 : ℚ) : ℝ) ≤ ((97139799255268 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (852 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_852.trans
      change ((5 / 140737488355328 : ℚ) : ℝ) ≤ ((10 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_852.trans
      change ((97016318503447 / 281474976710656 : ℚ) : ℝ) ≤ ((97016318503447 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (853 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_853.trans
      change ((5 / 140737488355328 : ℚ) : ℝ) ≤ ((10 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_853.trans
      change ((48446395537927 / 140737488355328 : ℚ) : ℝ) ≤ ((96892791075854 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (854 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_854.trans
      change ((11 / 281474976710656 : ℚ) : ℝ) ≤ ((11 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_854.trans
      change ((96769216946021 / 281474976710656 : ℚ) : ℝ) ≤ ((96769216946021 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (855 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_855.trans
      change ((11 / 281474976710656 : ℚ) : ℝ) ≤ ((11 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_855.trans
      change ((3020174877733 / 8796093022208 : ℚ) : ℝ) ≤ ((96645596087456 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (856 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_856.trans
      change ((11 / 281474976710656 : ℚ) : ℝ) ≤ ((11 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_856.trans
      change ((48260964236825 / 140737488355328 : ℚ) : ℝ) ≤ ((96521928473650 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (857 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_857.trans
      change ((3 / 70368744177664 : ℚ) : ℝ) ≤ ((12 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_857.trans
      change ((96398214078071 / 281474976710656 : ℚ) : ℝ) ≤ ((96398214078071 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (858 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_858.trans
      change ((3 / 70368744177664 : ℚ) : ℝ) ≤ ((12 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_858.trans
      change ((96274452874171 / 281474976710656 : ℚ) : ℝ) ≤ ((96274452874171 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (859 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_859.trans
      change ((3 / 70368744177664 : ℚ) : ℝ) ≤ ((12 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_859.trans
      change ((48075322417689 / 140737488355328 : ℚ) : ℝ) ≤ ((96150644835378 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (860 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_860.trans
      change ((13 / 281474976710656 : ℚ) : ℝ) ≤ ((13 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_860.trans
      change ((48013394967551 / 140737488355328 : ℚ) : ℝ) ≤ ((96026789935102 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (861 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_861.trans
      change ((13 / 281474976710656 : ℚ) : ℝ) ≤ ((13 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_861.trans
      change ((23975722036683 / 70368744177664 : ℚ) : ℝ) ≤ ((95902888146732 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (862 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_862.trans
      change ((13 / 281474976710656 : ℚ) : ℝ) ≤ ((13 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_862.trans
      change ((95778939443637 / 281474976710656 : ℚ) : ℝ) ≤ ((95778939443637 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (863 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_863.trans
      change ((7 / 140737488355328 : ℚ) : ℝ) ≤ ((14 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_863.trans
      change ((47827471899583 / 140737488355328 : ℚ) : ℝ) ≤ ((95654943799166 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (864 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_864.trans
      change ((7 / 140737488355328 : ℚ) : ℝ) ≤ ((14 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_864.trans
      change ((95530901186647 / 281474976710656 : ℚ) : ℝ) ≤ ((95530901186647 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (865 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_865.trans
      change ((7 / 140737488355328 : ℚ) : ℝ) ≤ ((14 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_865.trans
      change ((95406811579391 / 281474976710656 : ℚ) : ℝ) ≤ ((95406811579391 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (866 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_866.trans
      change ((15 / 281474976710656 : ℚ) : ℝ) ≤ ((15 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_866.trans
      change ((23820668737671 / 70368744177664 : ℚ) : ℝ) ≤ ((95282674950684 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (867 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_867.trans
      change ((15 / 281474976710656 : ℚ) : ℝ) ≤ ((15 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_867.trans
      change ((47579245636897 / 140737488355328 : ℚ) : ℝ) ≤ ((95158491273794 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (868 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_868.trans
      change ((1 / 17592186044416 : ℚ) : ℝ) ≤ ((16 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_868.trans
      change ((95034260521971 / 281474976710656 : ℚ) : ℝ) ≤ ((95034260521971 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (869 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_869.trans
      change ((1 / 17592186044416 : ℚ) : ℝ) ≤ ((16 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_869.trans
      change ((11863747833555 / 35184372088832 : ℚ) : ℝ) ≤ ((94909982668440 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (870 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_870.trans
      change ((17 / 281474976710656 : ℚ) : ℝ) ≤ ((17 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_870.trans
      change ((47392828843205 / 140737488355328 : ℚ) : ℝ) ≤ ((94785657686410 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (871 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_871.trans
      change ((17 / 281474976710656 : ℚ) : ℝ) ≤ ((17 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_871.trans
      change ((94661285549067 / 281474976710656 : ℚ) : ℝ) ≤ ((94661285549067 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (872 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_872.trans
      change ((9 / 140737488355328 : ℚ) : ℝ) ≤ ((18 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_872.trans
      change ((47268433114789 / 140737488355328 : ℚ) : ℝ) ≤ ((94536866229578 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (873 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_873.trans
      change ((9 / 140737488355328 : ℚ) : ℝ) ≤ ((18 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_873.trans
      change ((94412399701089 / 281474976710656 : ℚ) : ℝ) ≤ ((94412399701089 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (874 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_874.trans
      change ((19 / 281474976710656 : ℚ) : ℝ) ≤ ((19 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_874.trans
      change ((47143942968363 / 140737488355328 : ℚ) : ℝ) ≤ ((94287885936726 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (875 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_875.trans
      change ((19 / 281474976710656 : ℚ) : ℝ) ≤ ((19 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_875.trans
      change ((47081662454797 / 140737488355328 : ℚ) : ℝ) ≤ ((94163324909594 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (876 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_876.trans
      change ((5 / 70368744177664 : ℚ) : ℝ) ≤ ((20 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_876.trans
      change ((94038716592779 / 281474976710656 : ℚ) : ℝ) ≤ ((94038716592779 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (877 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_877.trans
      change ((5 / 70368744177664 : ℚ) : ℝ) ≤ ((20 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_877.trans
      change ((93914060959343 / 281474976710656 : ℚ) : ℝ) ≤ ((93914060959343 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (878 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_878.trans
      change ((21 / 281474976710656 : ℚ) : ℝ) ≤ ((21 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_878.trans
      change ((93789357982333 / 281474976710656 : ℚ) : ℝ) ≤ ((93789357982333 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (879 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_879.trans
      change ((11 / 140737488355328 : ℚ) : ℝ) ≤ ((22 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_879.trans
      change ((93664607634771 / 281474976710656 : ℚ) : ℝ) ≤ ((93664607634771 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (880 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_880.trans
      change ((11 / 140737488355328 : ℚ) : ℝ) ≤ ((22 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_880.trans
      change ((93539809889661 / 281474976710656 : ℚ) : ℝ) ≤ ((93539809889661 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (881 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_881.trans
      change ((23 / 281474976710656 : ℚ) : ℝ) ≤ ((23 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_881.trans
      change ((93414964719985 / 281474976710656 : ℚ) : ℝ) ≤ ((93414964719985 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (882 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_882.trans
      change ((3 / 35184372088832 : ℚ) : ℝ) ≤ ((24 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_882.trans
      change ((93290072098705 / 281474976710656 : ℚ) : ℝ) ≤ ((93290072098705 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (883 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_883.trans
      change ((3 / 35184372088832 : ℚ) : ℝ) ≤ ((24 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_883.trans
      change ((93165131998763 / 281474976710656 : ℚ) : ℝ) ≤ ((93165131998763 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (884 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_884.trans
      change ((25 / 281474976710656 : ℚ) : ℝ) ≤ ((25 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_884.trans
      change ((93040144393079 / 281474976710656 : ℚ) : ℝ) ≤ ((93040144393079 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (885 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_885.trans
      change ((13 / 140737488355328 : ℚ) : ℝ) ≤ ((26 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_885.trans
      change ((46457554627277 / 140737488355328 : ℚ) : ℝ) ≤ ((92915109254554 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (886 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_886.trans
      change ((13 / 140737488355328 : ℚ) : ℝ) ≤ ((26 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_886.trans
      change ((23197506639017 / 70368744177664 : ℚ) : ℝ) ≤ ((92790026556068 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (887 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_887.trans
      change ((27 / 281474976710656 : ℚ) : ℝ) ≤ ((27 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_887.trans
      change ((5791556016905 / 17592186044416 : ℚ) : ℝ) ≤ ((92664896270480 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (888 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_888.trans
      change ((7 / 70368744177664 : ℚ) : ℝ) ≤ ((28 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_888.trans
      change ((92539718370627 / 281474976710656 : ℚ) : ℝ) ≤ ((92539718370627 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (889 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_889.trans
      change ((29 / 281474976710656 : ℚ) : ℝ) ≤ ((29 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_889.trans
      change ((5775905801833 / 17592186044416 : ℚ) : ℝ) ≤ ((92414492829328 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (890 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_890.trans
      change ((15 / 140737488355328 : ℚ) : ℝ) ≤ ((30 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_890.trans
      change ((92289219619381 / 281474976710656 : ℚ) : ℝ) ≤ ((92289219619381 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (891 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_891.trans
      change ((15 / 140737488355328 : ℚ) : ℝ) ≤ ((30 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_891.trans
      change ((11520487339195 / 35184372088832 : ℚ) : ℝ) ≤ ((92163898713560 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (892 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_892.trans
      change ((31 / 281474976710656 : ℚ) : ℝ) ≤ ((31 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_892.trans
      change ((46019265042311 / 140737488355328 : ℚ) : ℝ) ≤ ((92038530084622 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (893 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_893.trans
      change ((1 / 8796093022208 : ℚ) : ℝ) ≤ ((32 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_893.trans
      change ((45956556852651 / 140737488355328 : ℚ) : ℝ) ≤ ((91913113705302 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (894 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_894.trans
      change ((33 / 281474976710656 : ℚ) : ℝ) ≤ ((33 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_894.trans
      change ((91787649548313 / 281474976710656 : ℚ) : ℝ) ≤ ((91787649548313 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (895 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_895.trans
      change ((17 / 140737488355328 : ℚ) : ℝ) ≤ ((34 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_895.trans
      change ((45831068793175 / 140737488355328 : ℚ) : ℝ) ≤ ((91662137586350 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Sigma006
