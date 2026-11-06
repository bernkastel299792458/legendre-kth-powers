import LegendreK6.M2Pilot.Enclosures.Height022
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height022
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 704 ≤ i.val) (hhi : i.val < 736) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (704 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_704.trans
      change ((5173899179 / 140737488355328 : ℚ) : ℝ) ≤ ((10347798358 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_704.trans
      change ((3187428461609381 / 281474976710656 : ℚ) : ℝ) ≤ ((3187428461609381 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (705 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_705.trans
      change ((10091046675 / 281474976710656 : ℚ) : ℝ) ≤ ((10091046675 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_705.trans
      change ((3191937042179125 / 281474976710656 : ℚ) : ℝ) ≤ ((3191937042179125 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (706 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_706.trans
      change ((2460165517 / 70368744177664 : ℚ) : ℝ) ≤ ((9840662068 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_706.trans
      change ((3196445579359641 / 281474976710656 : ℚ) : ℝ) ≤ ((3196445579359641 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (707 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_707.trans
      change ((9596486733 / 281474976710656 : ℚ) : ℝ) ≤ ((9596486733 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_707.trans
      change ((3200954073184977 / 281474976710656 : ℚ) : ℝ) ≤ ((3200954073184977 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (708 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_708.trans
      change ((9358366775 / 281474976710656 : ℚ) : ℝ) ≤ ((9358366775 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_708.trans
      change ((1602731261844573 / 140737488355328 : ℚ) : ℝ) ≤ ((3205462523689146 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (709 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_709.trans
      change ((9126152111 / 281474976710656 : ℚ) : ℝ) ≤ ((9126152111 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_709.trans
      change ((3209970930906119 / 281474976710656 : ℚ) : ℝ) ≤ ((3209970930906119 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (710 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_710.trans
      change ((1112462047 / 35184372088832 : ℚ) : ℝ) ≤ ((8899696376 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_710.trans
      change ((50226238982341 / 4398046511104 : ℚ) : ℝ) ≤ ((3214479294869824 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (711 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_711.trans
      change ((8678856829 / 281474976710656 : ℚ) : ℝ) ≤ ((8678856829 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_711.trans
      change ((3218987615614155 / 281474976710656 : ℚ) : ℝ) ≤ ((3218987615614155 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (712 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_712.trans
      change ((8463494267 / 281474976710656 : ℚ) : ℝ) ≤ ((8463494267 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_712.trans
      change ((3223495893172961 / 281474976710656 : ℚ) : ℝ) ≤ ((3223495893172961 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (713 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_713.trans
      change ((8253472933 / 281474976710656 : ℚ) : ℝ) ≤ ((8253472933 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_713.trans
      change ((3228004127580055 / 281474976710656 : ℚ) : ℝ) ≤ ((3228004127580055 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (714 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_714.trans
      change ((2012165109 / 70368744177664 : ℚ) : ℝ) ≤ ((8048660436 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_714.trans
      change ((3232512318869207 / 281474976710656 : ℚ) : ℝ) ≤ ((3232512318869207 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (715 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_715.trans
      change ((3924463831 / 140737488355328 : ℚ) : ℝ) ≤ ((7848927662 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_715.trans
      change ((1618510233537075 / 140737488355328 : ℚ) : ℝ) ≤ ((3237020467074150 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (716 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_716.trans
      change ((956768587 / 35184372088832 : ℚ) : ℝ) ≤ ((7654148696 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_716.trans
      change ((3241528572228577 / 281474976710656 : ℚ) : ℝ) ≤ ((3241528572228577 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (717 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_717.trans
      change ((3732100371 / 140737488355328 : ℚ) : ℝ) ≤ ((7464200742 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_717.trans
      change ((3246036634366139 / 281474976710656 : ℚ) : ℝ) ≤ ((3246036634366139 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (718 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_718.trans
      change ((7278964049 / 281474976710656 : ℚ) : ℝ) ≤ ((7278964049 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_718.trans
      change ((3250544653520451 / 281474976710656 : ℚ) : ℝ) ≤ ((3250544653520451 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (719 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_719.trans
      change ((1774580457 / 70368744177664 : ℚ) : ℝ) ≤ ((7098321828 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_719.trans
      change ((3255052629725087 / 281474976710656 : ℚ) : ℝ) ≤ ((3255052629725087 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (720 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_720.trans
      change ((1730540047 / 70368744177664 : ℚ) : ℝ) ≤ ((6922160188 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_720.trans
      change ((3259560563013581 / 281474976710656 : ℚ) : ℝ) ≤ ((3259560563013581 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (721 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_721.trans
      change ((843796007 / 35184372088832 : ℚ) : ℝ) ≤ ((6750368056 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_721.trans
      change ((1632034226709715 / 140737488355328 : ℚ) : ℝ) ≤ ((3264068453419430 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (722 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_722.trans
      change ((6582837113 / 281474976710656 : ℚ) : ℝ) ≤ ((6582837113 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_722.trans
      change ((3268576300976089 / 281474976710656 : ℚ) : ℝ) ≤ ((3268576300976089 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (723 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_723.trans
      change ((3209730861 / 140737488355328 : ℚ) : ℝ) ≤ ((6419461722 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_723.trans
      change ((3273084105716975 / 281474976710656 : ℚ) : ℝ) ≤ ((3273084105716975 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (724 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_724.trans
      change ((6260138865 / 281474976710656 : ℚ) : ℝ) ≤ ((6260138865 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_724.trans
      change ((819397966918867 / 70368744177664 : ℚ) : ℝ) ≤ ((3277591867675468 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (725 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_725.trans
      change ((6104768075 / 281474976710656 : ℚ) : ℝ) ≤ ((6104768075 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_725.trans
      change ((3282099586884905 / 281474976710656 : ℚ) : ℝ) ≤ ((3282099586884905 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (726 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_726.trans
      change ((5953251375 / 281474976710656 : ℚ) : ℝ) ≤ ((5953251375 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_726.trans
      change ((3286607263378587 / 281474976710656 : ℚ) : ℝ) ≤ ((3286607263378587 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (727 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_727.trans
      change ((5805493215 / 281474976710656 : ℚ) : ℝ) ≤ ((5805493215 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_727.trans
      change ((3291114897189775 / 281474976710656 : ℚ) : ℝ) ≤ ((3291114897189775 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (728 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_728.trans
      change ((2830700207 / 140737488355328 : ℚ) : ℝ) ≤ ((5661400414 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_728.trans
      change ((823905622087923 / 70368744177664 : ℚ) : ℝ) ≤ ((3295622488351692 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (729 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_729.trans
      change ((5520882097 / 281474976710656 : ℚ) : ℝ) ≤ ((5520882097 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_729.trans
      change ((3300130036897521 / 281474976710656 : ℚ) : ℝ) ≤ ((3300130036897521 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (730 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_730.trans
      change ((1345962411 / 70368744177664 : ℚ) : ℝ) ≤ ((5383849644 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_730.trans
      change ((3304637542860407 / 281474976710656 : ℚ) : ℝ) ≤ ((3304637542860407 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (731 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_731.trans
      change ((5250216627 / 281474976710656 : ℚ) : ℝ) ≤ ((5250216627 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_731.trans
      change ((206821562892091 / 17592186044416 : ℚ) : ℝ) ≤ ((3309145006273456 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (732 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_732.trans
      change ((1279974691 / 70368744177664 : ℚ) : ℝ) ≤ ((5119898764 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_732.trans
      change ((3313652427169737 / 281474976710656 : ℚ) : ℝ) ≤ ((3313652427169737 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (733 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_733.trans
      change ((2496406929 / 140737488355328 : ℚ) : ℝ) ≤ ((4992813858 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_733.trans
      change ((1659079902791139 / 140737488355328 : ℚ) : ℝ) ≤ ((3318159805582278 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (734 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_734.trans
      change ((2434440875 / 140737488355328 : ℚ) : ℝ) ≤ ((4868881750 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_734.trans
      change ((1661333570772035 / 140737488355328 : ℚ) : ℝ) ≤ ((3322667141544070 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (735 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height022.height_factor_upper_735.trans
      change ((1187006067 / 70368744177664 : ℚ) : ℝ) ≤ ((4748024268 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height022.height_power_upper_735.trans
      change ((3327174435088065 / 281474976710656 : ℚ) : ℝ) ≤ ((3327174435088065 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height022
