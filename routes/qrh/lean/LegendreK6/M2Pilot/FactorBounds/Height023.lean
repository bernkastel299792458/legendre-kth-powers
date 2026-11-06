import LegendreK6.M2Pilot.Enclosures.Height023
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height023
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 736 ≤ i.val) (hhi : i.val < 768) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (736 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_736.trans
      change ((578770647 / 35184372088832 : ℚ) : ℝ) ≤ ((4630165176 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_736.trans
      change ((3331681686247177 / 281474976710656 : ℚ) : ℝ) ≤ ((3331681686247177 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (737 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_737.trans
      change ((4515230127 / 281474976710656 : ℚ) : ℝ) ≤ ((4515230127 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_737.trans
      change ((1668094447527141 / 140737488355328 : ℚ) : ℝ) ≤ ((3336188895054282 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (738 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_738.trans
      change ((4403146619 / 281474976710656 : ℚ) : ℝ) ≤ ((4403146619 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_738.trans
      change ((1670348030771109 / 140737488355328 : ℚ) : ℝ) ≤ ((3340696061542218 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (739 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_739.trans
      change ((4293843943 / 281474976710656 : ℚ) : ℝ) ≤ ((4293843943 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_739.trans
      change ((1672601592871891 / 140737488355328 : ℚ) : ℝ) ≤ ((3345203185743782 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (740 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_740.trans
      change ((4187253145 / 281474976710656 : ℚ) : ℝ) ≤ ((4187253145 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_740.trans
      change ((3349710267691737 / 281474976710656 : ℚ) : ℝ) ≤ ((3349710267691737 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (741 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_741.trans
      change ((2041653489 / 140737488355328 : ℚ) : ℝ) ≤ ((4083306978 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_741.trans
      change ((3354217307418805 / 281474976710656 : ℚ) : ℝ) ≤ ((3354217307418805 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (742 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_742.trans
      change ((3981939863 / 281474976710656 : ℚ) : ℝ) ≤ ((3981939863 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_742.trans
      change ((419840538119709 / 35184372088832 : ℚ) : ℝ) ≤ ((3358724304957672 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (743 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_743.trans
      change ((1941543923 / 140737488355328 : ℚ) : ℝ) ≤ ((3883087846 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_743.trans
      change ((420403907542623 / 35184372088832 : ℚ) : ℝ) ≤ ((3363231260340984 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (744 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_744.trans
      change ((1893344279 / 140737488355328 : ℚ) : ℝ) ≤ ((3786688558 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_744.trans
      change ((3367738173601351 / 281474976710656 : ℚ) : ℝ) ≤ ((3367738173601351 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (745 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_745.trans
      change ((1846340587 / 140737488355328 : ℚ) : ℝ) ≤ ((3692681174 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_745.trans
      change ((210765315298209 / 17592186044416 : ℚ) : ℝ) ≤ ((3372245044771344 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (746 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_746.trans
      change ((3601006379 / 281474976710656 : ℚ) : ℝ) ≤ ((3601006379 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_746.trans
      change ((3376751873883497 / 281474976710656 : ℚ) : ℝ) ≤ ((3376751873883497 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (747 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_747.trans
      change ((3511606327 / 281474976710656 : ℚ) : ℝ) ≤ ((3511606327 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_747.trans
      change ((1690629330485153 / 140737488355328 : ℚ) : ℝ) ≤ ((3381258660970306 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (748 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_748.trans
      change ((3424424605 / 281474976710656 : ℚ) : ℝ) ≤ ((3424424605 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_748.trans
      change ((846441351516057 / 70368744177664 : ℚ) : ℝ) ≤ ((3385765406064228 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (749 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_749.trans
      change ((417425775 / 35184372088832 : ℚ) : ℝ) ≤ ((3339406200 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_749.trans
      change ((1695136054598843 / 140737488355328 : ℚ) : ℝ) ≤ ((3390272109197686 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (750 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_750.trans
      change ((3256497461 / 281474976710656 : ℚ) : ℝ) ≤ ((3256497461 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_750.trans
      change ((3394778770403061 / 281474976710656 : ℚ) : ℝ) ≤ ((3394778770403061 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (751 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_751.trans
      change ((1587823033 / 140737488355328 : ℚ) : ℝ) ≤ ((3175646066 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_751.trans
      change ((3399285389712699 / 281474976710656 : ℚ) : ℝ) ≤ ((3399285389712699 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (752 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_752.trans
      change ((3096800993 / 281474976710656 : ℚ) : ℝ) ≤ ((3096800993 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_752.trans
      change ((3403791967158909 / 281474976710656 : ℚ) : ℝ) ≤ ((3403791967158909 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (753 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_753.trans
      change ((1509956241 / 140737488355328 : ℚ) : ℝ) ≤ ((3019912482 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_753.trans
      change ((1704149251386981 / 140737488355328 : ℚ) : ℝ) ≤ ((3408298502773962 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (754 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_754.trans
      change ((2944932007 / 281474976710656 : ℚ) : ℝ) ≤ ((2944932007 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_754.trans
      change ((3412804996590091 / 281474976710656 : ℚ) : ℝ) ≤ ((3412804996590091 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (755 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_755.trans
      change ((2871812245 / 281474976710656 : ℚ) : ℝ) ≤ ((2871812245 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_755.trans
      change ((3417311448639493 / 281474976710656 : ℚ) : ℝ) ≤ ((3417311448639493 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (756 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_756.trans
      change ((2800507047 / 281474976710656 : ℚ) : ℝ) ≤ ((2800507047 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_756.trans
      change ((1710908929477163 / 140737488355328 : ℚ) : ℝ) ≤ ((3421817858954326 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (757 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_757.trans
      change ((2730971405 / 281474976710656 : ℚ) : ℝ) ≤ ((2730971405 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_757.trans
      change ((1713162113783357 / 140737488355328 : ℚ) : ℝ) ≤ ((3426324227566714 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (758 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_758.trans
      change ((2663161431 / 281474976710656 : ℚ) : ℝ) ≤ ((2663161431 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_758.trans
      change ((857707638627185 / 70368744177664 : ℚ) : ℝ) ≤ ((3430830554508740 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (759 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_759.trans
      change ((2597034321 / 281474976710656 : ℚ) : ℝ) ≤ ((2597034321 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_759.trans
      change ((858834209953113 / 70368744177664 : ℚ) : ℝ) ≤ ((3435336839812452 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (760 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_760.trans
      change ((1266274167 / 140737488355328 : ℚ) : ℝ) ≤ ((2532548334 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_760.trans
      change ((3439843083509863 / 281474976710656 : ℚ) : ℝ) ≤ ((3439843083509863 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (761 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_761.trans
      change ((617415691 / 70368744177664 : ℚ) : ℝ) ≤ ((2469662764 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_761.trans
      change ((3444349285632945 / 281474976710656 : ℚ) : ℝ) ≤ ((3444349285632945 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (762 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_762.trans
      change ((1204168957 / 140737488355328 : ℚ) : ℝ) ≤ ((2408337914 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_762.trans
      change ((3448855446213637 / 281474976710656 : ℚ) : ℝ) ≤ ((3448855446213637 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (763 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_763.trans
      change ((2348535069 / 281474976710656 : ℚ) : ℝ) ≤ ((2348535069 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_763.trans
      change ((1726680782641919 / 140737488355328 : ℚ) : ℝ) ≤ ((3453361565283838 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (764 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_764.trans
      change ((572554119 / 70368744177664 : ℚ) : ℝ) ≤ ((2290216476 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_764.trans
      change ((3457867642875413 / 281474976710656 : ℚ) : ℝ) ≤ ((3457867642875413 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (765 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_765.trans
      change ((2233345319 / 281474976710656 : ℚ) : ℝ) ≤ ((2233345319 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_765.trans
      change ((865593419755047 / 70368744177664 : ℚ) : ℝ) ≤ ((3462373679020188 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (766 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_766.trans
      change ((1088942845 / 140737488355328 : ℚ) : ℝ) ≤ ((2177885690 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_766.trans
      change ((3466879673749953 / 281474976710656 : ℚ) : ℝ) ≤ ((3466879673749953 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (767 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height023.height_factor_upper_767.trans
      change ((1061901289 / 140737488355328 : ℚ) : ℝ) ≤ ((2123802578 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height023.height_power_upper_767.trans
      change ((216961601693529 / 17592186044416 : ℚ) : ℝ) ≤ ((3471385627096464 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height023
