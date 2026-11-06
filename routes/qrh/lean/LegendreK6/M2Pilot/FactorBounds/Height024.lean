import LegendreK6.M2Pilot.Enclosures.Height024
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height024
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 768 ≤ i.val) (hhi : i.val < 800) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (768 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_768.trans
      change ((2071061833 / 281474976710656 : ℚ) : ℝ) ≤ ((2071061833 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_768.trans
      change ((3475891539091437 / 281474976710656 : ℚ) : ℝ) ≤ ((3475891539091437 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (769 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_769.trans
      change ((2019630157 / 281474976710656 : ℚ) : ℝ) ≤ ((2019630157 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_769.trans
      change ((435049676220819 / 35184372088832 : ℚ) : ℝ) ≤ ((3480397409766552 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (770 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_770.trans
      change ((1969475075 / 281474976710656 : ℚ) : ℝ) ≤ ((1969475075 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_770.trans
      change ((217806452447091 / 17592186044416 : ℚ) : ℝ) ≤ ((3484903239153456 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (771 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_771.trans
      change ((1920564917 / 281474976710656 : ℚ) : ℝ) ≤ ((1920564917 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_771.trans
      change ((3489409027283755 / 281474976710656 : ℚ) : ℝ) ≤ ((3489409027283755 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (772 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_772.trans
      change ((29263575 / 4398046511104 : ℚ) : ℝ) ≤ ((1872868800 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_772.trans
      change ((1746957387094511 / 140737488355328 : ℚ) : ℝ) ≤ ((3493914774189022 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (773 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_773.trans
      change ((1826356605 / 281474976710656 : ℚ) : ℝ) ≤ ((1826356605 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_773.trans
      change ((437302559987599 / 35184372088832 : ℚ) : ℝ) ≤ ((3498420479900792 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (774 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_774.trans
      change ((1780998961 / 281474976710656 : ℚ) : ℝ) ≤ ((1780998961 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_774.trans
      change ((3502926144450565 / 281474976710656 : ℚ) : ℝ) ≤ ((3502926144450565 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (775 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_775.trans
      change ((217095903 / 35184372088832 : ℚ) : ℝ) ≤ ((1736767224 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_775.trans
      change ((3507431767869805 / 281474976710656 : ℚ) : ℝ) ≤ ((3507431767869805 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (776 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_776.trans
      change ((846816731 / 140737488355328 : ℚ) : ℝ) ≤ ((1693633462 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_776.trans
      change ((1755968675094969 / 140737488355328 : ℚ) : ℝ) ≤ ((3511937350189938 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (777 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_777.trans
      change ((1651570433 / 281474976710656 : ℚ) : ℝ) ≤ ((1651570433 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_777.trans
      change ((3516442891442357 / 281474976710656 : ℚ) : ℝ) ≤ ((3516442891442357 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (778 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_778.trans
      change ((1610551573 / 281474976710656 : ℚ) : ℝ) ≤ ((1610551573 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_778.trans
      change ((3520948391658415 / 281474976710656 : ℚ) : ℝ) ≤ ((3520948391658415 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (779 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_779.trans
      change ((1570550975 / 281474976710656 : ℚ) : ℝ) ≤ ((1570550975 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_779.trans
      change ((1762726925434717 / 140737488355328 : ℚ) : ℝ) ≤ ((3525453850869434 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (780 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_780.trans
      change ((1531543375 / 281474976710656 : ℚ) : ℝ) ≤ ((1531543375 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_780.trans
      change ((441244908638337 / 35184372088832 : ℚ) : ℝ) ≤ ((3529959269106696 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (781 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_781.trans
      change ((1493504137 / 281474976710656 : ℚ) : ℝ) ≤ ((1493504137 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_781.trans
      change ((1767232323200725 / 140737488355328 : ℚ) : ℝ) ≤ ((3534464646401450 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (782 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_782.trans
      change ((1456409233 / 281474976710656 : ℚ) : ℝ) ≤ ((1456409233 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_782.trans
      change ((3538969982784907 / 281474976710656 : ℚ) : ℝ) ≤ ((3538969982784907 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (783 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_783.trans
      change ((44382351 / 8796093022208 : ℚ) : ℝ) ≤ ((1420235232 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_783.trans
      change ((885868819572061 / 70368744177664 : ℚ) : ℝ) ≤ ((3543475278288244 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (784 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_784.trans
      change ((692479643 / 140737488355328 : ℚ) : ℝ) ≤ ((1384959286 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_784.trans
      change ((1773990266471301 / 140737488355328 : ℚ) : ℝ) ≤ ((3547980532942602 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (785 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_785.trans
      change ((1350559111 / 281474976710656 : ℚ) : ℝ) ≤ ((1350559111 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_785.trans
      change ((3552485746779087 / 281474976710656 : ℚ) : ℝ) ≤ ((3552485746779087 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (786 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_786.trans
      change ((82313311 / 17592186044416 : ℚ) : ℝ) ≤ ((1317012976 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_786.trans
      change ((1778495459914383 / 140737488355328 : ℚ) : ℝ) ≤ ((3556990919828766 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (787 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_787.trans
      change ((642149845 / 140737488355328 : ℚ) : ℝ) ≤ ((1284299690 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_787.trans
      change ((3561496052122677 / 281474976710656 : ℚ) : ℝ) ≤ ((3561496052122677 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (788 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_788.trans
      change ((1252398587 / 281474976710656 : ℚ) : ℝ) ≤ ((1252398587 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_788.trans
      change ((445750142961477 / 35184372088832 : ℚ) : ℝ) ≤ ((3566001143691816 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (789 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_789.trans
      change ((610644757 / 140737488355328 : ℚ) : ℝ) ≤ ((1221289514 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_789.trans
      change ((3570506194567147 / 281474976710656 : ℚ) : ℝ) ≤ ((3570506194567147 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (790 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_790.trans
      change ((74434551 / 17592186044416 : ℚ) : ℝ) ≤ ((1190952816 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_790.trans
      change ((3575011204779599 / 281474976710656 : ℚ) : ℝ) ≤ ((3575011204779599 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (791 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_791.trans
      change ((72585583 / 17592186044416 : ℚ) : ℝ) ≤ ((1161369328 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_791.trans
      change ((3579516174360065 / 281474976710656 : ℚ) : ℝ) ≤ ((3579516174360065 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (792 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_792.trans
      change ((1132520359 / 281474976710656 : ℚ) : ℝ) ≤ ((1132520359 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_792.trans
      change ((3584021103339403 / 281474976710656 : ℚ) : ℝ) ≤ ((3584021103339403 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (793 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_793.trans
      change ((34512115 / 8796093022208 : ℚ) : ℝ) ≤ ((1104387680 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_793.trans
      change ((1794262995874217 / 140737488355328 : ℚ) : ℝ) ≤ ((3588525991748434 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (794 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_794.trans
      change ((538476759 / 140737488355328 : ℚ) : ℝ) ≤ ((1076953518 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_794.trans
      change ((898257709904487 / 70368744177664 : ℚ) : ℝ) ≤ ((3593030839617948 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (795 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_795.trans
      change ((1050200537 / 281474976710656 : ℚ) : ℝ) ≤ ((1050200537 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_795.trans
      change ((3597535646978695 / 281474976710656 : ℚ) : ℝ) ≤ ((3597535646978695 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (796 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_796.trans
      change ((512055917 / 140737488355328 : ℚ) : ℝ) ≤ ((1024111834 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_796.trans
      change ((1801020206930697 / 140737488355328 : ℚ) : ℝ) ≤ ((3602040413861394 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (797 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_797.trans
      change ((499335461 / 140737488355328 : ℚ) : ℝ) ≤ ((998670922 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_797.trans
      change ((450818142537091 / 35184372088832 : ℚ) : ℝ) ≤ ((3606545140296728 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (798 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_798.trans
      change ((973861725 / 281474976710656 : ℚ) : ℝ) ≤ ((973861725 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_798.trans
      change ((225690614144709 / 17592186044416 : ℚ) : ℝ) ≤ ((3611049826315344 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (799 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height024.height_factor_upper_799.trans
      change ((949668567 / 281474976710656 : ℚ) : ℝ) ≤ ((949668567 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height024.height_power_upper_799.trans
      change ((3615554471947855 / 281474976710656 : ℚ) : ℝ) ≤ ((3615554471947855 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height024
