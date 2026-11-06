import LegendreK6.M2Pilot.Enclosures.Height021
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height021
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 672 ≤ i.val) (hhi : i.val < 704) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (672 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_672.trans
      change ((11558759207 / 140737488355328 : ℚ) : ℝ) ≤ ((23117518414 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_672.trans
      change ((760782691995655 / 70368744177664 : ℚ) : ℝ) ≤ ((3043130767982620 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (673 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_673.trans
      change ((22544182709 / 281474976710656 : ℚ) : ℝ) ≤ ((22544182709 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_673.trans
      change ((380955094403703 / 35184372088832 : ℚ) : ℝ) ≤ ((3047640755229624 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (674 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_674.trans
      change ((21985058187 / 281474976710656 : ℚ) : ℝ) ≤ ((21985058187 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_674.trans
      change ((1526075348988117 / 140737488355328 : ℚ) : ℝ) ≤ ((3052150697976234 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (675 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_675.trans
      change ((5359948201 / 70368744177664 : ℚ) : ℝ) ≤ ((21439792804 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_675.trans
      change ((3056660596257819 / 281474976710656 : ℚ) : ℝ) ≤ ((3056660596257819 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (676 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_676.trans
      change ((10454021617 / 140737488355328 : ℚ) : ℝ) ≤ ((20908043234 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_676.trans
      change ((1530585225054851 / 140737488355328 : ℚ) : ℝ) ≤ ((3061170450109702 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (677 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_677.trans
      change ((20389474649 / 281474976710656 : ℚ) : ℝ) ≤ ((20389474649 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_677.trans
      change ((3065680259567167 / 281474976710656 : ℚ) : ℝ) ≤ ((3065680259567167 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (678 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_678.trans
      change ((155341879 / 2199023255552 : ℚ) : ℝ) ≤ ((19883760512 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_678.trans
      change ((3070190024665453 / 281474976710656 : ℚ) : ℝ) ≤ ((3070190024665453 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (679 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_679.trans
      change ((19390582369 / 281474976710656 : ℚ) : ℝ) ≤ ((19390582369 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_679.trans
      change ((192168734089985 / 17592186044416 : ℚ) : ℝ) ≤ ((3074699745439760 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (680 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_680.trans
      change ((18909629653 / 281474976710656 : ℚ) : ℝ) ≤ ((18909629653 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_680.trans
      change ((769802355481311 / 70368744177664 : ℚ) : ℝ) ≤ ((3079209421925244 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (681 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_681.trans
      change ((18440599483 / 281474976710656 : ℚ) : ℝ) ≤ ((18440599483 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_681.trans
      change ((3083719054157021 / 281474976710656 : ℚ) : ℝ) ≤ ((3083719054157021 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (682 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_682.trans
      change ((17983196479 / 281474976710656 : ℚ) : ℝ) ≤ ((17983196479 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_682.trans
      change ((3088228642170163 / 281474976710656 : ℚ) : ℝ) ≤ ((3088228642170163 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (683 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_683.trans
      change ((17537132575 / 281474976710656 : ℚ) : ℝ) ≤ ((17537132575 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_683.trans
      change ((3092738185999703 / 281474976710656 : ℚ) : ℝ) ≤ ((3092738185999703 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (684 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_684.trans
      change ((8551063419 / 140737488355328 : ℚ) : ℝ) ≤ ((17102126838 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_684.trans
      change ((1548623842840315 / 140737488355328 : ℚ) : ℝ) ≤ ((3097247685680630 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (685 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_685.trans
      change ((16677905289 / 281474976710656 : ℚ) : ℝ) ≤ ((16677905289 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_685.trans
      change ((3101757141247893 / 281474976710656 : ℚ) : ℝ) ≤ ((3101757141247893 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (686 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_686.trans
      change ((16264200735 / 281474976710656 : ℚ) : ℝ) ≤ ((16264200735 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_686.trans
      change ((3106266552736399 / 281474976710656 : ℚ) : ℝ) ≤ ((3106266552736399 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (687 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_687.trans
      change ((7930376299 / 140737488355328 : ℚ) : ℝ) ≤ ((15860752598 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_687.trans
      change ((3110775920181013 / 281474976710656 : ℚ) : ℝ) ≤ ((3110775920181013 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (688 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_688.trans
      change ((60419167 / 1099511627776 : ℚ) : ℝ) ≤ ((15467306752 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_688.trans
      change ((3115285243616559 / 281474976710656 : ℚ) : ℝ) ≤ ((3115285243616559 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (689 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_689.trans
      change ((15083615365 / 281474976710656 : ℚ) : ℝ) ≤ ((15083615365 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_689.trans
      change ((779948630769455 / 70368744177664 : ℚ) : ℝ) ≤ ((3119794523077820 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (690 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_690.trans
      change ((14709436743 / 281474976710656 : ℚ) : ℝ) ≤ ((14709436743 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_690.trans
      change ((3124303758599539 / 281474976710656 : ℚ) : ℝ) ≤ ((3124303758599539 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (691 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_691.trans
      change ((14344535173 / 281474976710656 : ℚ) : ℝ) ≤ ((14344535173 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_691.trans
      change ((3128812950216415 / 281474976710656 : ℚ) : ℝ) ≤ ((3128812950216415 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (692 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_692.trans
      change ((13988680783 / 281474976710656 : ℚ) : ℝ) ≤ ((13988680783 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_692.trans
      change ((783330524490777 / 70368744177664 : ℚ) : ℝ) ≤ ((3133322097963108 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (693 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_693.trans
      change ((852603087 / 17592186044416 : ℚ) : ℝ) ≤ ((13641649392 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_693.trans
      change ((3137831201874237 / 281474976710656 : ℚ) : ℝ) ≤ ((3137831201874237 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (694 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_694.trans
      change ((13303222371 / 281474976710656 : ℚ) : ℝ) ≤ ((13303222371 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_694.trans
      change ((1571170130992189 / 140737488355328 : ℚ) : ℝ) ≤ ((3142340261984378 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (695 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_695.trans
      change ((1621648313 / 35184372088832 : ℚ) : ℝ) ≤ ((12973186504 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_695.trans
      change ((3146849278328069 / 281474976710656 : ℚ) : ℝ) ≤ ((3146849278328069 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (696 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_696.trans
      change ((6325666929 / 140737488355328 : ℚ) : ℝ) ≤ ((12651333858 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_696.trans
      change ((3151358250939805 / 281474976710656 : ℚ) : ℝ) ≤ ((3151358250939805 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (697 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_697.trans
      change ((6168730823 / 140737488355328 : ℚ) : ℝ) ≤ ((12337461646 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_697.trans
      change ((3155867179854041 / 281474976710656 : ℚ) : ℝ) ≤ ((3155867179854041 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (698 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_698.trans
      change ((12031372107 / 281474976710656 : ℚ) : ℝ) ≤ ((12031372107 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_698.trans
      change ((3160376065105191 / 281474976710656 : ℚ) : ℝ) ≤ ((3160376065105191 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (699 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_699.trans
      change ((5866436187 / 140737488355328 : ℚ) : ℝ) ≤ ((11732872374 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_699.trans
      change ((1582442453363815 / 140737488355328 : ℚ) : ℝ) ≤ ((3164884906727630 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (700 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_700.trans
      change ((1430221795 / 35184372088832 : ℚ) : ℝ) ≤ ((11441774360 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_700.trans
      change ((3169393704755689 / 281474976710656 : ℚ) : ℝ) ≤ ((3169393704755689 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (701 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_701.trans
      change ((5578947317 / 140737488355328 : ℚ) : ℝ) ≤ ((11157894634 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_701.trans
      change ((1586951229611831 / 140737488355328 : ℚ) : ℝ) ≤ ((3173902459223662 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (702 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_702.trans
      change ((10881054309 / 281474976710656 : ℚ) : ℝ) ≤ ((10881054309 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_702.trans
      change ((3178411170165801 / 281474976710656 : ℚ) : ℝ) ≤ ((3178411170165801 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (703 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height021.height_factor_upper_703.trans
      change ((10611078929 / 281474976710656 : ℚ) : ℝ) ≤ ((10611078929 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height021.height_power_upper_703.trans
      change ((795729959404079 / 70368744177664 : ℚ) : ℝ) ≤ ((3182919837616316 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height021
