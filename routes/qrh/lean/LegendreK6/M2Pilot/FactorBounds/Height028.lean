import LegendreK6.M2Pilot.Enclosures.Height028
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height028
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 896 ≤ i.val) (hhi : i.val < 928) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (896 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_896.trans
      change ((82678443 / 281474976710656 : ℚ) : ℝ) ≤ ((82678443 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_896.trans
      change ((4052317812267235 / 281474976710656 : ℚ) : ℝ) ≤ ((4052317812267235 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (897 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_897.trans
      change ((40311723 / 140737488355328 : ℚ) : ℝ) ≤ ((80623446 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_897.trans
      change ((4056818643141983 / 281474976710656 : ℚ) : ℝ) ≤ ((4056818643141983 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (898 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_898.trans
      change ((78619543 / 281474976710656 : ℚ) : ℝ) ≤ ((78619543 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_898.trans
      change ((2030659718248671 / 140737488355328 : ℚ) : ℝ) ≤ ((4061319436497342 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (899 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_899.trans
      change ((9583183 / 35184372088832 : ℚ) : ℝ) ≤ ((76665464 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_899.trans
      change ((4065820192360693 / 281474976710656 : ℚ) : ℝ) ≤ ((4065820192360693 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (900 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_900.trans
      change ((74759971 / 281474976710656 : ℚ) : ℝ) ≤ ((74759971 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_900.trans
      change ((4070320910759389 / 281474976710656 : ℚ) : ℝ) ≤ ((4070320910759389 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (901 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_901.trans
      change ((72901855 / 281474976710656 : ℚ) : ℝ) ≤ ((72901855 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_901.trans
      change ((4074821591720749 / 281474976710656 : ℚ) : ℝ) ≤ ((4074821591720749 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (902 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_902.trans
      change ((71089941 / 281474976710656 : ℚ) : ℝ) ≤ ((71089941 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_902.trans
      change ((4079322235272067 / 281474976710656 : ℚ) : ℝ) ≤ ((4079322235272067 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (903 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_903.trans
      change ((8665385 / 35184372088832 : ℚ) : ℝ) ≤ ((69323080 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_903.trans
      change ((1020955710360151 / 70368744177664 : ℚ) : ℝ) ≤ ((4083822841440604 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (904 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_904.trans
      change ((67600151 / 281474976710656 : ℚ) : ℝ) ≤ ((67600151 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_904.trans
      change ((511040426281699 / 35184372088832 : ℚ) : ℝ) ≤ ((4088323410253592 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (905 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_905.trans
      change ((1030001 / 4398046511104 : ℚ) : ℝ) ≤ ((65920064 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_905.trans
      change ((2046411970869117 / 140737488355328 : ℚ) : ℝ) ≤ ((4092823941738234 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (906 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_906.trans
      change ((8035219 / 35184372088832 : ℚ) : ℝ) ≤ ((64281752 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_906.trans
      change ((4097324435921701 / 281474976710656 : ℚ) : ℝ) ≤ ((4097324435921701 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (907 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_907.trans
      change ((62684179 / 281474976710656 : ℚ) : ℝ) ≤ ((62684179 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_907.trans
      change ((4101824892831137 / 281474976710656 : ℚ) : ℝ) ≤ ((4101824892831137 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (908 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_908.trans
      change ((15281583 / 70368744177664 : ℚ) : ℝ) ≤ ((61126332 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_908.trans
      change ((4106325312493655 / 281474976710656 : ℚ) : ℝ) ≤ ((4106325312493655 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (909 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_909.trans
      change ((59607223 / 281474976710656 : ℚ) : ℝ) ≤ ((59607223 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_909.trans
      change ((4110825694936339 / 281474976710656 : ℚ) : ℝ) ≤ ((4110825694936339 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (910 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_910.trans
      change ((58125889 / 281474976710656 : ℚ) : ℝ) ≤ ((58125889 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_910.trans
      change ((1028831510046561 / 70368744177664 : ℚ) : ℝ) ≤ ((4115326040186244 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (911 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_911.trans
      change ((3542587 / 17592186044416 : ℚ) : ℝ) ≤ ((56681392 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_911.trans
      change ((4119826348270393 / 281474976710656 : ℚ) : ℝ) ≤ ((4119826348270393 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (912 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_912.trans
      change ((3454551 / 17592186044416 : ℚ) : ℝ) ≤ ((55272816 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_912.trans
      change ((2062163309607891 / 140737488355328 : ℚ) : ℝ) ≤ ((4124326619215782 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (913 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_913.trans
      change ((13474817 / 70368744177664 : ℚ) : ℝ) ≤ ((53899268 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_913.trans
      change ((4128826853049377 / 281474976710656 : ℚ) : ℝ) ≤ ((4128826853049377 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (914 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_914.trans
      change ((26279939 / 140737488355328 : ℚ) : ℝ) ≤ ((52559878 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_914.trans
      change ((4133327049798115 / 281474976710656 : ℚ) : ℝ) ≤ ((4133327049798115 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (915 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_915.trans
      change ((12813449 / 70368744177664 : ℚ) : ℝ) ≤ ((51253796 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_915.trans
      change ((4137827209488903 / 281474976710656 : ℚ) : ℝ) ≤ ((4137827209488903 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (916 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_916.trans
      change ((49980195 / 281474976710656 : ℚ) : ℝ) ≤ ((49980195 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_916.trans
      change ((2071163666074309 / 140737488355328 : ℚ) : ℝ) ≤ ((4142327332148618 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (917 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_917.trans
      change ((24369133 / 140737488355328 : ℚ) : ℝ) ≤ ((48738266 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_917.trans
      change ((4146827417804109 / 281474976710656 : ℚ) : ℝ) ≤ ((4146827417804109 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (918 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_918.trans
      change ((5940903 / 35184372088832 : ℚ) : ℝ) ≤ ((47527224 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_918.trans
      change ((4151327466482197 / 281474976710656 : ℚ) : ℝ) ≤ ((4151327466482197 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (919 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_919.trans
      change ((11586575 / 70368744177664 : ℚ) : ℝ) ≤ ((46346300 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_919.trans
      change ((4155827478209671 / 281474976710656 : ℚ) : ℝ) ≤ ((4155827478209671 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (920 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_920.trans
      change ((45194745 / 281474976710656 : ℚ) : ℝ) ≤ ((45194745 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_920.trans
      change ((1040081863253323 / 70368744177664 : ℚ) : ℝ) ≤ ((4160327453013292 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (921 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_921.trans
      change ((22035915 / 140737488355328 : ℚ) : ℝ) ≤ ((44071830 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_921.trans
      change ((4164827390919793 / 281474976710656 : ℚ) : ℝ) ≤ ((4164827390919793 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (922 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_922.trans
      change ((42976843 / 281474976710656 : ℚ) : ℝ) ≤ ((42976843 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_922.trans
      change ((4169327291955877 / 281474976710656 : ℚ) : ℝ) ≤ ((4169327291955877 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (923 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_923.trans
      change ((1309659 / 8796093022208 : ℚ) : ℝ) ≤ ((41909088 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_923.trans
      change ((2086913578074109 / 140737488355328 : ℚ) : ℝ) ≤ ((4173827156148218 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (924 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_924.trans
      change ((20433945 / 140737488355328 : ℚ) : ℝ) ≤ ((40867890 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_924.trans
      change ((2089163491761731 / 140737488355328 : ℚ) : ℝ) ≤ ((4178326983523462 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (925 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_925.trans
      change ((9963147 / 70368744177664 : ℚ) : ℝ) ≤ ((39852588 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_925.trans
      change ((65356668345441 / 4398046511104 : ℚ) : ℝ) ≤ ((4182826774108224 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (926 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_926.trans
      change ((38862539 / 281474976710656 : ℚ) : ℝ) ≤ ((38862539 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_926.trans
      change ((1046831631982273 / 70368744177664 : ℚ) : ℝ) ≤ ((4187326527929092 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (927 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height028.height_factor_upper_927.trans
      change ((18948557 / 140737488355328 : ℚ) : ℝ) ≤ ((37897114 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height028.height_power_upper_927.trans
      change ((2095913122506313 / 140737488355328 : ℚ) : ℝ) ≤ ((4191826245012626 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height028
