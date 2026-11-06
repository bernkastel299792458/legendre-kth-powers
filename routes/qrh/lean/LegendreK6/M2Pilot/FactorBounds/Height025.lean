import LegendreK6.M2Pilot.Enclosures.Height025
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height025
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 800 ≤ i.val) (hhi : i.val < 832) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (800 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_800.trans
      change ((926076157 / 281474976710656 : ℚ) : ℝ) ≤ ((926076157 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_800.trans
      change ((3620059077224839 / 281474976710656 : ℚ) : ℝ) ≤ ((3620059077224839 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (801 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_801.trans
      change ((225767397 / 70368744177664 : ℚ) : ℝ) ≤ ((903069588 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_801.trans
      change ((453070455272105 / 35184372088832 : ℚ) : ℝ) ≤ ((3624563642176840 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (802 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_802.trans
      change ((440317159 / 140737488355328 : ℚ) : ℝ) ≤ ((880634318 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_802.trans
      change ((1814534083417183 / 140737488355328 : ℚ) : ℝ) ≤ ((3629068166834366 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (803 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_803.trans
      change ((858756169 / 281474976710656 : ℚ) : ℝ) ≤ ((858756169 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_803.trans
      change ((908393162806973 / 70368744177664 : ℚ) : ℝ) ≤ ((3633572651227892 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (804 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_804.trans
      change ((418710657 / 140737488355328 : ℚ) : ℝ) ≤ ((837421314 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_804.trans
      change ((3638077095387857 / 281474976710656 : ℚ) : ℝ) ≤ ((3638077095387857 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (805 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_805.trans
      change ((816616269 / 281474976710656 : ℚ) : ℝ) ≤ ((816616269 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_805.trans
      change ((3642581499344667 / 281474976710656 : ℚ) : ℝ) ≤ ((3642581499344667 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (806 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_806.trans
      change ((796327883 / 281474976710656 : ℚ) : ℝ) ≤ ((796327883 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_806.trans
      change ((3647085863128691 / 281474976710656 : ℚ) : ℝ) ≤ ((3647085863128691 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (807 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_807.trans
      change ((776543333 / 281474976710656 : ℚ) : ℝ) ≤ ((776543333 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_807.trans
      change ((3651590186770267 / 281474976710656 : ℚ) : ℝ) ≤ ((3651590186770267 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (808 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_808.trans
      change ((757250113 / 281474976710656 : ℚ) : ℝ) ≤ ((757250113 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_808.trans
      change ((228505904393731 / 17592186044416 : ℚ) : ℝ) ≤ ((3656094470299696 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (809 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_809.trans
      change ((738436029 / 281474976710656 : ℚ) : ℝ) ≤ ((738436029 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_809.trans
      change ((1830299356873623 / 140737488355328 : ℚ) : ℝ) ≤ ((3660598713747246 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (810 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_810.trans
      change ((720089187 / 281474976710656 : ℚ) : ℝ) ≤ ((720089187 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_810.trans
      change ((1832551458571575 / 140737488355328 : ℚ) : ℝ) ≤ ((3665102917143150 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (811 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_811.trans
      change ((702197989 / 281474976710656 : ℚ) : ℝ) ≤ ((702197989 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_811.trans
      change ((3669607080517607 / 281474976710656 : ℚ) : ℝ) ≤ ((3669607080517607 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (812 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_812.trans
      change ((684751127 / 281474976710656 : ℚ) : ℝ) ≤ ((684751127 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_812.trans
      change ((1837055601950391 / 140737488355328 : ℚ) : ℝ) ≤ ((3674111203900782 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (813 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_813.trans
      change ((667737569 / 281474976710656 : ℚ) : ℝ) ≤ ((667737569 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_813.trans
      change ((3678615287322807 / 281474976710656 : ℚ) : ℝ) ≤ ((3678615287322807 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (814 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_814.trans
      change ((325573281 / 140737488355328 : ℚ) : ℝ) ≤ ((651146562 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_814.trans
      change ((1841559665406889 / 140737488355328 : ℚ) : ℝ) ≤ ((3683119330813778 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (815 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_815.trans
      change ((634967615 / 281474976710656 : ℚ) : ℝ) ≤ ((634967615 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_815.trans
      change ((3687623334403759 / 281474976710656 : ℚ) : ℝ) ≤ ((3687623334403759 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (816 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_816.trans
      change ((619190499 / 281474976710656 : ℚ) : ℝ) ≤ ((619190499 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_816.trans
      change ((3692127298122777 / 281474976710656 : ℚ) : ℝ) ≤ ((3692127298122777 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (817 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_817.trans
      change ((603805241 / 281474976710656 : ℚ) : ℝ) ≤ ((603805241 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_817.trans
      change ((924157805500207 / 70368744177664 : ℚ) : ℝ) ≤ ((3696631222000828 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (818 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_818.trans
      change ((9200033 / 4398046511104 : ℚ) : ℝ) ≤ ((588802112 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_818.trans
      change ((1850567553033937 / 140737488355328 : ℚ) : ℝ) ≤ ((3701135106067874 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (819 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_819.trans
      change ((287085813 / 140737488355328 : ℚ) : ℝ) ≤ ((574171626 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_819.trans
      change ((3705638950353841 / 281474976710656 : ℚ) : ℝ) ≤ ((3705638950353841 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (820 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_820.trans
      change ((559904533 / 281474976710656 : ℚ) : ℝ) ≤ ((559904533 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_820.trans
      change ((3710142754888625 / 281474976710656 : ℚ) : ℝ) ≤ ((3710142754888625 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (821 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_821.trans
      change ((136497953 / 70368744177664 : ℚ) : ℝ) ≤ ((545991812 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_821.trans
      change ((3714646519702083 / 281474976710656 : ℚ) : ℝ) ≤ ((3714646519702083 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (822 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_822.trans
      change ((66553083 / 35184372088832 : ℚ) : ℝ) ≤ ((532424664 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_822.trans
      change ((929787561206011 / 70368744177664 : ℚ) : ℝ) ≤ ((3719150244824044 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (823 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_823.trans
      change ((519194511 / 281474976710656 : ℚ) : ℝ) ≤ ((519194511 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_823.trans
      change ((930913482571075 / 70368744177664 : ℚ) : ℝ) ≤ ((3723653930284300 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (824 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_824.trans
      change ((253146493 / 140737488355328 : ℚ) : ℝ) ≤ ((506292986 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_824.trans
      change ((1864078788056305 / 140737488355328 : ℚ) : ℝ) ≤ ((3728157576112610 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (825 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_825.trans
      change ((123427983 / 70368744177664 : ℚ) : ℝ) ≤ ((493711932 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_825.trans
      change ((3732661182338699 / 281474976710656 : ℚ) : ℝ) ≤ ((3732661182338699 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (826 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_826.trans
      change ((481443391 / 281474976710656 : ℚ) : ℝ) ≤ ((481443391 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_826.trans
      change ((3737164748992261 / 281474976710656 : ℚ) : ℝ) ≤ ((3737164748992261 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (827 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_827.trans
      change ((469479605 / 281474976710656 : ℚ) : ℝ) ≤ ((469479605 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_827.trans
      change ((3741668276102955 / 281474976710656 : ℚ) : ℝ) ≤ ((3741668276102955 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (828 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_828.trans
      change ((28613313 / 17592186044416 : ℚ) : ℝ) ≤ ((457813008 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_828.trans
      change ((1873085881850203 / 140737488355328 : ℚ) : ℝ) ≤ ((3746171763700406 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (829 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_829.trans
      change ((111609055 / 70368744177664 : ℚ) : ℝ) ≤ ((446436220 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_829.trans
      change ((1875337605907103 / 140737488355328 : ℚ) : ℝ) ≤ ((3750675211814206 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (830 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_830.trans
      change ((435342047 / 281474976710656 : ℚ) : ℝ) ≤ ((435342047 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_830.trans
      change ((1877589310236957 / 140737488355328 : ℚ) : ℝ) ≤ ((3755178620473914 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (831 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height025.height_factor_upper_831.trans
      change ((26532717 / 17592186044416 : ℚ) : ℝ) ≤ ((424523472 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height025.height_power_upper_831.trans
      change ((3759681989709057 / 281474976710656 : ℚ) : ℝ) ≤ ((3759681989709057 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height025
