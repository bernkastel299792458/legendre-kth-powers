import LegendreK6.M2Pilot.Enclosures.Height011
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height011
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 352 ≤ i.val) (hhi : i.val < 384) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (352 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_352.trans
      change ((17499829701175 / 70368744177664 : ℚ) : ℝ) ≤ ((69999318804700 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_352.trans
      change ((1597433418668185 / 281474976710656 : ℚ) : ℝ) ≤ ((1597433418668185 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (353 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_353.trans
      change ((34136251985765 / 140737488355328 : ℚ) : ℝ) ≤ ((68272503971530 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_353.trans
      change ((800979864506159 / 140737488355328 : ℚ) : ℝ) ≤ ((1601959729012318 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (354 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_354.trans
      change ((66588255725713 / 281474976710656 : ℚ) : ℝ) ≤ ((66588255725713 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_354.trans
      change ((200810747616901 / 35184372088832 : ℚ) : ℝ) ≤ ((1606485980935208 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (355 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_355.trans
      change ((32472762805429 / 140737488355328 : ℚ) : ℝ) ≤ ((64945525610858 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_355.trans
      change ((1611012174490051 / 281474976710656 : ℚ) : ℝ) ≤ ((1611012174490051 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (356 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_356.trans
      change ((31671645486987 / 140737488355328 : ℚ) : ℝ) ≤ ((63343290973974 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_356.trans
      change ((1615538309729969 / 281474976710656 : ℚ) : ℝ) ≤ ((1615538309729969 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (357 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_357.trans
      change ((61780554330975 / 281474976710656 : ℚ) : ℝ) ≤ ((61780554330975 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_357.trans
      change ((1620064386708011 / 281474976710656 : ℚ) : ℝ) ≤ ((1620064386708011 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (358 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_358.trans
      change ((30128171373877 / 140737488355328 : ℚ) : ℝ) ≤ ((60256342747754 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_358.trans
      change ((1624590405477155 / 281474976710656 : ℚ) : ℝ) ≤ ((1624590405477155 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (359 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_359.trans
      change ((58769707236481 / 281474976710656 : ℚ) : ℝ) ≤ ((58769707236481 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_359.trans
      change ((814558183045153 / 140737488355328 : ℚ) : ℝ) ≤ ((1629116366090306 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (360 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_360.trans
      change ((28659861083361 / 140737488355328 : ℚ) : ℝ) ≤ ((57319722166722 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_360.trans
      change ((1633642268600297 / 281474976710656 : ℚ) : ℝ) ≤ ((1633642268600297 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (361 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_361.trans
      change ((55905484691035 / 281474976710656 : ℚ) : ℝ) ≤ ((55905484691035 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_361.trans
      change ((819084056529945 / 140737488355328 : ℚ) : ℝ) ≤ ((1638168113059890 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (362 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_362.trans
      change ((54526114184669 / 281474976710656 : ℚ) : ℝ) ≤ ((54526114184669 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_362.trans
      change ((1642693899521773 / 281474976710656 : ℚ) : ℝ) ≤ ((1642693899521773 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (363 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_363.trans
      change ((53180751699043 / 281474976710656 : ℚ) : ℝ) ≤ ((53180751699043 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_363.trans
      change ((411804907009641 / 70368744177664 : ℚ) : ℝ) ≤ ((1647219628038564 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (364 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_364.trans
      change ((25934279714321 / 140737488355328 : ℚ) : ℝ) ≤ ((51868559428642 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_364.trans
      change ((1651745298662809 / 281474976710656 : ℚ) : ℝ) ≤ ((1651745298662809 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (365 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_365.trans
      change ((50588720191023 / 281474976710656 : ℚ) : ℝ) ≤ ((50588720191023 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_365.trans
      change ((1656270911446983 / 281474976710656 : ℚ) : ℝ) ≤ ((1656270911446983 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (366 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_366.trans
      change ((12335109229897 / 70368744177664 : ℚ) : ℝ) ≤ ((49340436919588 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_366.trans
      change ((1660796466443489 / 281474976710656 : ℚ) : ℝ) ≤ ((1660796466443489 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (367 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_367.trans
      change ((24061466084415 / 140737488355328 : ℚ) : ℝ) ≤ ((48122932168830 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_367.trans
      change ((832660981852329 / 140737488355328 : ℚ) : ℝ) ≤ ((1665321963704658 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (368 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_368.trans
      change ((23467723815867 / 140737488355328 : ℚ) : ℝ) ≤ ((46935447631734 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_368.trans
      change ((1669847403282753 / 281474976710656 : ℚ) : ℝ) ≤ ((1669847403282753 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (369 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_369.trans
      change ((11444310917259 / 70368744177664 : ℚ) : ℝ) ≤ ((45777243669036 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_369.trans
      change ((837186392614981 / 140737488355328 : ℚ) : ℝ) ≤ ((1674372785229962 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (370 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_370.trans
      change ((11161899712513 / 70368744177664 : ℚ) : ℝ) ≤ ((44647598850052 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_370.trans
      change ((839449054799203 / 140737488355328 : ℚ) : ℝ) ≤ ((1678898109598406 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (371 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_371.trans
      change ((43545809504793 / 281474976710656 : ℚ) : ℝ) ≤ ((43545809504793 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_371.trans
      change ((420855844110033 / 70368744177664 : ℚ) : ℝ) ≤ ((1683423376440132 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (372 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_372.trans
      change ((42471189287081 / 281474976710656 : ℚ) : ℝ) ≤ ((42471189287081 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_372.trans
      change ((105496786612945 / 17592186044416 : ℚ) : ℝ) ≤ ((1687948585807120 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (373 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_373.trans
      change ((20711534374207 / 140737488355328 : ℚ) : ℝ) ≤ ((41423068748414 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_373.trans
      change ((423118434437819 / 70368744177664 : ℚ) : ℝ) ≤ ((1692473737751276 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (374 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_374.trans
      change ((20200397461145 / 140737488355328 : ℚ) : ℝ) ≤ ((40400794922290 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_374.trans
      change ((848499416162219 / 140737488355328 : ℚ) : ℝ) ≤ ((1696998832324438 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (375 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_375.trans
      change ((9850932729689 / 70368744177664 : ℚ) : ℝ) ≤ ((39403730918756 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_375.trans
      change ((1701523869578373 / 281474976710656 : ℚ) : ℝ) ≤ ((1701523869578373 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (376 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_376.trans
      change ((9607813882231 / 70368744177664 : ℚ) : ℝ) ≤ ((38431255528924 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_376.trans
      change ((853024424782389 / 140737488355328 : ℚ) : ℝ) ≤ ((1706048849564778 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (377 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_377.trans
      change ((1171336338725 / 8796093022208 : ℚ) : ℝ) ≤ ((37482762839200 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_377.trans
      change ((1710573772335281 / 281474976710656 : ℚ) : ℝ) ≤ ((1710573772335281 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (378 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_378.trans
      change ((18278830927501 / 140737488355328 : ℚ) : ℝ) ≤ ((36557661855002 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_378.trans
      change ((1715098637941439 / 281474976710656 : ℚ) : ℝ) ≤ ((1715098637941439 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (379 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_379.trans
      change ((35655376133723 / 281474976710656 : ℚ) : ℝ) ≤ ((35655376133723 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_379.trans
      change ((429905861608685 / 70368744177664 : ℚ) : ℝ) ≤ ((1719623446434740 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (380 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_380.trans
      change ((34775343426717 / 281474976710656 : ℚ) : ℝ) ≤ ((34775343426717 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_380.trans
      change ((862074098933301 / 140737488355328 : ℚ) : ℝ) ≤ ((1724148197866602 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (381 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_381.trans
      change ((33917015330087 / 281474976710656 : ℚ) : ℝ) ≤ ((33917015330087 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_381.trans
      change ((864336446144187 / 140737488355328 : ℚ) : ℝ) ≤ ((1728672892288374 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (382 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_382.trans
      change ((33079856944053 / 281474976710656 : ℚ) : ℝ) ≤ ((33079856944053 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_382.trans
      change ((1733197529751335 / 281474976710656 : ℚ) : ℝ) ≤ ((1733197529751335 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (383 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height011.height_factor_upper_383.trans
      change ((32263346540701 / 281474976710656 : ℚ) : ℝ) ≤ ((32263346540701 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height011.height_power_upper_383.trans
      change ((1737722110306697 / 281474976710656 : ℚ) : ℝ) ≤ ((1737722110306697 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height011
