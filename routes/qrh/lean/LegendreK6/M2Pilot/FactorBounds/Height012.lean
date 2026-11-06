import LegendreK6.M2Pilot.Enclosures.Height012
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height012
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 384 ≤ i.val) (hhi : i.val < 416) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (384 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_384.trans
      change ((7866743809973 / 70368744177664 : ℚ) : ℝ) ≤ ((31466975239892 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_384.trans
      change ((54445207312675 / 8796093022208 : ℚ) : ℝ) ≤ ((1742246634005600 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (385 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_385.trans
      change ((15345123346571 / 140737488355328 : ℚ) : ℝ) ≤ ((30690246693142 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_385.trans
      change ((436692775224779 / 70368744177664 : ℚ) : ℝ) ≤ ((1746771100899116 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (386 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_386.trans
      change ((14966338387635 / 140737488355328 : ℚ) : ℝ) ≤ ((29932676775270 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_386.trans
      change ((1751295511038251 / 281474976710656 : ℚ) : ℝ) ≤ ((1751295511038251 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (387 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_387.trans
      change ((7298448320909 / 70368744177664 : ℚ) : ℝ) ≤ ((29193793283636 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_387.trans
      change ((877909932236969 / 140737488355328 : ℚ) : ℝ) ≤ ((1755819864473938 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (388 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_388.trans
      change ((28473135644761 / 281474976710656 : ℚ) : ℝ) ≤ ((28473135644761 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_388.trans
      change ((1760344161257045 / 281474976710656 : ℚ) : ℝ) ≤ ((1760344161257045 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (389 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_389.trans
      change ((27770254628169 / 281474976710656 : ℚ) : ℝ) ≤ ((27770254628169 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_389.trans
      change ((1764868401438369 / 281474976710656 : ℚ) : ℝ) ≤ ((1764868401438369 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (390 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_390.trans
      change ((27084712067257 / 281474976710656 : ℚ) : ℝ) ≤ ((27084712067257 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_390.trans
      change ((55293518283395 / 8796093022208 : ℚ) : ℝ) ≤ ((1769392585068640 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (391 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_391.trans
      change ((26416080587039 / 281474976710656 : ℚ) : ℝ) ≤ ((26416080587039 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_391.trans
      change ((1773916712198519 / 281474976710656 : ℚ) : ℝ) ≤ ((1773916712198519 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (392 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_392.trans
      change ((25763943338569 / 281474976710656 : ℚ) : ℝ) ≤ ((25763943338569 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_392.trans
      change ((889220391439301 / 140737488355328 : ℚ) : ℝ) ≤ ((1778440782878602 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (393 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_393.trans
      change ((6281973434977 / 70368744177664 : ℚ) : ℝ) ≤ ((25127893739908 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_393.trans
      change ((445741199289853 / 70368744177664 : ℚ) : ℝ) ≤ ((1782964797159412 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (394 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_394.trans
      change ((24507535223453 / 281474976710656 : ℚ) : ℝ) ≤ ((24507535223453 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_394.trans
      change ((111718047193213 / 17592186044416 : ℚ) : ℝ) ≤ ((1787488755091408 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (395 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_395.trans
      change ((23902480989479 / 281474976710656 : ℚ) : ℝ) ≤ ((23902480989479 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_395.trans
      change ((448003164181245 / 70368744177664 : ℚ) : ℝ) ≤ ((1792012656724980 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (396 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_396.trans
      change ((11656176882871 / 140737488355328 : ℚ) : ℝ) ≤ ((23312353765742 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_396.trans
      change ((1796536502110451 / 281474976710656 : ℚ) : ℝ) ≤ ((1796536502110451 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (397 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_397.trans
      change ((22736785572997 / 281474976710656 : ℚ) : ℝ) ≤ ((22736785572997 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_397.trans
      change ((450265072824519 / 70368744177664 : ℚ) : ℝ) ≤ ((1801060291298076 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (398 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_398.trans
      change ((11087708748137 / 140737488355328 : ℚ) : ℝ) ≤ ((22175417496274 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_398.trans
      change ((902792012169021 / 140737488355328 : ℚ) : ℝ) ≤ ((1805584024338042 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (399 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_399.trans
      change ((5406974865447 / 70368744177664 : ℚ) : ℝ) ≤ ((21627899461788 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_399.trans
      change ((1810107701280471 / 281474976710656 : ℚ) : ℝ) ≤ ((1810107701280471 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (400 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_400.trans
      change ((21093890019327 / 281474976710656 : ℚ) : ℝ) ≤ ((21093890019327 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_400.trans
      change ((226828915271927 / 35184372088832 : ℚ) : ℝ) ≤ ((1814631322175416 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (401 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_401.trans
      change ((1285816008125 / 17592186044416 : ℚ) : ℝ) ≤ ((20573056130000 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_401.trans
      change ((1819154887072863 / 281474976710656 : ℚ) : ℝ) ≤ ((1819154887072863 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (402 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_402.trans
      change ((10032536479597 / 140737488355328 : ℚ) : ℝ) ≤ ((20065072959194 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_402.trans
      change ((1823678396022733 / 281474976710656 : ℚ) : ℝ) ≤ ((1823678396022733 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (403 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_403.trans
      change ((2446202959329 / 35184372088832 : ℚ) : ℝ) ≤ ((19569623674632 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_403.trans
      change ((914100924537439 / 140737488355328 : ℚ) : ℝ) ≤ ((1828201849074878 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (404 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_404.trans
      change ((19086399249395 / 281474976710656 : ℚ) : ℝ) ≤ ((19086399249395 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_404.trans
      change ((1832725246279085 / 281474976710656 : ℚ) : ℝ) ≤ ((1832725246279085 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (405 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_405.trans
      change ((18615098269787 / 281474976710656 : ℚ) : ℝ) ≤ ((18615098269787 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_405.trans
      change ((918624293842537 / 140737488355328 : ℚ) : ℝ) ≤ ((1837248587685074 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (406 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_406.trans
      change ((9077713373963 / 140737488355328 : ℚ) : ℝ) ≤ ((18155426747926 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_406.trans
      change ((920885936671249 / 140737488355328 : ℚ) : ℝ) ≤ ((1841771873342498 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (407 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_407.trans
      change ((8853548969473 / 140737488355328 : ℚ) : ℝ) ≤ ((17707097938946 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_407.trans
      change ((115393443956309 / 17592186044416 : ℚ) : ℝ) ≤ ((1846295103300944 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (408 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_408.trans
      change ((8634916081347 / 140737488355328 : ℚ) : ℝ) ≤ ((17269832162694 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_408.trans
      change ((1850818277609935 / 281474976710656 : ℚ) : ℝ) ≤ ((1850818277609935 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (409 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_409.trans
      change ((16843356629811 / 281474976710656 : ℚ) : ℝ) ≤ ((16843356629811 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_409.trans
      change ((1855341396318925 / 281474976710656 : ℚ) : ℝ) ≤ ((1855341396318925 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (410 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_410.trans
      change ((8213702636047 / 140737488355328 : ℚ) : ℝ) ≤ ((16427405272094 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_410.trans
      change ((1859864459477303 / 281474976710656 : ℚ) : ℝ) ≤ ((1859864459477303 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (411 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_411.trans
      change ((8010859288515 / 140737488355328 : ℚ) : ℝ) ≤ ((16021718577030 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_411.trans
      change ((1864387467134393 / 281474976710656 : ℚ) : ℝ) ≤ ((1864387467134393 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (412 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_412.trans
      change ((15626043426399 / 281474976710656 : ℚ) : ℝ) ≤ ((15626043426399 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_412.trans
      change ((1868910419339453 / 281474976710656 : ℚ) : ℝ) ≤ ((1868910419339453 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (413 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_413.trans
      change ((15240132938843 / 281474976710656 : ℚ) : ℝ) ≤ ((15240132938843 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_413.trans
      change ((1873433316141675 / 281474976710656 : ℚ) : ℝ) ≤ ((1873433316141675 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (414 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_414.trans
      change ((7431873158161 / 140737488355328 : ℚ) : ℝ) ≤ ((14863746316322 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_414.trans
      change ((938978078795093 / 140737488355328 : ℚ) : ℝ) ≤ ((1877956157590186 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (415 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height012.height_factor_upper_415.trans
      change ((14496648694327 / 281474976710656 : ℚ) : ℝ) ≤ ((14496648694327 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height012.height_power_upper_415.trans
      change ((58827466991689 / 8796093022208 : ℚ) : ℝ) ≤ ((1882478943734048 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height012
