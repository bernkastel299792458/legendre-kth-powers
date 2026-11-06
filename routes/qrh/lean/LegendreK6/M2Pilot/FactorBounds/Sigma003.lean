import LegendreK6.M2Pilot.Enclosures.Sigma003
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Sigma003
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 1536) (hlo : 384 ≤ i.val) (hhi : i.val < 512) :
    sigmaFactor i ≤ sigmaDyadicFactor i ∧ sigmaPower i ≤ sigmaDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (384 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_384.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_384.trans
      change ((150119987579017 / 281474976710656 : ℚ) : ℝ) ≤ ((150119987579017 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (385 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_385.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_385.trans
      change ((150015719485543 / 281474976710656 : ℚ) : ℝ) ≤ ((150015719485543 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (386 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_386.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_386.trans
      change ((149911415175295 / 281474976710656 : ℚ) : ℝ) ≤ ((149911415175295 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (387 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_387.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_387.trans
      change ((149807074629399 / 281474976710656 : ℚ) : ℝ) ≤ ((149807074629399 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (388 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_388.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_388.trans
      change ((149702697828971 / 281474976710656 : ℚ) : ℝ) ≤ ((149702697828971 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (389 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_389.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_389.trans
      change ((149598284755111 / 281474976710656 : ℚ) : ℝ) ≤ ((149598284755111 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (390 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_390.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_390.trans
      change ((74746917694453 / 140737488355328 : ℚ) : ℝ) ≤ ((149493835388906 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (391 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_391.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_391.trans
      change ((149389349711433 / 281474976710656 : ℚ) : ℝ) ≤ ((149389349711433 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (392 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_392.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_392.trans
      change ((149284827703751 / 281474976710656 : ℚ) : ℝ) ≤ ((149284827703751 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (393 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_393.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_393.trans
      change ((149180269346911 / 281474976710656 : ℚ) : ℝ) ≤ ((149180269346911 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (394 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_394.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_394.trans
      change ((74537837310973 / 140737488355328 : ℚ) : ℝ) ≤ ((149075674621946 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (395 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_395.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_395.trans
      change ((148971043509879 / 281474976710656 : ℚ) : ℝ) ≤ ((148971043509879 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (396 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_396.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_396.trans
      change ((74433187995859 / 140737488355328 : ℚ) : ℝ) ≤ ((148866375991718 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (397 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_397.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_397.trans
      change ((37190418012115 / 70368744177664 : ℚ) : ℝ) ≤ ((148761672048460 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (398 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_398.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_398.trans
      change ((148656931661087 / 281474976710656 : ℚ) : ℝ) ≤ ((148656931661087 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (399 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_399.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_399.trans
      change ((18569019351321 / 35184372088832 : ℚ) : ℝ) ≤ ((148552154810568 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (400 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_400.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_400.trans
      change ((74223670738929 / 140737488355328 : ℚ) : ℝ) ≤ ((148447341477858 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (401 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_401.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_401.trans
      change ((148342491643901 / 281474976710656 : ℚ) : ℝ) ≤ ((148342491643901 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (402 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_402.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_402.trans
      change ((148237605289625 / 281474976710656 : ℚ) : ℝ) ≤ ((148237605289625 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (403 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_403.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_403.trans
      change ((148132682395947 / 281474976710656 : ℚ) : ℝ) ≤ ((148132682395947 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (404 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_404.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_404.trans
      change ((148027722943769 / 281474976710656 : ℚ) : ℝ) ≤ ((148027722943769 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (405 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_405.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_405.trans
      change ((73961363456991 / 140737488355328 : ℚ) : ℝ) ≤ ((147922726913982 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (406 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_406.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_406.trans
      change ((36954423571865 / 70368744177664 : ℚ) : ℝ) ≤ ((147817694287460 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (407 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_407.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_407.trans
      change ((147712625045067 / 281474976710656 : ℚ) : ℝ) ≤ ((147712625045067 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (408 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_408.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_408.trans
      change ((147607519167653 / 281474976710656 : ℚ) : ℝ) ≤ ((147607519167653 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (409 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_409.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_409.trans
      change ((36875594159013 / 70368744177664 : ℚ) : ℝ) ≤ ((147502376636052 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (410 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_410.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_410.trans
      change ((147397197431089 / 281474976710656 : ℚ) : ℝ) ≤ ((147397197431089 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (411 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_411.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_411.trans
      change ((36822995383393 / 70368744177664 : ℚ) : ℝ) ≤ ((147291981533572 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (412 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_412.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_412.trans
      change ((73593364462149 / 140737488355328 : ℚ) : ℝ) ≤ ((147186728924298 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (413 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_413.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_413.trans
      change ((9192589974003 / 17592186044416 : ℚ) : ℝ) ≤ ((147081439584048 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (414 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_414.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_414.trans
      change ((146976113493593 / 281474976710656 : ℚ) : ℝ) ≤ ((146976113493593 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (415 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_415.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_415.trans
      change ((146870750633687 / 281474976710656 : ℚ) : ℝ) ≤ ((146870750633687 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (416 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_416.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_416.trans
      change ((146765350985073 / 281474976710656 : ℚ) : ℝ) ≤ ((146765350985073 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (417 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_417.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_417.trans
      change ((146659914528479 / 281474976710656 : ℚ) : ℝ) ≤ ((146659914528479 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (418 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_418.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_418.trans
      change ((73277220622311 / 140737488355328 : ℚ) : ℝ) ≤ ((146554441244622 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (419 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_419.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_419.trans
      change ((146448931114203 / 281474976710656 : ℚ) : ℝ) ≤ ((146448931114203 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (420 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_420.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_420.trans
      change ((73171692058955 / 140737488355328 : ℚ) : ℝ) ≤ ((146343384117910 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (421 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_421.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_421.trans
      change ((73118900118209 / 140737488355328 : ℚ) : ℝ) ≤ ((146237800236418 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (422 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_422.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_422.trans
      change ((146132179450389 / 281474976710656 : ℚ) : ℝ) ≤ ((146132179450389 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (423 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_423.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_423.trans
      change ((73013260870235 / 140737488355328 : ℚ) : ℝ) ≤ ((146026521740470 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (424 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_424.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_424.trans
      change ((2280012923239 / 4398046511104 : ℚ) : ℝ) ≤ ((145920827087296 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (425 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_425.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_425.trans
      change ((1139180433371 / 2199023255552 : ℚ) : ℝ) ≤ ((145815095471488 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (426 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_426.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_426.trans
      change ((36427331718413 / 70368744177664 : ℚ) : ℝ) ≤ ((145709326873652 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (427 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_427.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_427.trans
      change ((145603521274383 / 281474976710656 : ℚ) : ℝ) ≤ ((145603521274383 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (428 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_428.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_428.trans
      change ((145497678654261 / 281474976710656 : ℚ) : ℝ) ≤ ((145497678654261 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (429 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_429.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_429.trans
      change ((145391798993851 / 281474976710656 : ℚ) : ℝ) ≤ ((145391798993851 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (430 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_430.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_430.trans
      change ((145285882273707 / 281474976710656 : ℚ) : ℝ) ≤ ((145285882273707 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (431 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_431.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_431.trans
      change ((145179928474369 / 281474976710656 : ℚ) : ℝ) ≤ ((145179928474369 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (432 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_432.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_432.trans
      change ((145073937576361 / 281474976710656 : ℚ) : ℝ) ≤ ((145073937576361 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (433 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_433.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_433.trans
      change ((36241977390049 / 70368744177664 : ℚ) : ℝ) ≤ ((144967909560196 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (434 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_434.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_434.trans
      change ((36215461101593 / 70368744177664 : ℚ) : ℝ) ≤ ((144861844406372 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (435 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_435.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_435.trans
      change ((72377871047687 / 140737488355328 : ℚ) : ℝ) ≤ ((144755742095374 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (436 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_436.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_436.trans
      change ((18081200325959 / 35184372088832 : ℚ) : ℝ) ≤ ((144649602607672 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (437 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_437.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_437.trans
      change ((144543425923725 / 281474976710656 : ℚ) : ℝ) ≤ ((144543425923725 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (438 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_438.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_438.trans
      change ((144437212023975 / 281474976710656 : ℚ) : ℝ) ≤ ((144437212023975 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (439 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_439.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_439.trans
      change ((144330960888853 / 281474976710656 : ℚ) : ℝ) ≤ ((144330960888853 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (440 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_440.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_440.trans
      change ((144224672498775 / 281474976710656 : ℚ) : ℝ) ≤ ((144224672498775 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (441 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_441.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_441.trans
      change ((144118346834143 / 281474976710656 : ℚ) : ℝ) ≤ ((144118346834143 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (442 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_442.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_442.trans
      change ((72005991937673 / 140737488355328 : ℚ) : ℝ) ≤ ((144011983875346 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (443 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_443.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_443.trans
      change ((143905583602759 / 281474976710656 : ℚ) : ℝ) ≤ ((143905583602759 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (444 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_444.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_444.trans
      change ((143799145996743 / 281474976710656 : ℚ) : ℝ) ≤ ((143799145996743 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (445 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_445.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_445.trans
      change ((143692671037645 / 281474976710656 : ℚ) : ℝ) ≤ ((143692671037645 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (446 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_446.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_446.trans
      change ((143586158705799 / 281474976710656 : ℚ) : ℝ) ≤ ((143586158705799 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (447 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_447.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_447.trans
      change ((143479608981525 / 281474976710656 : ℚ) : ℝ) ≤ ((143479608981525 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (448 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_448.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_448.trans
      change ((143373021845129 / 281474976710656 : ℚ) : ℝ) ≤ ((143373021845129 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (449 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_449.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_449.trans
      change ((71633198638451 / 140737488355328 : ℚ) : ℝ) ≤ ((143266397276902 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (450 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_450.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_450.trans
      change ((35789933814281 / 70368744177664 : ℚ) : ℝ) ≤ ((143159735257124 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (451 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_451.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_451.trans
      change ((71526517883029 / 140737488355328 : ℚ) : ℝ) ≤ ((143053035766058 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (452 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_452.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_452.trans
      change ((142946298783955 / 281474976710656 : ℚ) : ℝ) ≤ ((142946298783955 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (453 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_453.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_453.trans
      change ((35709881072763 / 70368744177664 : ℚ) : ℝ) ≤ ((142839524291052 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (454 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_454.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_454.trans
      change ((35683178066893 / 70368744177664 : ℚ) : ℝ) ≤ ((142732712267572 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (455 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_455.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_455.trans
      change ((71312931346861 / 140737488355328 : ℚ) : ℝ) ≤ ((142625862693722 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (456 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_456.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_456.trans
      change ((35629743887425 / 70368744177664 : ℚ) : ℝ) ≤ ((142518975549700 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (457 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_457.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_457.trans
      change ((35603012703921 / 70368744177664 : ℚ) : ℝ) ≤ ((142412050815684 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (458 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_458.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_458.trans
      change ((142305088471843 / 281474976710656 : ℚ) : ℝ) ≤ ((142305088471843 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (459 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_459.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_459.trans
      change ((71099044249165 / 140737488355328 : ℚ) : ℝ) ≤ ((142198088498330 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (460 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_460.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_460.trans
      change ((35522762718821 / 70368744177664 : ℚ) : ℝ) ≤ ((142091050875284 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (461 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_461.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_461.trans
      change ((141983975582829 / 281474976710656 : ℚ) : ℝ) ≤ ((141983975582829 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (462 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_462.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_462.trans
      change ((141876862601077 / 281474976710656 : ℚ) : ℝ) ≤ ((141876862601077 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (463 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_463.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_463.trans
      change ((70884855955063 / 140737488355328 : ℚ) : ℝ) ≤ ((141769711910126 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (464 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_464.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_464.trans
      change ((70831261745029 / 140737488355328 : ℚ) : ℝ) ≤ ((141662523490058 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (465 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_465.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_465.trans
      change ((141555297320943 / 281474976710656 : ℚ) : ℝ) ≤ ((141555297320943 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (466 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_466.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_466.trans
      change ((35362008345709 / 70368744177664 : ℚ) : ℝ) ≤ ((141448033382836 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (467 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_467.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_467.trans
      change ((141340731655777 / 281474976710656 : ℚ) : ℝ) ≤ ((141340731655777 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (468 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_468.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_468.trans
      change ((70616696059897 / 140737488355328 : ℚ) : ℝ) ≤ ((141233392119794 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (469 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_469.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_469.trans
      change ((35281503688725 / 70368744177664 : ℚ) : ℝ) ≤ ((141126014754900 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (470 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_470.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_470.trans
      change ((141018599541093 / 281474976710656 : ℚ) : ℝ) ≤ ((141018599541093 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (471 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_471.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_471.trans
      change ((70455573229179 / 140737488355328 : ℚ) : ℝ) ≤ ((140911146458358 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (472 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_472.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_472.trans
      change ((70401827743333 / 140737488355328 : ℚ) : ℝ) ≤ ((140803655486666 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (473 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_473.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_473.trans
      change ((140696126605973 / 281474976710656 : ℚ) : ℝ) ≤ ((140696126605973 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (474 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_474.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_474.trans
      change ((70294279898111 / 140737488355328 : ℚ) : ℝ) ≤ ((140588559796222 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (475 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_475.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_475.trans
      change ((140480955037341 / 281474976710656 : ℚ) : ℝ) ≤ ((140480955037341 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (476 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_476.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_476.trans
      change ((140373312309243 / 281474976710656 : ℚ) : ℝ) ≤ ((140373312309243 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (477 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_477.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_477.trans
      change ((140265631591829 / 281474976710656 : ℚ) : ℝ) ≤ ((140265631591829 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (478 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_478.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_478.trans
      change ((17519739108123 / 35184372088832 : ℚ) : ℝ) ≤ ((140157912864984 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (479 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_479.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_479.trans
      change ((35012539027145 / 70368744177664 : ℚ) : ℝ) ≤ ((140050156108580 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (480 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_480.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_480.trans
      change ((69971180651237 / 140737488355328 : ℚ) : ℝ) ≤ ((139942361302474 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (481 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_481.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_481.trans
      change ((34958632106627 / 70368744177664 : ℚ) : ℝ) ≤ ((139834528426508 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (482 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_482.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_482.trans
      change ((4366458045641 / 8796093022208 : ℚ) : ℝ) ≤ ((139726657460512 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (483 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_483.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_483.trans
      change ((34904687096075 / 70368744177664 : ℚ) : ℝ) ≤ ((139618748384300 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (484 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_484.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_484.trans
      change ((139510801177673 / 281474976710656 : ℚ) : ℝ) ≤ ((139510801177673 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (485 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_485.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_485.trans
      change ((1089084498597 / 2199023255552 : ℚ) : ℝ) ≤ ((139402815820416 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (486 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_486.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_486.trans
      change ((139294792292301 / 281474976710656 : ℚ) : ℝ) ≤ ((139294792292301 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (487 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_487.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_487.trans
      change ((139186730573085 / 281474976710656 : ℚ) : ℝ) ≤ ((139186730573085 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (488 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_488.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_488.trans
      change ((8692414415157 / 17592186044416 : ℚ) : ℝ) ≤ ((139078630642512 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (489 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_489.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_489.trans
      change ((69485246240155 / 140737488355328 : ℚ) : ℝ) ≤ ((138970492480310 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (490 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_490.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_490.trans
      change ((69431158033097 / 140737488355328 : ℚ) : ℝ) ≤ ((138862316066194 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (491 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_491.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_491.trans
      change ((138754101379863 / 281474976710656 : ℚ) : ℝ) ≤ ((138754101379863 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (492 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_492.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_492.trans
      change ((138645848401003 / 281474976710656 : ℚ) : ℝ) ≤ ((138645848401003 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (493 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_493.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_493.trans
      change ((69268778554643 / 140737488355328 : ℚ) : ℝ) ≤ ((138537557109286 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (494 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_494.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_494.trans
      change ((8651826717773 / 17592186044416 : ℚ) : ℝ) ≤ ((138429227484368 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (495 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_495.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_495.trans
      change ((34580214876473 / 70368744177664 : ℚ) : ℝ) ≤ ((138320859505892 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (496 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_496.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_496.trans
      change ((69106226576743 / 140737488355328 : ℚ) : ℝ) ≤ ((138212453153486 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (497 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_497.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_497.trans
      change ((34526002101691 / 70368744177664 : ℚ) : ℝ) ≤ ((138104008406764 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (498 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_498.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_498.trans
      change ((34498881311331 / 70368744177664 : ℚ) : ℝ) ≤ ((137995525245324 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (499 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_499.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_499.trans
      change ((8617937728047 / 17592186044416 : ℚ) : ℝ) ≤ ((137887003648752 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (500 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_500.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_500.trans
      change ((137778443596617 / 281474976710656 : ℚ) : ℝ) ≤ ((137778443596617 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (501 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_501.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_501.trans
      change ((137669845068477 / 281474976710656 : ℚ) : ℝ) ≤ ((137669845068477 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (502 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_502.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_502.trans
      change ((137561208043871 / 281474976710656 : ℚ) : ℝ) ≤ ((137561208043871 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (503 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_503.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_503.trans
      change ((68726266251163 / 140737488355328 : ℚ) : ℝ) ≤ ((137452532502326 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (504 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_504.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_504.trans
      change ((34335954605839 / 70368744177664 : ℚ) : ℝ) ≤ ((137343818423356 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (505 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_505.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_505.trans
      change ((137235065786457 / 281474976710656 : ℚ) : ℝ) ≤ ((137235065786457 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (506 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_506.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_506.trans
      change ((68563137285557 / 140737488355328 : ℚ) : ℝ) ≤ ((137126274571114 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (507 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_507.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_507.trans
      change ((137017444756793 / 281474976710656 : ℚ) : ℝ) ≤ ((137017444756793 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (508 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_508.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_508.trans
      change ((68454288161475 / 140737488355328 : ℚ) : ℝ) ≤ ((136908576322950 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (509 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_509.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_509.trans
      change ((133593427001 / 274877906944 : ℚ) : ℝ) ≤ ((136799669249024 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (510 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_510.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_510.trans
      change ((17086340439305 / 35184372088832 : ℚ) : ℝ) ≤ ((136690723514440 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (511 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_511.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_511.trans
      change ((136581739098609 / 281474976710656 : ℚ) : ℝ) ≤ ((136581739098609 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Sigma003
