import LegendreK6.M2Pilot.Enclosures.Sigma004
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Sigma004
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 1536) (hlo : 512 ≤ i.val) (hhi : i.val < 640) :
    sigmaFactor i ≤ sigmaDyadicFactor i ∧ sigmaPower i ≤ sigmaDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (512 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_512.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_512.trans
      change ((136472715980925 / 281474976710656 : ℚ) : ℝ) ≤ ((136472715980925 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (513 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_513.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_513.trans
      change ((136363654140769 / 281474976710656 : ℚ) : ℝ) ≤ ((136363654140769 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (514 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_514.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_514.trans
      change ((136254553557509 / 281474976710656 : ℚ) : ℝ) ≤ ((136254553557509 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (515 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_515.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_515.trans
      change ((2127272097039 / 4398046511104 : ℚ) : ℝ) ≤ ((136145414210496 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (516 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_516.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_516.trans
      change ((136036236079067 / 281474976710656 : ℚ) : ℝ) ≤ ((136036236079067 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (517 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_517.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_517.trans
      change ((135927019142543 / 281474976710656 : ℚ) : ℝ) ≤ ((135927019142543 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (518 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_518.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_518.trans
      change ((67908881690117 / 140737488355328 : ℚ) : ℝ) ≤ ((135817763380234 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (519 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_519.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_519.trans
      change ((135708468771431 / 281474976710656 : ℚ) : ℝ) ≤ ((135708468771431 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (520 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_520.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_520.trans
      change ((67799567647707 / 140737488355328 : ℚ) : ℝ) ≤ ((135599135295414 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (521 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_521.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_521.trans
      change ((33872440732861 / 70368744177664 : ℚ) : ℝ) ≤ ((135489762931444 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (522 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_522.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_522.trans
      change ((33845087914693 / 70368744177664 : ℚ) : ℝ) ≤ ((135380351658772 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (523 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_523.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_523.trans
      change ((135270901456631 / 281474976710656 : ℚ) : ℝ) ≤ ((135270901456631 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (524 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_524.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_524.trans
      change ((8447588269015 / 17592186044416 : ℚ) : ℝ) ≤ ((135161412304240 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (525 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_525.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_525.trans
      change ((135051884180803 / 281474976710656 : ℚ) : ℝ) ≤ ((135051884180803 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (526 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_526.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_526.trans
      change ((67471158532755 / 140737488355328 : ℚ) : ℝ) ≤ ((134942317065510 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (527 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_527.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_527.trans
      change ((2106761108399 / 4398046511104 : ℚ) : ℝ) ≤ ((134832710937536 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (528 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_528.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_528.trans
      change ((134723065776041 / 281474976710656 : ℚ) : ℝ) ≤ ((134723065776041 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (529 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_529.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_529.trans
      change ((134613381560169 / 281474976710656 : ℚ) : ℝ) ≤ ((134613381560169 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (530 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_530.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_530.trans
      change ((33625914567263 / 70368744177664 : ℚ) : ℝ) ≤ ((134503658269052 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (531 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_531.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_531.trans
      change ((134393895881803 / 281474976710656 : ℚ) : ℝ) ≤ ((134393895881803 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (532 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_532.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_532.trans
      change ((33571023594381 / 70368744177664 : ℚ) : ℝ) ≤ ((134284094377524 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (533 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_533.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_533.trans
      change ((33543563433825 / 70368744177664 : ℚ) : ℝ) ≤ ((134174253735300 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (534 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_534.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_534.trans
      change ((67032186967101 / 140737488355328 : ℚ) : ℝ) ≤ ((134064373934202 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (535 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_535.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_535.trans
      change ((66977227476643 / 140737488355328 : ℚ) : ℝ) ≤ ((133954454953286 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (536 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_536.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_536.trans
      change ((16730562096449 / 35184372088832 : ℚ) : ℝ) ≤ ((133844496771592 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (537 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_537.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_537.trans
      change ((133734499368145 / 281474976710656 : ℚ) : ℝ) ≤ ((133734499368145 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (538 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_538.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_538.trans
      change ((66812231360979 / 140737488355328 : ℚ) : ℝ) ≤ ((133624462721958 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (539 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_539.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_539.trans
      change ((133514386812025 / 281474976710656 : ℚ) : ℝ) ≤ ((133514386812025 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (540 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_540.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_540.trans
      change ((8337766976083 / 17592186044416 : ℚ) : ℝ) ≤ ((133404271617328 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (541 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_541.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_541.trans
      change ((4165441159901 / 8796093022208 : ℚ) : ℝ) ≤ ((133294117116832 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (542 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_542.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_542.trans
      change ((133183923289489 / 281474976710656 : ℚ) : ℝ) ≤ ((133183923289489 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (543 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_543.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_543.trans
      change ((133073690114233 / 281474976710656 : ℚ) : ℝ) ≤ ((133073690114233 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (544 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_544.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_544.trans
      change ((132963417569987 / 281474976710656 : ℚ) : ℝ) ≤ ((132963417569987 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (545 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_545.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_545.trans
      change ((132853105635655 / 281474976710656 : ℚ) : ℝ) ≤ ((132853105635655 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (546 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_546.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_546.trans
      change ((8296422143133 / 17592186044416 : ℚ) : ℝ) ≤ ((132742754290128 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (547 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_547.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_547.trans
      change ((66316181756141 / 140737488355328 : ℚ) : ℝ) ≤ ((132632363512282 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (548 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_548.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_548.trans
      change ((8282620830061 / 17592186044416 : ℚ) : ℝ) ≤ ((132521933280976 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (549 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_549.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_549.trans
      change ((66205731787529 / 140737488355328 : ℚ) : ℝ) ≤ ((132411463575058 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (550 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_550.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_550.trans
      change ((33075238593339 / 70368744177664 : ℚ) : ℝ) ≤ ((132300954373356 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (551 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_551.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_551.trans
      change ((66095202827343 / 140737488355328 : ℚ) : ℝ) ≤ ((132190405654686 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (552 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_552.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_552.trans
      change ((16509977174731 / 35184372088832 : ℚ) : ℝ) ≤ ((132079817397848 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (553 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_553.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_553.trans
      change ((65984594790813 / 140737488355328 : ℚ) : ℝ) ≤ ((131969189581626 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (554 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_554.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_554.trans
      change ((65929261092395 / 140737488355328 : ℚ) : ℝ) ≤ ((131858522184790 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (555 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_555.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_555.trans
      change ((65873907593047 / 140737488355328 : ℚ) : ℝ) ≤ ((131747815186094 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (556 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_556.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_556.trans
      change ((65818534282139 / 140737488355328 : ℚ) : ℝ) ≤ ((131637068564278 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (557 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_557.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_557.trans
      change ((131526282298065 / 281474976710656 : ℚ) : ℝ) ≤ ((131526282298065 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (558 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_558.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_558.trans
      change ((32853864091541 / 70368744177664 : ℚ) : ℝ) ≤ ((131415456366164 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (559 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_559.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_559.trans
      change ((131304590747269 / 281474976710656 : ℚ) : ℝ) ≤ ((131304590747269 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (560 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_560.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_560.trans
      change ((65596842710029 / 140737488355328 : ℚ) : ℝ) ≤ ((131193685420058 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (561 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_561.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_561.trans
      change ((131082740363193 / 281474976710656 : ℚ) : ℝ) ≤ ((131082740363193 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (562 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_562.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_562.trans
      change ((130971755555323 / 281474976710656 : ℚ) : ℝ) ≤ ((130971755555323 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (563 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_563.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_563.trans
      change ((130860730975079 / 281474976710656 : ℚ) : ℝ) ≤ ((130860730975079 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (564 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_564.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_564.trans
      change ((130749666601079 / 281474976710656 : ℚ) : ℝ) ≤ ((130749666601079 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (565 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_565.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_565.trans
      change ((130638562411925 / 281474976710656 : ℚ) : ℝ) ≤ ((130638562411925 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (566 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_566.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_566.trans
      change ((65263709193101 / 140737488355328 : ℚ) : ℝ) ≤ ((130527418386202 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (567 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_567.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_567.trans
      change ((130416234502481 / 281474976710656 : ℚ) : ℝ) ≤ ((130416234502481 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (568 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_568.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_568.trans
      change ((130305010739319 / 281474976710656 : ℚ) : ℝ) ≤ ((130305010739319 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (569 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_569.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_569.trans
      change ((130193747075255 / 281474976710656 : ℚ) : ℝ) ≤ ((130193747075255 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (570 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_570.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_570.trans
      change ((130082443488815 / 281474976710656 : ℚ) : ℝ) ≤ ((130082443488815 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (571 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_571.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_571.trans
      change ((129971099958507 / 281474976710656 : ℚ) : ℝ) ≤ ((129971099958507 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (572 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_572.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_572.trans
      change ((129859716462825 / 281474976710656 : ℚ) : ℝ) ≤ ((129859716462825 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (573 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_573.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_573.trans
      change ((129748292980249 / 281474976710656 : ℚ) : ℝ) ≤ ((129748292980249 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (574 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_574.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_574.trans
      change ((129636829489241 / 281474976710656 : ℚ) : ℝ) ≤ ((129636829489241 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (575 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_575.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_575.trans
      change ((129525325968249 / 281474976710656 : ℚ) : ℝ) ≤ ((129525325968249 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (576 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_576.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_576.trans
      change ((16176722799463 / 35184372088832 : ℚ) : ℝ) ≤ ((129413782395704 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (577 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_577.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_577.trans
      change ((129302198750025 / 281474976710656 : ℚ) : ℝ) ≤ ((129302198750025 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (578 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_578.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_578.trans
      change ((64595287504805 / 140737488355328 : ℚ) : ℝ) ≤ ((129190575009610 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (579 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_579.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_579.trans
      change ((8067431947053 / 17592186044416 : ℚ) : ℝ) ≤ ((129078911152848 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (580 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_580.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_580.trans
      change ((64483603579053 / 140737488355328 : ℚ) : ℝ) ≤ ((128967207158106 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (581 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_581.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_581.trans
      change ((32213865750935 / 70368744177664 : ℚ) : ℝ) ≤ ((128855463003740 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (582 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_582.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_582.trans
      change ((128743678668089 / 281474976710656 : ℚ) : ℝ) ≤ ((128743678668089 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (583 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_583.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_583.trans
      change ((32157963532369 / 70368744177664 : ℚ) : ℝ) ≤ ((128631854129476 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (584 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_584.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_584.trans
      change ((128519989366209 / 281474976710656 : ℚ) : ℝ) ≤ ((128519989366209 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (585 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_585.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_585.trans
      change ((32102021089145 / 70368744177664 : ℚ) : ℝ) ≤ ((128408084356580 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (586 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_586.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_586.trans
      change ((128296139078865 / 281474976710656 : ℚ) : ℝ) ≤ ((128296139078865 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (587 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_587.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_587.trans
      change ((64092076755663 / 140737488355328 : ℚ) : ℝ) ≤ ((128184153511326 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (588 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_588.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_588.trans
      change ((128072127632207 / 281474976710656 : ℚ) : ℝ) ≤ ((128072127632207 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (589 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_589.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_589.trans
      change ((63980030709869 / 140737488355328 : ℚ) : ℝ) ≤ ((127960061419738 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (590 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_590.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_590.trans
      change ((63923977426067 / 140737488355328 : ℚ) : ℝ) ≤ ((127847954852134 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (591 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_591.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_591.trans
      change ((15966975988449 / 35184372088832 : ℚ) : ℝ) ≤ ((127735807907592 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (592 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_592.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_592.trans
      change ((63811810282147 / 140737488355328 : ℚ) : ℝ) ≤ ((127623620564294 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (593 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_593.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_593.trans
      change ((15938924100051 / 35184372088832 : ℚ) : ℝ) ≤ ((127511392800408 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (594 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_594.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_594.trans
      change ((127399124594085 / 281474976710656 : ℚ) : ℝ) ≤ ((127399124594085 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (595 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_595.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_595.trans
      change ((127286815923459 / 281474976710656 : ℚ) : ℝ) ≤ ((127286815923459 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (596 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_596.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_596.trans
      change ((127174466766651 / 281474976710656 : ℚ) : ℝ) ≤ ((127174466766651 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (597 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_597.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_597.trans
      change ((31765519275441 / 70368744177664 : ℚ) : ℝ) ≤ ((127062077101764 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (598 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_598.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_598.trans
      change ((63474823453443 / 140737488355328 : ℚ) : ℝ) ≤ ((126949646906886 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (599 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_599.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_599.trans
      change ((126837176160089 / 281474976710656 : ℚ) : ℝ) ≤ ((126837176160089 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (600 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_600.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_600.trans
      change ((63362332419715 / 140737488355328 : ℚ) : ℝ) ≤ ((126724664839430 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (601 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_601.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_601.trans
      change ((126612112922949 / 281474976710656 : ℚ) : ℝ) ≤ ((126612112922949 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (602 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_602.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_602.trans
      change ((63249760194335 / 140737488355328 : ℚ) : ℝ) ≤ ((126499520388670 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (603 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_603.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_603.trans
      change ((126386887214603 / 281474976710656 : ℚ) : ℝ) ≤ ((126386887214603 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (604 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_604.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_604.trans
      change ((31568553344685 / 70368744177664 : ℚ) : ℝ) ≤ ((126274213378740 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (605 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_605.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_605.trans
      change ((63080749429529 / 140737488355328 : ℚ) : ℝ) ≤ ((126161498859058 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (606 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_606.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_606.trans
      change ((126048743633519 / 281474976710656 : ℚ) : ℝ) ≤ ((126048743633519 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (607 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_607.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_607.trans
      change ((31483986920017 / 70368744177664 : ℚ) : ℝ) ≤ ((125935947680068 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (608 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_608.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_608.trans
      change ((125823110976633 / 281474976710656 : ℚ) : ℝ) ≤ ((125823110976633 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (609 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_609.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_609.trans
      change ((15713779187641 / 35184372088832 : ℚ) : ℝ) ≤ ((125710233501128 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (610 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_610.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_610.trans
      change ((125597315231451 / 281474976710656 : ℚ) : ℝ) ≤ ((125597315231451 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (611 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_611.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_611.trans
      change ((62742178072741 / 140737488355328 : ℚ) : ℝ) ≤ ((125484356145482 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (612 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_612.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_612.trans
      change ((3917854881909 / 8796093022208 : ℚ) : ℝ) ≤ ((125371356221088 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (613 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_613.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_613.trans
      change ((125258315436117 / 281474976710656 : ℚ) : ℝ) ≤ ((125258315436117 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (614 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_614.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_614.trans
      change ((125145233768403 / 281474976710656 : ℚ) : ℝ) ≤ ((125145233768403 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (615 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_615.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_615.trans
      change ((125032111195763 / 281474976710656 : ℚ) : ℝ) ≤ ((125032111195763 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (616 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_616.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_616.trans
      change ((62459473847999 / 140737488355328 : ℚ) : ℝ) ≤ ((124918947695998 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (617 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_617.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_617.trans
      change ((62402871623447 / 140737488355328 : ℚ) : ℝ) ≤ ((124805743246894 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (618 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_618.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_618.trans
      change ((124692497826219 / 281474976710656 : ℚ) : ℝ) ≤ ((124692497826219 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (619 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_619.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_619.trans
      change ((124579211411727 / 281474976710656 : ℚ) : ℝ) ≤ ((124579211411727 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (620 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_620.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_620.trans
      change ((124465883981155 / 281474976710656 : ℚ) : ℝ) ≤ ((124465883981155 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (621 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_621.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_621.trans
      change ((62176257756111 / 140737488355328 : ℚ) : ℝ) ≤ ((124352515512222 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (622 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_622.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_622.trans
      change ((124239105982635 / 281474976710656 : ℚ) : ℝ) ≤ ((124239105982635 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (623 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_623.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_623.trans
      change ((3878926730315 / 8796093022208 : ℚ) : ℝ) ≤ ((124125655370080 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (624 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_624.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_624.trans
      change ((15501520456529 / 35184372088832 : ℚ) : ℝ) ≤ ((124012163652232 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (625 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_625.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_625.trans
      change ((123898630806745 / 281474976710656 : ℚ) : ℝ) ≤ ((123898630806745 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (626 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_626.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_626.trans
      change ((123785056811259 / 281474976710656 : ℚ) : ℝ) ≤ ((123785056811259 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (627 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_627.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_627.trans
      change ((123671441643399 / 281474976710656 : ℚ) : ℝ) ≤ ((123671441643399 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (628 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_628.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_628.trans
      change ((30889446320193 / 70368744177664 : ℚ) : ℝ) ≤ ((123557785280772 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (629 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_629.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_629.trans
      change ((123444087700969 / 281474976710656 : ℚ) : ℝ) ≤ ((123444087700969 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (630 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_630.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_630.trans
      change ((123330348881565 / 281474976710656 : ℚ) : ℝ) ≤ ((123330348881565 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (631 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_631.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_631.trans
      change ((61608284400059 / 140737488355328 : ℚ) : ℝ) ≤ ((123216568800118 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (632 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_632.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_632.trans
      change ((30775686858543 / 70368744177664 : ℚ) : ℝ) ≤ ((123102747434172 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (633 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_633.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_633.trans
      change ((30747221190313 / 70368744177664 : ℚ) : ℝ) ≤ ((122988884761252 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (634 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_634.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_634.trans
      change ((122874980758869 / 281474976710656 : ℚ) : ℝ) ≤ ((122874980758869 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (635 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_635.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_635.trans
      change ((122761035404515 / 281474976710656 : ℚ) : ℝ) ≤ ((122761035404515 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (636 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_636.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_636.trans
      change ((30661762168917 / 70368744177664 : ℚ) : ℝ) ≤ ((122647048675668 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (637 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_637.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_637.trans
      change ((30633255137447 / 70368744177664 : ℚ) : ℝ) ≤ ((122533020549788 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (638 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_638.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_638.trans
      change ((3825592218885 / 8796093022208 : ℚ) : ℝ) ≤ ((122418951004320 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (639 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_639.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_639.trans
      change ((30576210004173 / 70368744177664 : ℚ) : ℝ) ≤ ((122304840016692 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Sigma004
